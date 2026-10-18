#!/usr/bin/env python3
"""Mutation checks for theorem statements.

For each named theorem, generate small perturbations ("mutants") of its *statement* only (binders,
hypotheses and conclusion), keep the original proof, and check whether the file still compiles. A
mutant that still compiles "survives": the perturbed part of the statement is irrelevant to the
proof, which is either harmless (an equivalent statement) or a sign that the theorem is proved for
a trivial reason. See Test/MUTATION.md.

The real source tree is never modified. Each check runs on a scratch copy of the module, truncated
right after the theorem, inside a temporary directory that is removed at the end. To save time the
proofs of earlier theorems/lemmas in the scratch copy are replaced by `sorry` (later code only sees
their statements); if that "fast prefix" does not compile, the full prefix is used instead.

Usage (from the repository root, after `lake build`):

    python3 scripts/mutation_check.py                  # default list: headline + research theorems
    python3 scripts/mutation_check.py isInMDAFrechet_iff tendstoInMeasure_hill
    python3 scripts/mutation_check.py --list           # only show the mutants that would be run
    python3 scripts/mutation_check.py --jobs 4 --max-mutants 6 --json out.json

Outcomes per mutant:
  killed    the proof no longer checks against the mutated statement (good)
  invalid   the mutated statement itself does not elaborate (uninformative, counted as killed)
  survived  the original proof still proves the mutated statement (inspect by hand)
  timeout   the check exceeded the time limit (inconclusive)
  error     the check could not run (OS resource error after retries; inconclusive)
"""

from __future__ import annotations

import argparse
import concurrent.futures as cf
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "ExtremeValueTheory"
LAKE = os.environ.get("LAKE", str(Path.home() / ".elan" / "bin" / "lake"))

# Lean names from the README "Headline theorems" table and "Research results" list, plus the main
# research results named in RESEARCH.md.
DEFAULT_THEOREMS = [
    # Headline theorems
    "CumulativeDistributionFunction.IsExtremeValueDistr.classification",
    "isMaxStable_iff_isExtremeValueDistr",
    "isInMDAFrechet_iff",
    "isInMDAWeibull_iff",
    "isInMDAGumbel_iff",
    "isInMDAGEV_iff_exists_isExtendedRegularlyVarying_tailQuantile",
    "isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival",
    "IsRegularlyVarying.tendsto_integral_Ioi_div",
    "tendsto_measure_mul_div_measure",
    "tendsto_map_convPow_sub_of_isRegularlyVarying_of_one_lt'",
    "domainOfAttraction_isStableIndex_iff",
    "IsStable.existsUnique_isStableIndex",
    "domainOfAttraction_gaussianReal_iff",
    "IsSubexponential.tendsto_tail_compound_div",
    "tendsto_pkRuin_div_mul_tail",
    "tendstoInMeasure_hill",
    "tendstoInDistribution_hill",
    "tendstoInMeasure_hill_of_alphaMixing_rate",
    "tendstoInMeasure_pickands",
    "tendstoInMeasure_momentEstimator_of_isInMDAGEV'",
    "tendstoInDistribution_weissman",
    "ae_tendsto_gpdMLE'",
    "exists_gpdMLE_tendstoInDistribution",
    "ae_tendsto_gevMLE",
    "tendsto_measureReal_partialMax_le_exp",
    "HasSpectralTailProcess.lintegral_timeChange",
    "HasSpectralTailProcess.hasExtremalIndex_abs",
    "isRegVarVector_iff",
    "CramerWold.isRegVarVector_of_tendsto_linear",
    "isMDAWith_iff",
    "IsMDAWith.tendsto_conditionalExcessCDF",
    "IsSimpleMaxStable.existsUnique_hasSpectralMeasure",
    "ProbabilityTheory.exists_isPoissonRandomMeasure",
    "tendsto_measureReal_sumDiracRange_timeSpace_eq",
    "tendstoInDistribution_tailEmpiricalPath",
    # Research results
    "logEchoProcess_theta_lt_vartheta",
    "logEchoProcess_phase_transition",
    "powEchoProcess_antiClustering_iff",
    "logEchoProcess_betaMixing_incompatible",
    "HasSpectralTailProcess.lt_candidateExtremalIndex_iff",
    "HasSpectralTailProcess.le_candidateExtremalIndex'",
    "tendsto_blockRatio",
    "hasExtremalIndex_abs_of_alphaMixing",
    "powEchoProcess_critical",
]

MODIFIERS = r"(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*"
DECL_RE = re.compile(
    r"^(?:@\[[^\n]*?\]\s*)?" + MODIFIERS +
    r"(theorem|lemma|def|instance|abbrev|structure|class|inductive|example|opaque|axiom)\b\s*([^\s:({\[⦃]*)"
)
NS_RE = re.compile(r"^namespace\s+(\S+)")
SEC_RE = re.compile(r"^(?:noncomputable\s+)?section\b\s*(\S*)")
END_RE = re.compile(r"^end\b\s*(\S*)")
OPEN_BR = "([{⦃⟨"
CLOSE_BR = ")]}⦄⟩"


# --------------------------------------------------------------------------------------------
# Parsing


def comment_mask(text: str) -> list[bool]:
    """True at positions inside comments or string literals."""
    mask = [False] * len(text)
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                mask[k] = True
            i = j
        elif text.startswith("/-", i):
            depth += 1
            mask[i] = mask[i + 1] = True
            i += 2
        elif depth > 0 and text.startswith("-/", i):
            depth -= 1
            mask[i] = mask[i + 1] = True
            i += 2
        elif depth > 0:
            mask[i] = True
            i += 1
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            for k in range(i, min(j + 1, n)):
                mask[k] = True
            i = j + 1
        else:
            i += 1
    return mask


@dataclass
class Decl:
    kind: str
    name: str  # as written
    full: str  # with namespaces
    start: int  # char offset of the declaration line
    name_end: int  # char offset just after the name
    assign: int | None  # char offset of the top-level ':=' (None if absent)
    end: int  # char offset of the end of the declaration


def top_level_assign(text: str, mask: list[bool], i: int, end: int) -> int | None:
    depth = 0
    while i < end:
        if mask[i]:
            i += 1
            continue
        c = text[i]
        if c in OPEN_BR:
            depth += 1
        elif c in CLOSE_BR:
            depth -= 1
        elif depth == 0 and text.startswith(":=", i):
            return i
        elif depth == 0 and c == "|" and (i == 0 or text[i - 1] == "\n" or text[i - 2:i] == "  "):
            # pattern-matching definition: no single ':='
            line_start = text.rfind("\n", 0, i) + 1
            if text[line_start:i].strip() == "":
                return None
        i += 1
    return None


def parse_file(path: Path) -> tuple[str, list[bool], list[Decl]]:
    text = path.read_text(encoding="utf-8")
    mask = comment_mask(text)
    lines = text.split("\n")
    offsets, pos = [], 0
    for ln in lines:
        offsets.append(pos)
        pos += len(ln) + 1
    # column-0 lines that start a new top-level item (decl boundaries)
    boundary = []
    for idx, ln in enumerate(lines):
        o = offsets[idx]
        if ln and not ln[0].isspace() and ln[0] not in CLOSE_BR and not mask[o]:
            boundary.append(idx)
        elif ln.startswith("/--") or ln.startswith("/-"):
            boundary.append(idx)
    stack: list[tuple[str, str]] = []  # (kind, name)
    decls = []
    for bi, idx in enumerate(boundary):
        ln, o = lines[idx], offsets[idx]
        if mask[o]:
            continue
        if m := NS_RE.match(ln):
            for part in m.group(1).split("."):
                stack.append(("ns", part))
            continue
        if m := SEC_RE.match(ln):
            stack.append(("sec", m.group(1)))
            continue
        if m := END_RE.match(ln):
            name = m.group(1)
            if name:
                for _ in name.split("."):
                    if stack:
                        stack.pop()
            elif stack:
                stack.pop()
            continue
        m = DECL_RE.match(ln)
        if not m:
            continue
        kind, name = m.group(1), m.group(2)
        nxt = boundary[bi + 1] if bi + 1 < len(boundary) else len(lines)
        end = offsets[nxt] if nxt < len(lines) else len(text)
        name_end = o + m.end(2)
        ns = ".".join(n for k, n in stack if k == "ns")
        if name.startswith("_root_."):
            full = name[len("_root_."):]
        else:
            full = f"{ns}.{name}" if ns and name else name
        assign = top_level_assign(text, mask, name_end, end)
        decls.append(Decl(kind, name, full, o, name_end, assign, end))
    return text, mask, decls


def build_index() -> dict[str, list[tuple[Path, Decl]]]:
    index: dict[str, list[tuple[Path, Decl]]] = {}
    for path in sorted(SRC.rglob("*.lean")):
        _, _, decls = parse_file(path)
        for d in decls:
            if d.kind in ("theorem", "lemma") and d.full:
                index.setdefault(d.full, []).append((path, d))
    return index


def lookup(index, name: str):
    hits = []
    for full, entries in index.items():
        if full == name or full.endswith("." + name):
            hits.extend(entries)
    return hits


# --------------------------------------------------------------------------------------------
# Mutation operators. Each returns a list of (start, end, replacement) edits inside the statement.

IDENT = r"[\w.'₀-₉ᵢ]+"


def _subs(pattern, repl):
    rx = re.compile(pattern)

    def op(stmt, mask):
        out = []
        for m in rx.finditer(stmt):
            if any(mask[m.start():m.end()]):
                continue
            out.append((m.start(), m.end(), repl(m) if callable(repl) else m.expand(repl)))
        return out

    return op


def _atom_after(stmt: str, mask, i: int) -> int | None:
    """End of the atom (identifier, numeral or bracketed group) starting at i."""
    if i >= len(stmt):
        return None
    if stmt[i] in "(⟨":
        depth = 0
        for j in range(i, len(stmt)):
            if mask[j]:
                continue
            if stmt[j] in OPEN_BR:
                depth += 1
            elif stmt[j] in CLOSE_BR:
                depth -= 1
                if depth == 0:
                    return j + 1
        return None
    m = re.compile(IDENT).match(stmt, i)
    return m.end() if m else None


def op_nhds(stmt, mask):
    out = []
    for m in re.finditer(r"(?:𝓝|nhds)\s+", stmt):
        if any(mask[m.start():m.end()]):
            continue
        j = _atom_after(stmt, mask, m.end())
        if j is None:
            continue
        atom = stmt[m.end():j]
        out.append((m.end(), j, f"({atom} + 1)"))
    return out


def op_unary_neg(stmt, mask):
    out = []
    for m in re.finditer(r"-(?=[\w(])", stmt):
        i = m.start()
        if mask[i] or (i > 0 and stmt[i - 1] in "-<"):
            continue
        k = i - 1
        while k >= 0 and stmt[k] == " ":
            k -= 1
        # unary if preceded by an opening bracket, an operator, or start
        if k < 0 or stmt[k] in "([{⟨,=<>≤≥≠+*/^∣:↑" or (stmt[k] == " ") or stmt[k:k + 1] in ("→", "↔", "∧", "∨"):
            out.append((i, i + 1, ""))
    return out


def op_drop_hyp(stmt, mask):
    """Replace an explicit hypothesis `(h... : P)`, not referenced elsewhere, by `(h... : True)`."""
    out = []
    concl = conclusion_start(stmt, mask)
    depth, i = 0, 0
    while i < concl:
        c = stmt[i]
        if mask[i]:
            i += 1
            continue
        if c == "(" and depth == 0:
            j = _atom_after(stmt, mask, i)
            if j is None:
                break
            m = re.match(r"\((h\S*)\s*:", stmt[i:j])
            if m:
                name = m.group(1)
                rest = stmt[:i] + stmt[j:]
                if not re.search(r"(?<![\w.'])" + re.escape(name) + r"(?![\w'₀-₉])", rest):
                    out.append((i, j, f"({name} : True)"))
            i = j
            continue
        if c in OPEN_BR:
            depth += 1
        elif c in CLOSE_BR:
            depth -= 1
        i += 1
    return list(reversed(out))


# `0 < t` where `t` is an application of identifiers, up to a delimiter
SIGN = r"(?<![\w.₀-₉])0 {} ((?:[\w.'₀-₉ᵢ]+)(?: [\w.'₀-₉ᵢ]+)*)(?=\s*(?:[)∧∨→↔,]|$))"


def _flip(rel):
    return lambda m: (f"({m.group(1)})" if " " in m.group(1) else m.group(1)) + f" {rel} 0"


NUM = r"(?<![\w.₀-₉'≥])(?<!Fin )({})(?![\w.₀-₉∞])"

OPERATORS = [
    # (key, description, op), in priority order
    ("nhds", "𝓝 c -> 𝓝 (c + 1)", op_nhds),
    ("atTop", "atTop -> atBot", _subs(r"\batTop\b", "atBot")),
    ("pos", "0 < x -> x < 0", _subs(SIGN.format("<"), _flip("<"))),
    ("hyp", "hypothesis -> True", op_drop_hyp),
    ("lt", "< -> ≤", _subs(r"(?<![<|\-=])<(?![=|;$>\-])", "≤")),
    ("le", "≤ -> <", _subs(r"≤", "<")),
    ("lit1", "1 -> 2", _subs(NUM.format("1"), "2")),
    ("lit2", "2 -> 3", _subs(NUM.format("2"), "3")),
    ("neg", "drop unary -", op_unary_neg),
    ("and", "∧ -> ∨", _subs(r"∧", "∨")),
    ("or", "∨ -> ∧", _subs(r"∨", "∧")),
    ("Ioi", "Ioi -> Ici", _subs(r"\bIoi\b", "Ici")),
    ("Iio", "Iio -> Iic", _subs(r"\bIio\b", "Iic")),
    ("nonneg", "0 ≤ x -> x ≤ 0", _subs(SIGN.format("≤"), _flip("≤"))),
    ("eq", "= -> ≠", _subs(r"(?<![:<>≤≥=!])=(?![=>])", "≠")),
    ("atBot", "atBot -> atTop", _subs(r"\batBot\b", "atTop")),
    ("lit0", "0 -> 1", _subs(NUM.format("0"), "1")),
]


def conclusion_start(stmt: str, mask) -> int:
    """Offset of the first top-level ':' (start of the conclusion; binders are bracketed)."""
    depth = 0
    for i, c in enumerate(stmt):
        if mask[i]:
            continue
        if c in OPEN_BR:
            depth += 1
        elif c in CLOSE_BR:
            depth -= 1
        elif depth == 0 and c == ":" and not stmt.startswith(":=", i):
            return i
    return 0


def mutants_for(stmt: str, cap: int):
    mask = comment_mask(stmt)
    concl = conclusion_start(stmt, mask)
    per_op = []
    for key, desc, op in OPERATORS:
        edits = op(stmt, mask)
        # conclusion occurrences first, then hypotheses from the last one backwards
        edits = [e for e in edits if e[0] >= concl] + [e for e in reversed(edits) if e[0] < concl]
        if edits:
            per_op.append((key, desc, edits))
    chosen, seen, used = [], set(), []
    ptr = [0] * len(per_op)
    while len(chosen) < cap and any(ptr[k] < len(e) for k, (_, _, e) in enumerate(per_op)):
        for k, (key, desc, edits) in enumerate(per_op):
            if len(chosen) >= cap or ptr[k] >= len(edits):
                continue
            # prefer an occurrence that does not overlap an already mutated span
            pick = next((q for q in range(ptr[k], len(edits))
                         if all(edits[q][1] <= a or edits[q][0] >= b for a, b in used)), ptr[k])
            edits.insert(ptr[k], edits.pop(pick))
            s, e, r = edits[ptr[k]]
            ptr[k] += 1
            new = stmt[:s] + r + stmt[e:]
            if new in seen:
                continue
            seen.add(new)
            used.append((s, max(e, s + 1)))
            where = "conclusion" if s >= concl else "hypotheses"
            line = stmt.count("\n", 0, s)
            ctx = stmt[max(0, s - 25):e + 25].replace("\n", " ")
            chosen.append(dict(op=key, desc=desc, where=where, offset=s, stmt_line=line,
                               context=" ".join(ctx.split()), statement=new))
    return chosen


# --------------------------------------------------------------------------------------------
# Scratch files and compilation


def scratch_source(text, mask, decls, target: Decl, statement: str | None, fast: bool):
    """The file truncated after `target`, with `statement` substituted, prior proofs sorried.

    Returns the source and the (line, column) span of the statement in it, lines 1-based,
    columns 0-based (as in Lean's messages); the span ends at the top-level `:=`."""
    parts, cur = [], 0
    if fast:
        for d in decls:
            if d.start >= target.start:
                break
            if d.kind in ("theorem", "lemma", "example") and d.assign is not None:
                parts.append(text[cur:d.assign])
                parts.append(":= sorry\n\n")
                cur = d.end
    parts.append(text[cur:target.name_end])
    first = "".join(parts).count("\n") + 1
    stmt = text[target.name_end:target.assign] if statement is None else statement
    parts.append(stmt)
    before = "".join(parts)
    assign = (before.count("\n") + 1, len(before) - (before.rfind("\n") + 1))
    parts.append(text[target.assign:target.end])
    return "".join(parts), ((first, 0), assign)


def run_lean(path: Path, timeout: float, attempts: int = 5):
    """Check one file. Transient OS errors (e.g. a full system file table) are retried."""
    for attempt in range(attempts):
        t0 = time.time()
        try:
            p = subprocess.run([LAKE, "env", "lean", str(path)], cwd=ROOT, capture_output=True,
                               text=True, timeout=timeout)
            if "Too many open files" in p.stdout + p.stderr:  # resource exhaustion, not a verdict
                raise OSError("Too many open files (reported by lean)")
            break
        except subprocess.TimeoutExpired:
            return "timeout", time.time() - t0, ""
        except OSError as e:
            if attempt == attempts - 1:
                return "oserror", time.time() - t0, str(e)
            time.sleep(30 * (attempt + 1))
    out = p.stdout + p.stderr
    ok = p.returncode == 0 and ": error" not in out
    return ("ok" if ok else "error"), time.time() - t0, out


def write_retry(path: Path, text: str, attempts: int = 5):
    for attempt in range(attempts):
        try:
            path.write_text(text, encoding="utf-8")
            return
        except OSError:
            if attempt == attempts - 1:
                raise
            time.sleep(30 * (attempt + 1))


def first_error(out: str, path: Path) -> tuple[tuple[int, int] | None, str]:
    """Position (line, column) and first message line of the first error reported in `path`."""
    m = re.search(re.escape(str(path)) + r":(\d+):(\d+): error:?\s*(.*)", out)
    return ((int(m.group(1)), int(m.group(2))), m.group(3).strip()[:200]) if m else (None, "")


@dataclass
class Job:
    name: str
    path: Path
    decl: Decl
    text: str
    mask: list
    decls: list
    mutants: list = field(default_factory=list)
    mode: str = "fast"
    baseline: float = 0.0
    status: str = "pending"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("names", nargs="*", help="theorem names (default: headline + research list)")
    ap.add_argument("--max-mutants", type=int, default=8)
    ap.add_argument("--jobs", type=int, default=4, help="concurrent lean processes (default 4)")
    ap.add_argument("--skip-after", type=float, default=600,
                    help="skip a theorem whose unmutated check takes longer (seconds, default 600)")
    ap.add_argument("--list", action="store_true", help="only list the mutants")
    ap.add_argument("--json", help="write results as JSON to this file")
    ap.add_argument("--keep", action="store_true", help="keep the scratch directory")
    args = ap.parse_args()
    names = args.names or DEFAULT_THEOREMS

    index = build_index()
    parsed: dict[Path, tuple] = {}
    jobs: list[Job] = []
    for name in names:
        hits = lookup(index, name)
        if not hits:
            print(f"!! {name}: not found", file=sys.stderr)
            continue
        for path, d in hits:
            if d.assign is None:
                print(f"!! {name}: no top-level ':=' in {path}", file=sys.stderr)
                continue
            if path not in parsed:
                parsed[path] = parse_file(path)
            text, mask, decls = parsed[path]
            d = next(x for x in decls if x.start == d.start)
            stmt = text[d.name_end:d.assign]
            job = Job(d.full, path, d, text, mask, decls, mutants_for(stmt, args.max_mutants))
            jobs.append(job)

    if args.list:
        for j in jobs:
            print(f"{j.name}  ({j.path.relative_to(ROOT)})")
            for m in j.mutants:
                print(f"    [{m['op']}] {m['where']}: {m['context']}")
        return

    tmp = Path(tempfile.mkdtemp(prefix="evt-mutation-"))
    results = []
    try:
        def baseline(ji: int, j: Job):
            for mode in ("fast", "full"):
                f = tmp / f"b{ji}_{mode}.lean"
                write_retry(f, scratch_source(j.text, j.mask, j.decls, j.decl, None, mode == "fast")[0])
                st, dt, out = run_lean(f, args.skip_after)
                if st == "ok":
                    j.mode, j.baseline, j.status = mode, dt, "ok"
                    return
                if st == "oserror":
                    j.status = f"skipped: {out}"
                    return
                if st == "timeout":
                    j.status = f"skipped: unmutated check exceeded {args.skip_after:.0f}s ({mode} prefix)"
                    return
            j.status = "skipped: unmutated scratch copy does not compile:\n" + out[-2000:]

        with cf.ThreadPoolExecutor(args.jobs) as ex:
            list(ex.map(lambda a: baseline(*a), enumerate(jobs)))
        for j in jobs:
            print(f"baseline {j.name}: {j.status if j.status != 'ok' else f'{j.baseline:.0f}s ({j.mode})'}",
                  flush=True)

        def check(ji: int, mi: int):
            j = jobs[ji]
            m = j.mutants[mi]
            f = tmp / f"m{ji}_{mi}.lean"
            src, (s_pos, e_pos) = scratch_source(j.text, j.mask, j.decls, j.decl, m["statement"],
                                                   j.mode == "fast")
            write_retry(f, src)
            st, dt, out = run_lean(f, max(300.0, 3 * j.baseline + 60))
            if st == "ok":
                res = "survived"
            elif st == "timeout":
                res = "timeout"
            elif st == "oserror":
                res, m["error"] = "error", out
            else:
                # error inside the statement => the mutant does not even elaborate
                pos, m["error"] = first_error(out, f)
                res = "invalid" if pos is not None and s_pos <= pos < e_pos else "killed"
            m["result"], m["seconds"] = res, round(dt)
            print(f"  {res:8s} {j.name} [{m['op']}] {m['where']}: {m['context']}"
                  + (f"\n           -> {m['error']}" if m.get("error") else ""), flush=True)

        todo = [(ji, mi) for ji, j in enumerate(jobs) if j.status == "ok" for mi in range(len(j.mutants))]
        with cf.ThreadPoolExecutor(args.jobs) as ex:
            list(ex.map(lambda a: check(*a), todo))

        for j in jobs:
            results.append(dict(name=j.name, file=str(j.path.relative_to(ROOT)), status=j.status,
                                baseline_seconds=round(j.baseline), prefix=j.mode,
                                mutants=[{k: v for k, v in m.items() if k != "statement"}
                                         for m in j.mutants]))
    finally:
        if args.keep:
            print(f"scratch directory kept: {tmp}")
        else:
            shutil.rmtree(tmp, ignore_errors=True)

    counts: dict[str, int] = {}
    for r in results:
        for m in r["mutants"]:
            if "result" in m:
                counts[m["result"]] = counts.get(m["result"], 0) + 1
    print("\nSummary:", ", ".join(f"{k} {v}" for k, v in sorted(counts.items())))
    skipped = [r for r in results if r["status"] != "ok"]
    for r in skipped:
        print(f"  skipped {r['name']}: {r['status'].splitlines()[0]}")
    print("\nSurvivors:")
    for r in results:
        for m in r["mutants"]:
            if m.get("result") == "survived":
                print(f"  {r['name']} ({r['file']}) [{m['desc']}] in {m['where']}: {m['context']}")
    if args.json:
        Path(args.json).write_text(json.dumps(results, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
