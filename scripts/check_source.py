#!/usr/bin/env python3
"""Fail if committed Lean source contains something that weakens or bypasses a proof.

`Test/AxiomAudit.lean` is the real check on what proofs depend on. This one is fast, runs before
any build, names the line, and also catches what leaves no axiom behind (search tactics left in a
proof, `implemented_by`). Comments and strings are removed first, so prose may mention the words.

Usage: python3 scripts/check_source.py [ROOT ...]   (default: ExtremeValueTheory Test)
"""

import re
import sys
from pathlib import Path

FORBIDDEN = [
    (r"(?<![\w.'])sorry(?![\w'])", "`sorry`: an unfinished proof"),
    (r"(?<![\w.'])admit(?![\w'])", "`admit`: an unfinished proof"),
    (r"(?<![\w.'])stop(?![\w'])", "`stop`: skips the rest of a proof"),
    (r"(?<![\w.'])sorryAx(?![\w'])", "`sorryAx`: an unfinished proof"),
    (r"(?<![\w.'])native_decide(?![\w'])", "`native_decide`: trusts the compiler"),
    (r"(?<![\w.'])ofReduceBool(?![\w'])", "`ofReduceBool`: trusts the compiler"),
    (r"^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+)?axiom\s", "`axiom`: a new assumption"),
    (r"(?<![\w.'])implemented_by(?![\w'])", "`implemented_by`: replaces a definition's code"),
    (r"(?<![\w.'])unsafe\s", "`unsafe`: outside the logic"),
    (r"(?<![\w.'])(?:exact|apply|rw|simp|simp_all|aesop|have|show)\?", "a search tactic left in the source"),
    (r"^\s*(?:·\s*)?hint\s*$", "a search tactic left in the source"),
    (r"(?<![\w.'])says(?![\w'])", "a search tactic left in the source"),
]
PATTERNS = [(re.compile(p, re.MULTILINE), why) for p, why in FORBIDDEN]


def strip_comments_and_strings(text: str) -> str:
    """Blank out comments (nested `/- -/`, and `--`) and strings, keeping line numbers."""
    out = []
    i, n, depth = 0, len(text), 0
    in_string = False
    while i < n:
        c, two = text[i], text[i : i + 2]
        if depth:
            if two == "/-":
                depth, i = depth + 1, i + 2
            elif two == "-/":
                depth, i = depth - 1, i + 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif in_string:
            if c == "\\":
                i += 2
            else:
                in_string = c != '"'
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif two == "/-":
            depth, i = 1, i + 2
        elif two == "--":
            while i < n and text[i] != "\n":
                i += 1
        elif c == '"' and text[i - 1 : i] != "'":
            in_string = True
            i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def check(path: Path) -> list[str]:
    code = strip_comments_and_strings(path.read_text(encoding="utf-8"))
    return [
        f"{path}:{code.count(chr(10), 0, m.start()) + 1}: {why}"
        for pattern, why in PATTERNS
        for m in pattern.finditer(code)
    ]


def main() -> int:
    roots = [Path(a) for a in sys.argv[1:]] or [Path("ExtremeValueTheory"), Path("Test")]
    files = [f for root in roots for f in ([root] if root.is_file() else sorted(root.rglob("*.lean")))]
    if not files:
        print("check_source: no Lean files found", file=sys.stderr)
        return 2
    problems = [p for f in files for p in check(f)]
    for p in problems:
        print(p)
    print(f"check_source: {len(files)} files, {len(problems)} problems")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
