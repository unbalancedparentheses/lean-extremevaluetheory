#!/usr/bin/env python3
"""Cross-check Lean executable reference estimators (`Executable/Estimators.lean`)
against Python (`scipy.stats`) and R (`evd`, `exdex`).

Usage:
    python3 scripts/crosscheck_estimators.py [--exe PATH]

Expects `scipy` (Python) and `Rscript` with packages `evd` and `exdex` on PATH
(e.g., via `nix shell nixpkgs#python3Packages.scipy nixpkgs#R nixpkgs#rPackages.evd nixpkgs#rPackages.exdex`).
Exits 0 if all cross-checks pass within tolerance, 1 otherwise.
"""

from __future__ import annotations

import argparse
import json
import math
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

import numpy as np
from scipy import stats


REPO = Path(__file__).resolve().parent.parent
DEFAULT_EXE = REPO / ".lake" / "build" / "bin" / "evt_estimators"


def run_lean(exe: Path, cmd: list[str], data: np.ndarray | None = None) -> list[float]:
    if data is not None:
        args = [str(exe), *cmd, "--stdin"]
        stdin_str = "\n".join(f"{x:.17g}" for x in data)
        proc = subprocess.run(args, input=stdin_str, capture_output=True, text=True, check=True)
    else:
        args = [str(exe), *cmd]
        proc = subprocess.run(args, capture_output=True, text=True, check=True)
    return [float(tok) for tok in proc.stdout.strip().split()]


def run_r(script: str) -> dict:
    rscript = shutil.which("Rscript")
    if rscript is None:
        raise RuntimeError("Rscript not found on PATH")
    with tempfile.NamedTemporaryFile("w", suffix=".R", delete=True, encoding="utf-8") as f:
        f.write(script)
        f.flush()
        proc = subprocess.run([rscript, f.name], capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError(f"Rscript failed:\nSTDOUT:\n{proc.stdout}\nSTDERR:\n{proc.stderr}")
    lines = [ln.strip() for ln in proc.stdout.strip().splitlines() if ln.strip()]
    return json.loads(lines[-1])


class Checker:
    def __init__(self) -> None:
        self.results: list[tuple[str, float, float, float, bool, str]] = []

    def check(self, name: str, lean_val: float, ref_val: float, tol: float, note: str = "") -> None:
        err = abs(lean_val - ref_val)
        ok = math.isfinite(err) and err <= tol
        self.results.append((name, lean_val, ref_val, err, ok, note))

    def summary(self) -> int:
        print(f"{'Check':<46} {'Lean':>14} {'Reference':>14} {'|Diff|':>11}  Status")
        print("-" * 98)
        failures = 0
        for name, lv, rv, err, ok, note in self.results:
            status = "PASS" if ok else "FAIL"
            if not ok:
                failures += 1
            extra = f"  ({note})" if note else ""
            print(f"{name:<46} {lv:14.8f} {rv:14.8f} {err:11.3e}  {status}{extra}")
        print("-" * 98)
        print(f"Total: {len(self.results)} checks, {len(self.results) - failures} passed, {failures} failed")
        return 1 if failures else 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--exe", type=Path, default=DEFAULT_EXE)
    parser.add_argument("--skip-r", action="store_true", help="Skip R cross-checks (Python/scipy only)")
    args = parser.parse_args()

    if not args.exe.exists():
        print(f"ERROR: Lean executable not found at {args.exe}. Run `lake build evt_estimators` first.", file=sys.stderr)
        return 2

    rng = np.random.default_rng(20261127)
    chk = Checker()

    # -------------------------------------------------------------------------
    # 1. Tail-index & quantile estimators on Pareto(alpha = 2, gamma = 0.5)
    # -------------------------------------------------------------------------
    pareto = (1.0 - rng.uniform(0.0, 1.0, size=200)) ** (-0.5)
    k = 30
    s_desc = np.sort(pareto)[::-1]
    py_hill = float(np.mean(np.log(s_desc[:k]) - np.log(s_desc[k])))
    py_pickands = float(np.log((s_desc[k] - s_desc[2 * k]) / (s_desc[2 * k] - s_desc[4 * k])) / np.log(2.0))
    m1 = py_hill
    m2 = float(np.mean((np.log(s_desc[:k]) - np.log(s_desc[k])) ** 2))
    py_moment = float(m1 + 1.0 - 0.5 / (1.0 - m1 * m1 / m2))
    p_ext = 0.005
    py_weissman = float(s_desc[k] * (k / (len(pareto) * p_ext)) ** py_hill)

    chk.check("Hill estimator (Pareto, k=30)", run_lean(args.exe, ["hill", str(k)], pareto)[0], py_hill, 1e-12)
    chk.check("Pickands estimator (Pareto, k=30)", run_lean(args.exe, ["pickands", str(k)], pareto)[0], py_pickands, 1e-12)
    chk.check("Moment estimator (Pareto, k=30)", run_lean(args.exe, ["moment", str(k)], pareto)[0], py_moment, 1e-12)
    chk.check("Weissman quantile (Pareto, p=0.005)", run_lean(args.exe, ["weissman", str(k), str(p_ext)], pareto)[0], py_weissman, 1e-10)

    # -------------------------------------------------------------------------
    # 2. Sample PWMs, L-moments, and GPD PWM estimators
    # -------------------------------------------------------------------------
    gpd_pos = stats.genpareto.rvs(c=0.25, loc=0.0, scale=2.0, size=150, random_state=rng)
    n = len(gpd_pos)
    ranks = np.array([int(np.sum(gpd_pos <= x)) for x in gpd_pos], dtype=float)
    b0 = float(np.mean(gpd_pos))
    b1 = float(np.mean(gpd_pos * (ranks - 1.0) / (n - 1.0)))
    b2 = float(np.mean(gpd_pos * (ranks - 1.0) * (ranks - 2.0) / ((n - 1.0) * (n - 2.0))))
    l1, l2, l3 = b0, 2.0 * b1 - b0, 6.0 * b2 - 6.0 * b1 + b0
    t3 = l3 / l2
    gpd_pwm_xi = 2.0 - l1 / l2
    gpd_pwm_sig = l1 * (l1 / l2 - 1.0)

    lean_lm = run_lean(args.exe, ["lmoments"], gpd_pos)
    for idx, (label, ref) in enumerate([
        ("Sample PWM b0", b0),
        ("Sample PWM b1", b1),
        ("Sample PWM b2", b2),
        ("Sample L-moment l1", l1),
        ("Sample L-moment l2", l2),
        ("Sample L-moment l3", l3),
        ("Sample L-skewness t3", t3),
        ("GPD PWM shape xi_hat", gpd_pwm_xi),
        ("GPD PWM scale sigma_hat", gpd_pwm_sig),
    ]):
        chk.check(label, lean_lm[idx], ref, 1e-11)

    # -------------------------------------------------------------------------
    # 3. GEV log-likelihood, return levels, and MLEs vs scipy.stats.genextreme
    #    NOTE: scipy.stats.genextreme uses c = -xi (opposite sign to Coles/dHF/evd)!
    # -------------------------------------------------------------------------
    gev_cases = [
        ("Frechet xi=0.25", 0.25, 1.5, 2.0),
        ("Gumbel xi=0.0", 0.0, 1.5, 2.0),
        ("Weibull xi=-0.25", -0.25, 1.5, 2.0),
    ]
    gev_samples: dict[str, np.ndarray] = {}
    for label, xi, mu, sig in gev_cases:
        xs = stats.genextreme.rvs(c=-xi, loc=mu, scale=sig, size=120, random_state=rng)
        gev_samples[label] = xs
        lean_ll = run_lean(args.exe, ["gev-loglik", str(xi), str(mu), str(sig)], xs)[0]
        scipy_ll = float(np.sum(stats.genextreme.logpdf(xs, c=-xi, loc=mu, scale=sig)))
        chk.check(f"GEV loglik vs scipy ({label})", lean_ll, scipy_ll, 1e-9, "scipy c=-xi")

        # Verify scipy's opposite sign genuinely disagrees when xi != 0
        if xi != 0.0:
            wrong_sign_ll = float(np.sum(stats.genextreme.logpdf(xs, c=+xi, loc=mu, scale=sig)))
            assert abs(lean_ll - wrong_sign_ll) > 1.0, "Expected scipy +xi sign convention to differ"

        m = 100.0
        lean_rl = run_lean(args.exe, ["gev-rl", str(xi), str(mu), str(sig), str(m)])[0]
        scipy_rl = float(stats.genextreme.ppf(1.0 - 1.0 / m, c=-xi, loc=mu, scale=sig))
        chk.check(f"GEV 100-rl vs scipy ({label})", lean_rl, scipy_rl, 1e-11, "scipy c=-xi")

    # GEV MLE comparison vs scipy.stats.genextreme.fit (on Fréchet sample)
    xs_fr = gev_samples["Frechet xi=0.25"]
    lean_xi, lean_mu, lean_sig, lean_mle_ll = run_lean(args.exe, ["gev-mle"], xs_fr)
    sc_c, sc_mu, sc_sig = stats.genextreme.fit(xs_fr)
    sc_xi = -sc_c
    sc_mle_ll = float(np.sum(stats.genextreme.logpdf(xs_fr, c=sc_c, loc=sc_mu, scale=sc_sig)))
    chk.check("GEV MLE xi vs scipy (Frechet)", lean_xi, sc_xi, 1e-4, "scipy c=-xi")
    chk.check("GEV MLE mu vs scipy (Frechet)", lean_mu, sc_mu, 1e-4)
    chk.check("GEV MLE sigma vs scipy (Frechet)", lean_sig, sc_sig, 1e-4)
    chk.check("GEV MLE loglik vs scipy (Frechet)", lean_mle_ll, sc_mle_ll, 1e-6)

    # Gumbel 2-parameter MLE & return-level variance vs scipy.stats.gumbel_r
    xs_gu = gev_samples["Gumbel xi=0.0"]
    lean_gmu, lean_gsig, lean_gll = run_lean(args.exe, ["gumbel-mle"], xs_gu)
    sc_gmu, sc_gsig = stats.gumbel_r.fit(xs_gu)
    sc_gll = float(np.sum(stats.gumbel_r.logpdf(xs_gu, loc=sc_gmu, scale=sc_gsig)))
    chk.check("Gumbel MLE mu vs scipy.gumbel_r", lean_gmu, sc_gmu, 1e-5)
    chk.check("Gumbel MLE sigma vs scipy.gumbel_r", lean_gsig, sc_gsig, 1e-5)
    chk.check("Gumbel MLE loglik vs scipy.gumbel_r", lean_gll, sc_gll, 1e-7)

    # Gumbel return-level asymptotic variance formula check
    gamma_em = 0.577215664901532860606512090082402431
    ym100 = -math.log(1.0 - 1.0 / 100.0)
    ref_gvar = (2.0 ** 2) * (1.0 + 6.0 * (1.0 - gamma_em - math.log(ym100)) ** 2 / (math.pi ** 2))
    lean_gvar = run_lean(args.exe, ["gumbel-rl-var", "2.0", "100.0"])[0]
    chk.check("Gumbel 100-rl asymptotic var", lean_gvar, ref_gvar, 1e-12)

    # -------------------------------------------------------------------------
    # 4. GPD log-likelihood, return levels, and MLEs vs scipy.stats.genpareto
    # -------------------------------------------------------------------------
    gpd_cases = [
        ("Pareto xi=0.3", 0.3, 1.8),
        ("Exp xi=0.0", 0.0, 1.8),
        ("Beta xi=-0.2", -0.2, 1.8),
    ]
    gpd_samples: dict[str, np.ndarray] = {}
    for label, xi, sig in gpd_cases:
        xs = stats.genpareto.rvs(c=xi, loc=0.0, scale=sig, size=120, random_state=rng)
        gpd_samples[label] = xs
        lean_ll = run_lean(args.exe, ["gpd-loglik", str(xi), str(sig)], xs)[0]
        scipy_ll = float(np.sum(stats.genpareto.logpdf(xs, c=xi, loc=0.0, scale=sig)))
        chk.check(f"GPD loglik vs scipy ({label})", lean_ll, scipy_ll, 1e-9)

        u, zeta, N = 5.0, 0.1, 1000.0
        lean_rl = run_lean(args.exe, ["gpd-rl", str(u), str(xi), str(sig), str(zeta), str(N)])[0]
        scipy_rl = u + float(stats.genpareto.ppf(1.0 - 1.0 / (N * zeta), c=xi, loc=0.0, scale=sig))
        chk.check(f"GPD POT return level vs scipy ({label})", lean_rl, scipy_rl, 1e-11)

    xs_gp = gpd_samples["Pareto xi=0.3"]
    lean_gpxi, lean_gpsig, lean_gpll = run_lean(args.exe, ["gpd-mle"], xs_gp)
    sc_gpxi, _, sc_gpsig = stats.genpareto.fit(xs_gp, floc=0.0)
    sc_gpll = float(np.sum(stats.genpareto.logpdf(xs_gp, c=sc_gpxi, loc=0.0, scale=sc_gpsig)))
    chk.check("GPD MLE xi vs scipy (floc=0)", lean_gpxi, sc_gpxi, 1e-4)
    chk.check("GPD MLE sigma vs scipy (floc=0)", lean_gpsig, sc_gpsig, 1e-4)
    chk.check("GPD MLE loglik vs scipy (floc=0)", lean_gpll, sc_gpll, 1e-6)

    # -------------------------------------------------------------------------
    # 5. Extremal-index estimators on moving-max (theta = 0.5) & ARMAX (theta = 0.3)
    # -------------------------------------------------------------------------
    z = rng.exponential(scale=1.0, size=601)
    movmax = np.maximum(z[:-1], z[1:])  # 2-step moving maximum, true theta = 0.5
    u_mm = float(np.quantile(movmax, 0.90))
    r_mm = 5

    # Exact Python reference of the four formal definitions
    exc_mask = movmax > u_mm
    tc = int(np.sum(exc_mask))
    py_blocks = sum(1 for j in range(len(movmax) // r_mm) if np.any(exc_mask[j * r_mm : (j + 1) * r_mm])) / tc
    py_runs = sum(1 for i in range(len(movmax) - r_mm) if exc_mask[i] and not np.any(exc_mask[i + 1 : i + 1 + r_mm])) / tc
    py_sliding = sum(1 for i in range(len(movmax) - r_mm + 1) if np.any(exc_mask[i : i + r_mm])) / (r_mm * tc)
    exc_idx = np.flatnonzero(exc_mask)
    T = np.diff(exc_idx).astype(float)
    if np.all(T <= 2):
        py_intervals = min(1.0, 2.0 * (np.sum(T) ** 2) / (len(T) * np.sum(T ** 2)))
    else:
        py_intervals = min(1.0, 2.0 * (np.sum(T - 1.0) ** 2) / (len(T) * np.sum((T - 1.0) * (T - 2.0))))

    lean_b, lean_rn, lean_sl, lean_iv = run_lean(args.exe, ["extremal-index", str(r_mm), f"{u_mm:.17g}"], movmax)
    chk.check("Blocks estimator (movmax, r=5)", lean_b, py_blocks, 1e-12)
    chk.check("Runs estimator (movmax, r=5)", lean_rn, py_runs, 1e-12)
    chk.check("Sliding-blocks estimator (movmax, r=5)", lean_sl, py_sliding, 1e-12)
    chk.check("Intervals estimator (movmax)", lean_iv, py_intervals, 1e-12)

    # -------------------------------------------------------------------------
    # 6. Cross-checks against R (`evd` and `exdex`)
    # -------------------------------------------------------------------------
    if not args.skip_r:
        def r_vec(arr: np.ndarray) -> str:
            return "c(" + ",".join(f"{x:.17g}" for x in arr) + ")"

        r_code = f"""
suppressPackageStartupMessages({{
  library(evd)
  library(exdex)
}})
x_fr <- {r_vec(gev_samples["Frechet xi=0.25"])}
x_gu <- {r_vec(gev_samples["Gumbel xi=0.0"])}
x_wb <- {r_vec(gev_samples["Weibull xi=-0.25"])}
x_gp <- {r_vec(gpd_samples["Pareto xi=0.3"])}
x_mm <- {r_vec(movmax)}

f_fr <- fgev(x_fr, std.err = FALSE)
f_gu <- fgev(x_gu, shape = 0, std.err = FALSE)
f_gp <- fpot(x_gp, threshold = 0, std.err = FALSE)

# evd::exi(x, u, r = 0) is the Ferro-Segers (2003) intervals estimator;
# evd::exi(x, u, r = r) is the runs estimator with run length r.
exi_int <- exi(x_mm, u = {u_mm:.17g}, r = 0)
exi_run <- exi(x_mm, u = {u_mm:.17g}, r = {r_mm})
# Also compute exdex::spm (Northrop 2015 sliding/disjoint block-maxima estimator) for reference reporting
spm_res <- spm(x_mm, b = {r_mm})

cat(sprintf(
  '{{"gev_ll_fr": %.15f, "gev_ll_gu": %.15f, "gev_ll_wb": %.15f, "gev_rl_fr": %.15f, "gev_rl_gu": %.15f, "gev_rl_wb": %.15f, "gev_mle_xi": %.15f, "gev_mle_mu": %.15f, "gev_mle_sig": %.15f, "gumbel_mle_mu": %.15f, "gumbel_mle_sig": %.15f, "gpd_ll_pos": %.15f, "gpd_rl_pos": %.15f, "gpd_mle_xi": %.15f, "gpd_mle_sig": %.15f, "evd_exi_int": %.15f, "evd_exi_run": %.15f, "exdex_spm_sliding": %.15f}}\\n',
  sum(dgev(x_fr, loc = 1.5, scale = 2.0, shape = 0.25, log = TRUE)),
  sum(dgev(x_gu, loc = 1.5, scale = 2.0, shape = 0.0, log = TRUE)),
  sum(dgev(x_wb, loc = 1.5, scale = 2.0, shape = -0.25, log = TRUE)),
  qgev(0.99, loc = 1.5, scale = 2.0, shape = 0.25),
  qgev(0.99, loc = 1.5, scale = 2.0, shape = 0.0),
  qgev(0.99, loc = 1.5, scale = 2.0, shape = -0.25),
  f_fr$estimate["shape"], f_fr$estimate["loc"], f_fr$estimate["scale"],
  f_gu$estimate["loc"], f_gu$estimate["scale"],
  sum(dgpd(x_gp, loc = 0.0, scale = 1.8, shape = 0.3, log = TRUE)),
  5.0 + qgpd(1.0 - 1.0 / (1000.0 * 0.1), loc = 0.0, scale = 1.8, shape = 0.3),
  f_gp$estimate["shape"], f_gp$estimate["scale"],
  exi_int, exi_run,
  unname(spm_res$theta_sl["N2015"])
))
"""
        r_out = run_r(r_code)

        chk.check("GEV loglik vs R evd::dgev (Frechet)", run_lean(args.exe, ["gev-loglik", "0.25", "1.5", "2.0"], gev_samples["Frechet xi=0.25"])[0], r_out["gev_ll_fr"], 1e-9)
        chk.check("GEV loglik vs R evd::dgev (Gumbel)", run_lean(args.exe, ["gev-loglik", "0.0", "1.5", "2.0"], gev_samples["Gumbel xi=0.0"])[0], r_out["gev_ll_gu"], 1e-9)
        chk.check("GEV loglik vs R evd::dgev (Weibull)", run_lean(args.exe, ["gev-loglik", "-0.25", "1.5", "2.0"], gev_samples["Weibull xi=-0.25"])[0], r_out["gev_ll_wb"], 1e-9)
        chk.check("GEV 100-rl vs R evd::qgev (Frechet)", run_lean(args.exe, ["gev-rl", "0.25", "1.5", "2.0", "100.0"])[0], r_out["gev_rl_fr"], 1e-11)
        chk.check("GEV 100-rl vs R evd::qgev (Gumbel)", run_lean(args.exe, ["gev-rl", "0.0", "1.5", "2.0", "100.0"])[0], r_out["gev_rl_gu"], 1e-11)
        chk.check("GEV 100-rl vs R evd::qgev (Weibull)", run_lean(args.exe, ["gev-rl", "-0.25", "1.5", "2.0", "100.0"])[0], r_out["gev_rl_wb"], 1e-11)
        chk.check("GEV MLE xi vs R evd::fgev", lean_xi, r_out["gev_mle_xi"], 1e-3)
        chk.check("GEV MLE mu vs R evd::fgev", lean_mu, r_out["gev_mle_mu"], 1e-3)
        chk.check("GEV MLE sigma vs R evd::fgev", lean_sig, r_out["gev_mle_sig"], 1e-3)
        chk.check("Gumbel MLE mu vs R evd::fgev(shape=0)", lean_gmu, r_out["gumbel_mle_mu"], 1e-3)
        chk.check("Gumbel MLE sigma vs R evd::fgev(shape=0)", lean_gsig, r_out["gumbel_mle_sig"], 1e-3)
        chk.check("GPD loglik vs R evd::dgpd (Pareto)", run_lean(args.exe, ["gpd-loglik", "0.3", "1.8"], gpd_samples["Pareto xi=0.3"])[0], r_out["gpd_ll_pos"], 1e-9)
        chk.check("GPD POT rl vs R evd::qgpd (Pareto)", run_lean(args.exe, ["gpd-rl", "5.0", "0.3", "1.8", "0.1", "1000.0"])[0], r_out["gpd_rl_pos"], 1e-11)
        chk.check("GPD MLE xi vs R evd::fpot", lean_gpxi, r_out["gpd_mle_xi"], 1e-3)
        chk.check("GPD MLE sigma vs R evd::fpot", lean_gpsig, r_out["gpd_mle_sig"], 1e-3)
        chk.check("Intervals est vs R evd::exi(r=0)", lean_iv, r_out["evd_exi_int"], 1e-12)
        # Note on R evd::exi(r=5) runs estimator boundary convention:
        # evd::exi counts the final exceedance cluster (treating post-sample observations as <= u),
        # while ExtremeValueTheory.runsEstimator restricts to indices i < n - r so every run is fully observed.
        # On a sample of size 600 with ~60 exceedances, they differ by at most 1 / tailCount!
        chk.check(
            "Runs est vs R evd::exi(r=5)",
            lean_rn,
            r_out["evd_exi_run"],
            1.0 / tc + 1e-12,
            f"boundary convention diff <= 1/N_u = {1.0/tc:.4f}",
        )
        print(
            f"\nConvention note (informational): on movmax (true theta=0.5), "
            f"threshold sliding-blocks = {lean_sl:.4f}, R exdex::spm (Northrop 2015 block-maxima) = {r_out['exdex_spm_sliding']:.4f}."
        )

    return chk.summary()


if __name__ == "__main__":
    sys.exit(main())
