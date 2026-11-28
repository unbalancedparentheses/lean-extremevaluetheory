#!/usr/bin/env python3
"""Empirical Star-DAG specification test on US flight delays and Upper Danube floods.

Companion script to `Research/MaxLinearCI/`.
Downloads `flights.rda` and `danube.rda` from `sebastian-engelke/graphicalExtremes`
into a local `.cache/` directory on first run (ignored by git).
"""

from __future__ import annotations

import urllib.request
from pathlib import Path

import numpy as np
import rdata
from scipy import stats

CACHE_DIR = Path(__file__).resolve().parent / ".cache"
BASE_URL = "https://raw.githubusercontent.com/sebastian-engelke/graphicalExtremes/master/data"


def ensure_dataset(filename: str) -> Path:
    CACHE_DIR.mkdir(parents=True, exist_ok=True)
    path = CACHE_DIR / filename
    if not path.exists():
        print(f"Downloading {filename} from graphicalExtremes...")
        urllib.request.urlretrieve(f"{BASE_URL}/{filename}", path)
    return path


def to_pareto(X: np.ndarray) -> np.ndarray:
    """Empirical rank transformation to unit Pareto(1) margins."""
    n, d = X.shape
    Y = np.zeros_like(X, dtype=float)
    for j in range(d):
        ranks = stats.rankdata(X[:, j])
        Y[:, j] = 1.0 / (1.0 - ranks / (n + 1.0))
    return Y


def chi_emp(Y: np.ndarray, i: int, j: int, u: float = 10.0) -> float:
    m = Y[:, i] > u
    return float(np.mean(Y[m, j] > u)) if m.sum() > 0 else float("nan")


def angular_star_test(Y: np.ndarray, u: float = 10.0) -> tuple[int, float, float, float, float]:
    """Scale-free angular test of 0 _|_ 1 | {2, 3} on {Y_2 > u, Y_3 > u}.

    Returns (n_box, partial_spearman_rho, p_value, iqr_log_y0_over_y2, mad_hub).
    """
    m = (Y[:, 2] > u) & (Y[:, 3] > u)
    nb = int(m.sum())
    if nb < 15:
        return nb, float("nan"), float("nan"), float("nan"), float("nan")
    Ym = Y[m]
    r0 = np.log(Ym[:, 0] / Ym[:, 2])
    r1 = np.log(Ym[:, 1] / Ym[:, 2])
    r3 = np.log(Ym[:, 3] / Ym[:, 2])
    r0_rk = stats.rankdata(r0)
    r1_rk = stats.rankdata(r1)
    r3_rk = stats.rankdata(r3)
    Z = np.column_stack([np.ones(nb), r3_rk, r3_rk**2])
    res0 = r0_rk - Z @ np.linalg.lstsq(Z, r0_rk, rcond=None)[0]
    res1 = r1_rk - Z @ np.linalg.lstsq(Z, r1_rk, rcond=None)[0]
    rho, pval = stats.pearsonr(res0, res1)
    iqr_r0 = float(np.percentile(r0, 75) - np.percentile(r0, 25))
    mad_hub = float(np.median(np.abs(r0 - np.median(r0))))
    return nb, float(rho), float(pval), iqr_r0, mad_hub


def sim_max_linear_star(chis: list[float], n: int, rng: np.random.Generator) -> np.ndarray:
    """Unit-Frechet recursive max-linear Star DAG matching pairwise chi(0, i) = chis[i-1]."""
    Z = -1.0 / np.log(rng.uniform(0.0, 1.0, size=(n, 4)))
    Y = np.zeros((n, 4))
    Y[:, 0] = Z[:, 0]
    for i in range(1, 4):
        w = float(np.clip(chis[i - 1], 0.05, 0.95))
        Y[:, i] = np.maximum(w * Z[:, 0], (1.0 - w) * Z[:, i])
    return to_pareto(Y)


def sim_husler_reiss_star(chis: list[float], n: int, rng: np.random.Generator) -> np.ndarray:
    """Exact Husler-Reiss max-stable Star tree (Dombry-Engelke-Oesting 2016 Alg. 1)."""
    gammas = [(2.0 * stats.norm.ppf(1.0 - np.clip(c, 0.05, 0.95) / 2.0)) ** 2 for c in chis]
    d = 4
    G = np.zeros((d, d))
    for i in range(1, d):
        G[0, i] = G[i, 0] = gammas[i - 1]
    for i in range(1, d):
        for j in range(i + 1, d):
            G[i, j] = G[j, i] = gammas[i - 1] + gammas[j - 1]

    Y = np.zeros((n, d))
    for j in range(d):
        Sigma = 0.5 * (G[j, :, None] + G[j, None, :] - G)
        idx = [k for k in range(d) if k != j]
        Lchol = np.linalg.cholesky(Sigma[np.ix_(idx, idx)] + 1e-12 * np.eye(d - 1))
        mu = -0.5 * G[j, :]
        E_cur = rng.exponential(1.0, size=n)
        active = np.ones(n, dtype=bool)
        while np.any(active):
            act_idx = np.where(active)[0]
            m = len(act_idx)
            W = np.zeros((m, d))
            W[:, idx] = rng.standard_normal((m, d - 1)) @ Lchol.T
            P_vec = np.exp(W + mu[None, :])
            cand = P_vec / E_cur[act_idx, None]
            ok = np.ones(m, dtype=bool)
            for k in range(j):
                ok &= cand[:, k] < Y[act_idx, k]
            if np.any(ok):
                upd = act_idx[ok]
                Y[upd] = np.maximum(Y[upd], cand[ok])
            E_cur[act_idx] += rng.exponential(1.0, size=m)
            active[act_idx] = (1.0 / E_cur[act_idx]) > Y[act_idx, j]
    return to_pareto(Y)


def main() -> None:
    rng = np.random.default_rng(42)

    flights_path = ensure_dataset("flights.rda")
    danube_path = ensure_dataset("danube.rda")

    fl = rdata.read_rda(flights_path)["flights"]
    fc = fl["flightCounts"]
    delays = fl["delays"]
    iata = list(fc.coords[fc.dims[0]].values)
    idx_of = {c: i for i, c in enumerate(iata)}
    arr = delays.values[:, :, 0]
    dep = delays.values[:, :, 1]

    stars = [
        ("DFW", ["ABI", "TYR", "CLL"]),
        ("DFW", ["ABI", "TYR", "FSM"]),
        ("ATL", ["DHN", "CSG", "AGS"]),
        ("ATL", ["VLD", "DHN", "CSG"]),
        ("ATL", ["VLD", "DHN", "MLB"]),
        ("ORD", ["CMI", "CWA", "SPI"]),
        ("IAH", ["BRO", "LCH", "MFE"]),
    ]

    print("=== 1. US FLIGHT DELAY STARS vs MATCHED-CHI HUSLER-REISS & MAX-LINEAR (u = 10) ===")
    for hub, spokes in stars:
        Xraw = np.column_stack([dep[:, idx_of[hub]]] + [arr[:, idx_of[s]] for s in spokes])
        ok = ~np.isnan(Xraw).any(axis=1)
        Y_real = to_pareto(Xraw[ok])
        n = len(Y_real)
        chis = [chi_emp(Y_real, 0, i, u=10.0) for i in [1, 2, 3]]
        Y_hr = sim_husler_reiss_star(chis, n, rng)
        Y_ml = sim_max_linear_star(chis, n, rng)
        print(f"\nStar {hub} -> ({', '.join(spokes)}) [n={n}, chi_90=({chis[0]:.2f},{chis[1]:.2f},{chis[2]:.2f})]:")
        for label, Yc in [("REAL FLIGHTS", Y_real), ("HUSLER-REISS", Y_hr), ("MAX-LINEAR  ", Y_ml)]:
            nb, rho, p, iqr0, mad = angular_star_test(Yc, u=10.0)
            print(f"  {label} (n={nb:3d}): rho={rho:+.3f} (p={p:.2e}) | IQR(log Y0/Y2)={iqr0:.3f}, MAD={mad:.3f}")

    dn = rdata.read_rda(danube_path)["danube"]
    edges_dn = [(int(u) - 1, int(v) - 1) for u, v in dn["flow_edges"]]
    out_deg: dict[int, int] = {}
    for u, _ in edges_dn:
        out_deg[u] = out_deg.get(u, 0) + 1
    Y_dn = to_pareto(dn["data_clustered"].values)
    print(f"\n=== 2. UPPER DANUBE RIVER (31 stations, max out-degree = {max(out_deg.values())}) ===")
    for u, v in edges_dn[:10]:
        m = (Y_dn[:, u] > 5.0) & (Y_dn[:, v] > 5.0)
        if m.sum() >= 10:
            r = np.log(Y_dn[m, u] / Y_dn[m, v])
            iqr = float(np.percentile(r, 75) - np.percentile(r, 25))
            chi = chi_emp(Y_dn, u, v, u=5.0)
            print(f"  Edge {u + 1:2d} -> {v + 1:2d}: n_joint={m.sum():2d}, chi_80={chi:.2f}, IQR(log Yu/Yv)={iqr:.3f}")


if __name__ == "__main__":
    main()
