# Extremal Conditional Independence in Max-Linear DAGs

Companion empirical benchmark for the Lean 4 formalization in [`Research/MaxLinearCI/`](../MaxLinearCI.lean), resolving the open problem of Engelke, Hentschel, Lalancette, and Röttger (`arXiv:2402.02187`).

## What the Lean formalization proves

Across all finite DAGs $G$ and all positive recursive max-linear models $M$:

$$d\text{-separation} \;\subsetneq\; *\text{-separation} \;\subsetneq\; \text{footprint separation} \;\subseteq\; \text{universal }\Lambda\text{-CI} \;\subsetneq\; \text{fixed-weight }\Lambda\text{-CI}.$$

In particular, on the **4-node Star DAG** (`0 → 1, 0 → 2, 0 → 3`), `starDAG_extremalCondIndep` and `starDAG_paretoCondIndep` prove that `0 ⊥ 1 | {2, 3}` holds for **every** positive weight matrix — even though `0 → 1` is a direct causal edge — because conditioning on both sibling children spiking pins down the parent deterministically ($Y_0 = \frac{B_{00}}{B_{20}} Y_2$, forcing $\operatorname{IQR}(\log(Y_0 / Y_2)) \to 0$).

## What the empirical script demonstrates

[`star_test_benchmark.py`](star_test_benchmark.py) downloads the two flagship benchmark datasets from `sebastian-engelke/graphicalExtremes` (`flights.rda` and `danube.rda`, cached locally under `.cache/` and not committed to git) and runs two checks:

1. **Zero-parameter Star-DAG specification test on US flight delays (`flights.rda`):**
   Compares 7 physical US hub-and-spoke stars (e.g., `DFW → (ABI, TYR, CLL)`, `ATL → (VLD, DHN, CSG)`) against **matched-$\chi_{90}$** Hüsler–Reiss and recursive max-linear stars of the same sample size. Even with identical pairwise tail dependence $\chi_{90}$, real flight delays have $\operatorname{IQR}(\log(Y_{\text{Hub}} / Y_{\text{Spoke}_2})) \in [1.47, 2.00]$ — matching Hüsler–Reiss ($[1.40, 1.82]$) and **9× to 45× wider** than matched-$\chi_{90}$ max-linear models ($[0.04, 0.21]$).
2. **Upper Danube river topology & concentration (`danube.rda`):**
   Confirms that Danube's 30 physical `flow_edges` form a pure converging in-tree (`max out-degree = 1`, zero $d$-sep / $*$-sep / footprint-sep gaps) while showing much sharper ray concentration along direct river edges ($\operatorname{IQR} \approx 0.17\text{–}0.22$ on strong edges).

## Running the benchmark

```bash
uv run --with numpy --with scipy --with rdata python3 Research/MaxLinearCI/empirical/star_test_benchmark.py
```

(On NixOS, set `LD_LIBRARY_PATH` to a store path containing `libstdc++.so.6` if using `uv` wheels.)
