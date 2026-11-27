/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/

/-!
# Executable (`Float`) reference estimators for extreme value theory

Standalone `Float` implementations of the main estimators formalized in `ExtremeValueTheory`.
Every function cites the exact formal definition it implements so that `scripts/crosscheck_estimators.py`
can cross-check the library's conventions and formulas directly against Python (`scipy.stats`) and
R (`evd`, `exdex`).

Conventions (matching Coles 2001, de Haan–Ferreira 2006, and `ExtremeValueTheory`):
* **GEV shape sign:** `ξ > 0` is heavy-tailed (Fréchet), `ξ = 0` is Gumbel, `ξ < 0` is bounded
  (Weibull). Note that `scipy.stats.genextreme` uses the opposite sign `c = -ξ`.
* **GPD shape sign:** `ξ > 0` is heavy-tailed (Pareto), `ξ = 0` is exponential, `ξ < 0` is
  bounded. Matches both `scipy.stats.genpareto` (`c = ξ`) and R `evd::dgpd` (`shape = ξ`).
* **Order statistics:** `orderStat xs j` is 0-indexed from the largest (`j = 0` is `max xs`).
-/

namespace ExtremeValueTheory.Executable

/-! ### Order statistics and tail-index estimators -/

/-- Sort an array in descending order (`a[0] ≥ a[1] ≥ … ≥ a[n-1]`). -/
def sortDesc (xs : Array Float) : Array Float :=
  xs.qsort (fun a b => a > b)

/-- Descending order statistic, 0-indexed from the largest (`j = 0` is the maximum).
Implements `ExtremeValueTheory.orderStat` in `ExtremeValueTheory/Statistics/OrderStatistics.lean`. -/
def orderStat (xs : Array Float) (j : Nat) : Float :=
  let s := sortDesc xs
  if h : j < s.size then s[j] else 0.0

/-- **Hill estimator** `H_{k,n} = (1/k) ∑_{i<k} (log X_{(i)} - log X_{(k)})`.
Implements `ExtremeValueTheory.hill` in `ExtremeValueTheory/Statistics/Hill.lean`. -/
def hill (xs : Array Float) (k : Nat) : Float :=
  if k == 0 || k >= xs.size then 0.0
  else
    let s := sortDesc xs
    let logThresh := Float.log s[k]!
    let sum := Id.run do
      let mut acc := 0.0
      for i in [:k] do
        acc := acc + (Float.log s[i]! - logThresh)
      return acc
    sum / k.toFloat

/-- **Pickands estimator** `γ̂_P = log((X_{(k)} - X_{(2k)}) / (X_{(2k)} - X_{(4k)})) / log 2`.
Implements `ExtremeValueTheory.pickands` in `ExtremeValueTheory/Statistics/Pickands.lean`. -/
def pickands (xs : Array Float) (k : Nat) : Float :=
  if k == 0 || 4 * k >= xs.size then 0.0
  else
    let s := sortDesc xs
    let num := s[k]! - s[2 * k]!
    let den := s[2 * k]! - s[4 * k]!
    Float.log (num / den) / Float.log 2.0

/-- **`j`-th log-moment** `M^{(j)}_{k,n} = (1/k) ∑_{i<k} (log X_{(i)} - log X_{(k)})^j`.
Implements `ExtremeValueTheory.logMoment` in `ExtremeValueTheory/Statistics/Moment.lean`. -/
def logMoment (xs : Array Float) (k j : Nat) : Float :=
  if k == 0 || k >= xs.size then 0.0
  else
    let s := sortDesc xs
    let logThresh := Float.log s[k]!
    let sum := Id.run do
      let mut acc := 0.0
      for i in [:k] do
        let d := Float.log s[i]! - logThresh
        acc := acc + d ^ j.toFloat
      return acc
    sum / k.toFloat

/-- **Dekkers–Einmahl–de Haan moment estimator**
`M_{k,n} = M^{(1)} + 1 - (1/2) (1 - (M^{(1)})² / M^{(2)})⁻¹`.
Implements `ExtremeValueTheory.momentEstimator` in `ExtremeValueTheory/Statistics/Moment.lean`. -/
def momentEstimator (xs : Array Float) (k : Nat) : Float :=
  let m1 := logMoment xs k 1
  let m2 := logMoment xs k 2
  m1 + 1.0 - 0.5 / (1.0 - (m1 * m1) / m2)

/-- **Weissman extreme-quantile estimator** `x̂_p = X_{(k)} (k / (n p))^{H_{k,n}}`.
Implements `ExtremeValueTheory.weissman` in `ExtremeValueTheory/Statistics/ExtremeQuantile.lean`. -/
def weissman (xs : Array Float) (k : Nat) (p : Float) : Float :=
  if k == 0 || k >= xs.size then 0.0
  else
    let s := sortDesc xs
    let n := xs.size.toFloat
    let h := hill xs k
    s[k]! * ((k.toFloat / (n * p)) ^ h)

/-! ### Probability-weighted moments and L-moments -/

/-- Empirical rank `#{j < n : x_j ≤ t}`.
Implements `ExtremeValueTheory.countLE` in `ExtremeValueTheory/Statistics/LMomentsEstimators.lean`. -/
def countLE (xs : Array Float) (t : Float) : Nat := Id.run do
  let mut c := 0
  for x in xs do
    if x <= t then c := c + 1
  return c

/-- Weight `∏_{k<r} (R - 1 - k) / (n - 1 - k)`.
Implements `ExtremeValueTheory.pwmWeight` in `ExtremeValueTheory/Statistics/LMomentsEstimators.lean`. -/
def pwmWeight (n r R : Nat) : Float := Id.run do
  let mut prod := 1.0
  for k in [:r] do
    prod := prod * ((R.toFloat - 1.0 - k.toFloat) / (n.toFloat - 1.0 - k.toFloat))
  return prod

/-- **Unbiased sample probability-weighted moment** `b_r`.
Implements `ExtremeValueTheory.samplePWM` in `ExtremeValueTheory/Statistics/LMomentsEstimators.lean`. -/
def samplePWM (xs : Array Float) (r : Nat) : Float :=
  let n := xs.size
  if n == 0 then 0.0
  else
    let sum := Id.run do
      let mut acc := 0.0
      for x in xs do
        let rank := countLE xs x
        acc := acc + x * pwmWeight n r rank
      return acc
    sum / n.toFloat

/-- First sample L-moment `l₁ = b₀`. Implements `ExtremeValueTheory.sampleLMoment1`. -/
def sampleLMoment1 (xs : Array Float) : Float := samplePWM xs 0

/-- Second sample L-moment `l₂ = 2 b₁ - b₀`. Implements `ExtremeValueTheory.sampleLMoment2`. -/
def sampleLMoment2 (xs : Array Float) : Float := 2.0 * samplePWM xs 1 - samplePWM xs 0

/-- Third sample L-moment `l₃ = 6 b₂ - 6 b₁ + b₀`. Implements `ExtremeValueTheory.sampleLMoment3`. -/
def sampleLMoment3 (xs : Array Float) : Float :=
  6.0 * samplePWM xs 2 - 6.0 * samplePWM xs 1 + samplePWM xs 0

/-- Sample L-skewness `t₃ = l₃ / l₂`. Implements `ExtremeValueTheory.sampleLSkewness`. -/
def sampleLSkewness (xs : Array Float) : Float := sampleLMoment3 xs / sampleLMoment2 xs

/-- **GPD PWM shape estimator** (Hosking–Wallis 1987): `ξ̂ = 2 - l₁ / l₂`.
Implements `ExtremeValueTheory.gpdPWMShapeEst` in `ExtremeValueTheory/Statistics/LMomentsEstimators.lean`. -/
def gpdPWMShapeEst (xs : Array Float) : Float :=
  2.0 - sampleLMoment1 xs / sampleLMoment2 xs

/-- **GPD PWM scale estimator** (Hosking–Wallis 1987): `σ̂ = l₁ (l₁ / l₂ - 1)`.
Implements `ExtremeValueTheory.gpdPWMScaleEst` in `ExtremeValueTheory/Statistics/LMomentsEstimators.lean`. -/
def gpdPWMScaleEst (xs : Array Float) : Float :=
  let l1 := sampleLMoment1 xs
  let l2 := sampleLMoment2 xs
  l1 * (l1 / l2 - 1.0)

/-! ### GEV, Gumbel, and GPD log-likelihoods, return levels, and MLEs -/

/-- Box–Cox transform `h_ξ(x) = (x^ξ - 1)/ξ`, `h_0(x) = log x`.
Implements `ExtremeValueTheory.boxCox` in `ExtremeValueTheory/RegularVariation/SecondOrder.lean`. -/
def boxCox (xi x : Float) : Float :=
  if Float.abs xi < 1e-12 then Float.log x else ((x ^ xi) - 1.0) / xi

/-- Single-observation GEV log-density (returns `-inf` outside the support or for `σ ≤ 0`).
Implements `ExtremeValueTheory.gevLogDensityE` in `ExtremeValueTheory/Statistics/GEVConsistency.lean`. -/
def gevLogDensity (xi mu sigma x : Float) : Float :=
  if sigma <= 0.0 then -1.0 / 0.0
  else
    let z := (x - mu) / sigma
    if Float.abs xi < 1e-12 then
      -(Float.log sigma) - z - Float.exp (-z)
    else
      let u := 1.0 + xi * z
      if u <= 0.0 then -1.0 / 0.0
      else -(Float.log sigma) - (1.0 + 1.0 / xi) * Float.log u - (u ^ (-1.0 / xi))

/-- **GEV log-likelihood** `∑_i log f_{ξ,μ,σ}(x_i)`.
Implements `ExtremeValueTheory.gevLogLikE` in `ExtremeValueTheory/Statistics/GEVConsistency.lean`. -/
def gevLogLik (xi mu sigma : Float) (xs : Array Float) : Float := Id.run do
  let mut acc := 0.0
  for x in xs do
    let l := gevLogDensity xi mu sigma x
    if !l.isFinite then return -1.0 / 0.0
    acc := acc + l
  return acc

/-- **Gumbel (`ξ = 0`) log-likelihood**. -/
def gumbelLogLik (mu sigma : Float) (xs : Array Float) : Float :=
  gevLogLik 0.0 mu sigma xs

/-- **GEV `m`-block return level** `z_m = μ + σ h_ξ(1 / (-log(1 - 1/m)))`.
Implements `ExtremeValueTheory.gevReturnLevel` in `ExtremeValueTheory/Statistics/ReturnLevelNormality.lean`. -/
def gevReturnLevel (xi mu sigma m : Float) : Float :=
  let ym := -Float.log (1.0 - 1.0 / m)
  if Float.abs xi < 1e-12 then
    mu - sigma * Float.log ym
  else
    mu + sigma * ((ym ^ (-xi)) - 1.0) / xi

/-- **Gumbel MLE return-level asymptotic variance**
`σ² (1 + 6 (1 - γ - log y_m)² / π²)`.
Implements `ExtremeValueTheory.gumbelReturnLevelVar` in `ExtremeValueTheory/Statistics/GumbelMLENormality.lean`. -/
def gumbelReturnLevelVar (sigma m : Float) : Float :=
  let gamma := 0.577215664901532860606512090082402431
  let pi := 3.141592653589793238462643383279502884
  let ym := -Float.log (1.0 - 1.0 / m)
  let c := 1.0 - gamma - Float.log ym
  sigma * sigma * (1.0 + 6.0 * c * c / (pi * pi))

/-- Single-observation GPD log-density (for excesses `x ≥ 0`, `σ > 0`).
Implements `ExtremeValueTheory.gpdLogDensityE` in `ExtremeValueTheory/Statistics/GPDConsistency.lean`. -/
def gpdLogDensity (xi sigma x : Float) : Float :=
  if sigma <= 0.0 || x < 0.0 then -1.0 / 0.0
  else if Float.abs xi < 1e-12 then
    -(Float.log sigma) - x / sigma
  else
    let u := 1.0 + xi * x / sigma
    if u <= 0.0 then -1.0 / 0.0
    else -(Float.log sigma) - (1.0 + 1.0 / xi) * Float.log u

/-- **GPD log-likelihood** `∑_i log g_{ξ,σ}(x_i)`.
Implements `ExtremeValueTheory.gpdLogLikE` in `ExtremeValueTheory/Statistics/GPDConsistency.lean`. -/
def gpdLogLik (xi sigma : Float) (xs : Array Float) : Float := Id.run do
  let mut acc := 0.0
  for x in xs do
    let l := gpdLogDensity xi sigma x
    if !l.isFinite then return -1.0 / 0.0
    acc := acc + l
  return acc

/-- **POT `N`-observation return level** `x_N = u + σ h_ξ(N ζ)`.
Implements `ExtremeValueTheory.gpdReturnLevel` in `ExtremeValueTheory/Statistics/ReturnLevelNormality.lean`. -/
def gpdReturnLevel (u xi sigma zeta N : Float) : Float :=
  u + sigma * boxCox xi (N * zeta)

/-! ### Simple Nelder–Mead optimization for reference MLEs -/

private def vecAdd (a b : Array Float) : Array Float :=
  Array.ofFn (n := a.size) fun i => a[i.val]! + b[i.val]!

private def vecSub (a b : Array Float) : Array Float :=
  Array.ofFn (n := a.size) fun i => a[i.val]! - b[i.val]!

private def vecScale (s : Float) (a : Array Float) : Array Float :=
  a.map (s * ·)

/-- Nelder–Mead minimization of `f : Array Float → Float` starting from `x0` with step sizes `step`. -/
def nelderMead (f : Array Float → Float) (x0 step : Array Float) (maxIter : Nat := 4000) :
    Array Float × Float := Id.run do
  let d := x0.size
  let mut pts : Array (Array Float × Float) := #[(x0, f x0)]
  for i in [:d] do
    let p := x0.set! i (x0[i]! + step[i]!)
    pts := pts.push (p, f p)
  for _ in [:maxIter] do
    pts := pts.qsort (fun a b => a.2 < b.2)
    let best := pts[0]!
    let worst := pts[d]!
    let secondWorst := pts[d - 1]!
    if Float.abs (worst.2 - best.2) < 1e-13 then
      break
    -- Centroid of the best `d` points
    let mut centroid := Array.replicate d 0.0
    for i in [:d] do
      centroid := vecAdd centroid pts[i]!.1
    centroid := vecScale (1.0 / d.toFloat) centroid
    -- Reflection
    let xr := vecAdd centroid (vecSub centroid worst.1)
    let fr := f xr
    if fr < best.2 then
      -- Expansion
      let xe := vecAdd centroid (vecScale 2.0 (vecSub xr centroid))
      let fe := f xe
      pts := pts.set! d (if fe < fr then (xe, fe) else (xr, fr))
    else if fr < secondWorst.2 then
      pts := pts.set! d (xr, fr)
    else
      -- Contraction
      let xc := if fr < worst.2
        then vecAdd centroid (vecScale 0.5 (vecSub xr centroid))
        else vecAdd centroid (vecScale 0.5 (vecSub worst.1 centroid))
      let fc := f xc
      if fc < min fr worst.2 then
        pts := pts.set! d (xc, fc)
      else
        -- Shrink
        for i in [1 : d + 1] do
          let p := vecAdd best.1 (vecScale 0.5 (vecSub pts[i]!.1 best.1))
          pts := pts.set! i (p, f p)
  pts := pts.qsort (fun a b => a.2 < b.2)
  return pts[0]!

/-- Numerical 3-parameter GEV MLE `(ξ̂, μ̂, σ̂, logLik)` by maximizing `gevLogLik` via Nelder–Mead
(reparameterizing `σ = exp(logσ)` to enforce `σ > 0`). -/
def fitGevMLE (xs : Array Float) : Float × Float × Float × Float :=
  let n := xs.size.toFloat
  let mean := xs.foldl (· + ·) 0.0 / n
  let var := xs.foldl (fun acc x => acc + (x - mean) * (x - mean)) 0.0 / n
  let sd := Float.sqrt (if var > 0.0 then var else 1.0)
  let pi := 3.141592653589793238462643383279502884
  let gamma := 0.577215664901532860606512090082402431
  let sigma0 := sd * Float.sqrt 6.0 / pi
  let mu0 := mean - gamma * sigma0
  let obj (p : Array Float) : Float :=
    let ll := gevLogLik p[0]! p[1]! (Float.exp p[2]!) xs
    if ll.isFinite then -ll else 1e300
  let (p1, _) := nelderMead obj #[0.05, mu0, Float.log sigma0] #[0.1, 0.2 * sigma0, 0.2] 5000
  let (p2, val) := nelderMead obj p1 #[0.01, 0.01 * sigma0, 0.01] 5000
  (p2[0]!, p2[1]!, Float.exp p2[2]!, -val)

/-- Numerical 2-parameter Gumbel (`ξ = 0`) MLE `(μ̂, σ̂, logLik)`. -/
def fitGumbelMLE (xs : Array Float) : Float × Float × Float :=
  let n := xs.size.toFloat
  let mean := xs.foldl (· + ·) 0.0 / n
  let var := xs.foldl (fun acc x => acc + (x - mean) * (x - mean)) 0.0 / n
  let sd := Float.sqrt (if var > 0.0 then var else 1.0)
  let pi := 3.141592653589793238462643383279502884
  let gamma := 0.577215664901532860606512090082402431
  let sigma0 := sd * Float.sqrt 6.0 / pi
  let mu0 := mean - gamma * sigma0
  let obj (p : Array Float) : Float :=
    let ll := gumbelLogLik p[0]! (Float.exp p[1]!) xs
    if ll.isFinite then -ll else 1e300
  let (p1, _) := nelderMead obj #[mu0, Float.log sigma0] #[0.2 * sigma0, 0.2] 4000
  let (p2, val) := nelderMead obj p1 #[0.01 * sigma0, 0.01] 4000
  (p2[0]!, Float.exp p2[1]!, -val)

/-- Numerical 2-parameter GPD MLE `(ξ̂, σ̂, logLik)` for nonnegative excesses `xs`. -/
def fitGpdMLE (xs : Array Float) : Float × Float × Float :=
  let xi0 := gpdPWMShapeEst xs
  let sig0 := gpdPWMScaleEst xs
  let sigInit := if sig0.isFinite && sig0 > 0.0 then sig0 else
    let m := xs.foldl (· + ·) 0.0 / xs.size.toFloat
    if m > 0.0 then m else 1.0
  let xiInit := if xi0.isFinite && xi0 > -0.45 && xi0 < 2.0 then xi0 else 0.1
  let obj (p : Array Float) : Float :=
    let ll := gpdLogLik p[0]! (Float.exp p[1]!) xs
    if ll.isFinite then -ll else 1e300
  let (p1, _) := nelderMead obj #[xiInit, Float.log sigInit] #[0.1, 0.2] 5000
  let (p2, val) := nelderMead obj p1 #[0.01, 0.01] 5000
  (p2[0]!, Float.exp p2[1]!, -val)

/-! ### Extremal-index estimators -/

/-- Count of exceedances `#{i < n : x_i > u}`.
Implements `ExtremeValueTheory.tailCount` in `ExtremeValueTheory/Statistics/ExtremalIndexEstimators.lean`. -/
def tailCount (xs : Array Float) (u : Float) : Nat := Id.run do
  let mut c := 0
  for x in xs do
    if x > u then c := c + 1
  return c

/-- **Disjoint blocks estimator** of the extremal index:
`(# of disjoint blocks of length r with an exceedance) / (# of exceedances)`.
Implements `ExtremeValueTheory.blocksEstimator` in `ExtremeValueTheory/Statistics/ExtremalIndexEstimators.lean`. -/
def blocksEstimator (xs : Array Float) (r : Nat) (u : Float) : Float :=
  let tc := tailCount xs u
  if r == 0 || tc == 0 then 0.0
  else
    let numBlocks := xs.size / r
    let bc := Id.run do
      let mut c := 0
      for j in [:numBlocks] do
        let mut hit := false
        for s in [:r] do
          if xs[j * r + s]! > u then hit := true
        if hit then c := c + 1
      return c
    bc.toFloat / tc.toFloat

/-- **Runs estimator** of the extremal index:
`(# of i < n - r with X_i > u and X_{i+1}, …, X_{i+r} ≤ u) / (# of exceedances)`.
Implements `ExtremeValueTheory.runsEstimator` in `ExtremeValueTheory/Statistics/ExtremalIndexEstimators.lean`. -/
def runsEstimator (xs : Array Float) (r : Nat) (u : Float) : Float :=
  let tc := tailCount xs u
  if tc == 0 || xs.size <= r then 0.0
  else
    let m := xs.size - r
    let rc := Id.run do
      let mut c := 0
      for i in [:m] do
        if xs[i]! > u then
          let mut clear := true
          for s in [:r] do
            if xs[i + 1 + s]! > u then clear := false
          if clear then c := c + 1
      return c
    rc.toFloat / tc.toFloat

/-- **Sliding-blocks estimator** of the extremal index (Cissokho–Kulik 2021):
`(# of sliding windows [i, i+r-1] for i < n - r + 1 with an exceedance) / (r · # of exceedances)`.
Implements `ExtremeValueTheory.slidingBlocksEstimator` in `ExtremeValueTheory/Statistics/SlidingBlocks.lean`. -/
def slidingBlocksEstimator (xs : Array Float) (r : Nat) (u : Float) : Float :=
  let tc := tailCount xs u
  if r == 0 || tc == 0 || xs.size < r then 0.0
  else
    let m := xs.size - r + 1
    let sc := Id.run do
      let mut c := 0
      for i in [:m] do
        let mut hit := false
        for s in [:r] do
          if xs[i + s]! > u then hit := true
        if hit then c := c + 1
      return c
    sc.toFloat / (r.toFloat * tc.toFloat)

/-- Inter-exceedance times `T_j = t_{j+1} - t_j` from the exceedance indices `{i : x_i > u}`. -/
def interExceedanceTimes (xs : Array Float) (u : Float) : Array Float := Id.run do
  let mut idxs : Array Nat := #[]
  for i in [:xs.size] do
    if xs[i]! > u then idxs := idxs.push i
  if idxs.size < 2 then return #[]
  let mut ts : Array Float := #[]
  for j in [:idxs.size - 1] do
    ts := ts.push ((idxs[j + 1]! - idxs[j]!).toFloat)
  return ts

/-- Uncorrected Ferro–Segers intervals estimator `θ̂₁ = 2 (∑ T_i)² / (m ∑ T_i²)`.
Implements `ExtremeValueTheory.intervalsEstimator₁`. -/
def intervalsEstimator1 (ts : Array Float) : Float :=
  let m := ts.size
  if m == 0 then 0.0
  else
    let s1 := ts.foldl (· + ·) 0.0
    let s2 := ts.foldl (fun acc t => acc + t * t) 0.0
    2.0 * s1 * s1 / (m.toFloat * s2)

/-- Bias-corrected Ferro–Segers intervals estimator
`θ̂₂ = 2 (∑ (T_i - 1))² / (m ∑ (T_i - 1)(T_i - 2))`.
Implements `ExtremeValueTheory.intervalsEstimator₂`. -/
def intervalsEstimator2 (ts : Array Float) : Float :=
  let m := ts.size
  if m == 0 then 0.0
  else
    let s1 := ts.foldl (fun acc t => acc + (t - 1.0)) 0.0
    let s2 := ts.foldl (fun acc t => acc + (t - 1.0) * (t - 2.0)) 0.0
    2.0 * s1 * s1 / (m.toFloat * s2)

/-- **Ferro–Segers (2003) intervals estimator** `min(1, θ̂₁)` if `max T_i ≤ 2`, else `min(1, θ̂₂)`.
Implements `ExtremeValueTheory.intervalsEstimator` in
`ExtremeValueTheory/Statistics/ExtremalIndexEstimatorsIntervals.lean`. -/
def intervalsEstimator (xs : Array Float) (u : Float) : Float :=
  let ts := interExceedanceTimes xs u
  if ts.isEmpty then 0.0
  else
    let allLe2 := ts.all (· <= 2.0)
    let raw := if allLe2 then intervalsEstimator1 ts else intervalsEstimator2 ts
    if raw < 1.0 then raw else 1.0

end ExtremeValueTheory.Executable
