import ExtremeValueTheory

/-!
# Downstream check

A client of the library, built by `.github/workflows/downstream.yml` in a fresh Lake project that
requires this repository, as the README's "Use it in your project" section tells a reader to do. It
imports only the umbrella module and restates the theorem the README quotes.
-/

example {G : CumulativeDistributionFunction} (hG : G.IsExtremeValueDistr) :
    (∃ (A : AffineIncrEquiv), A • G = standardGumbelCDF) ∨
      (∃ (A : AffineIncrEquiv) (ξ : ℝ) (hξ : 0 < ξ), A • G = standardFrechetCDF hξ) ∨
      (∃ (A : AffineIncrEquiv) (ξ : ℝ) (hξ : 0 < ξ), A • G = standardWeibullCDF hξ) :=
  hG.classification
