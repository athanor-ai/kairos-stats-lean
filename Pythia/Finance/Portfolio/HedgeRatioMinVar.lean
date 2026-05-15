/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Minimum-Variance Hedge Ratio

For a spot asset with variance `vS`, a futures contract with variance
`vF` and covariance with the spot `cSF`, the *minimum-variance hedge
ratio* (the proportion of futures shorted per unit of spot held) is

    h* = cSF / vF.

This is the closed-form solution to
`min_h Var(S - h · F) = vS - 2h · cSF + h² · vF`, which is a quadratic
in `h` minimised at `h = cSF / vF` (assuming `vF > 0`).

## Main results

* `minVarHedgeRatio`            : `cSF / vF`
* `hedgedVariance`              : `vS - 2h·cSF + h²·vF`
* `hedgedVariance_at_optimum`   :
  `hedgedVariance vS vF cSF (minVarHedgeRatio vF cSF) = vS - cSF² / vF`
* `hedgedVariance_le_unhedged`  : optimum-hedged variance ≤ unhedged spot variance
  (when PSD condition `cSF² ≤ vS · vF` holds and `0 < vF`)

## Why this lemma

Minimum-variance hedge ratio is the textbook entrypoint for cross-asset
hedging — equity trading teams compute it daily against futures / ETF
baskets.  Surfacing the closed form in Pythia gives the `pythia`
tactic cascade a clean closure target for basis-risk / cross-hedge
optimisation goals.

## References

* Hull, J. C. *Options, Futures, and Other Derivatives*, 10th ed.
  Pearson (2017), §3.4 (cross-hedging and the minimum-variance hedge
  ratio).
* Ederington, L. H. "The Hedging Performance of the New Futures
  Markets." *Journal of Finance* 34(1): 157-170 (1979).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Hedged-portfolio variance: `Var(S - h·F) = vS - 2h·cSF + h²·vF`. -/
noncomputable def hedgedVariance (vS vF cSF h : ℝ) : ℝ :=
  vS - 2 * h * cSF + h^2 * vF

/-- Minimum-variance hedge ratio: `h* = cSF / vF`. -/
noncomputable def minVarHedgeRatio (vF cSF : ℝ) : ℝ :=
  cSF / vF

/-- **Variance at the optimum.** Plugging the minimum-variance hedge
ratio `h* = cSF/vF` into `hedgedVariance` yields

    hedgedVariance vS vF cSF (cSF/vF) = vS - cSF² / vF. -/
@[stat_lemma]
theorem hedgedVariance_at_optimum {vF : ℝ} (hvF : 0 < vF) (vS cSF : ℝ) :
    hedgedVariance vS vF cSF (minVarHedgeRatio vF cSF) = vS - cSF^2 / vF := by
  unfold hedgedVariance minVarHedgeRatio
  field_simp
  ring

/-- **Optimum-hedged variance ≤ unhedged spot variance.** Under the
positive-semidefinite Cauchy-Schwarz condition `cSF² ≤ vS · vF` and
`vF > 0`, the optimum-hedged variance is bounded above by the
unhedged spot variance.  Equivalently, the hedge weakly reduces
variance — its raison d'être. -/
@[stat_lemma]
theorem hedgedVariance_le_unhedged
    {vS vF cSF : ℝ} (hvF : 0 < vF) (hCS : cSF^2 ≤ vS * vF) :
    hedgedVariance vS vF cSF (minVarHedgeRatio vF cSF) ≤ vS := by
  rw [hedgedVariance_at_optimum hvF]
  have : 0 ≤ cSF^2 / vF := div_nonneg (sq_nonneg _) hvF.le
  linarith

end Pythia.Finance
