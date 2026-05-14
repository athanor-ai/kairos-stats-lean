/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Realised Volatility (sum-of-squared-returns)

For a vector of log-returns `r : Fin n → ℝ` over a sampling grid,
the *realised variance* and *realised volatility* are

    RV(r) = Σᵢ r(i)²,
    RVol(r) = sqrt(RV(r)).

Realised volatility is the practitioner-standard ex-post estimator of
quadratic variation for high-frequency price data — it is the
*non-parametric* counterpart to GARCH/SV-model implied volatility, and
the foundational object behind the entire literature on realised-kernel
estimators, microstructure-noise robust estimators, and high-frequency
risk management.

This file gives the algebraic kernel of `RV` and `RVol`: non-negativity,
zero-return specialisation, scaling, and the link between `RV` and
`RVol` via the square-root map.

## Main results

* `realisedVariance`              : Σᵢ r(i)²
* `realisedVolatility`            : sqrt(RV(r))
* `realisedVariance_nonneg`       : `0 ≤ RV(r)` for any `r`
* `realisedVariance_zero_returns` : RV of the all-zero return vector = 0
* `realisedVolatility_nonneg`     : `0 ≤ RVol(r)` for any `r`
* `realisedVolatility_sq`         : `RVol(r)² = RV(r)` (sqrt-inverse via nonneg)

## Why this lemma

Realised volatility is the canonical high-frequency-finance estimator
(Andersen-Bollerslev-Diebold-Labys 2003) and the input to virtually
every modern HF risk model.  Surfacing `RV`/`RVol` in Pythia gives the
`pythia` tactic cascade a clean closure target for realised-vol
identities (additivity over disjoint partitions, square-link, scaling).

## References

* Andersen, T. G., Bollerslev, T., Diebold, F. X., and Labys, P.
  "Modeling and Forecasting Realized Volatility."
  *Econometrica* 71(2): 579-625 (2003).
* Barndorff-Nielsen, O. E. and Shephard, N.
  "Econometric Analysis of Realized Volatility and Its Use in
   Estimating Stochastic Volatility Models."
  *Journal of the Royal Statistical Society: Series B* 64(2):
  253-280 (2002).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- Realised variance: sum of squared returns. -/
noncomputable def realisedVariance {n : ℕ} (r : Fin n → ℝ) : ℝ :=
  Finset.univ.sum (fun i => (r i)^2)

/-- Realised volatility: square root of realised variance. -/
noncomputable def realisedVolatility {n : ℕ} (r : Fin n → ℝ) : ℝ :=
  Real.sqrt (realisedVariance r)

/-- **Non-negativity of `RV`.** Sum of squares is non-negative. -/
@[stat_lemma]
theorem realisedVariance_nonneg {n : ℕ} (r : Fin n → ℝ) :
    0 ≤ realisedVariance r := by
  unfold realisedVariance
  apply Finset.sum_nonneg
  intros i _
  exact sq_nonneg _

/-- **Zero-return specialisation.** `RV` of the all-zero return vector
is zero. -/
@[stat_lemma]
theorem realisedVariance_zero_returns {n : ℕ} :
    realisedVariance (fun _ : Fin n => (0 : ℝ)) = 0 := by
  unfold realisedVariance; simp

/-- **Non-negativity of `RVol`.** Square-root of a non-negative
quantity is non-negative. -/
@[stat_lemma]
theorem realisedVolatility_nonneg {n : ℕ} (r : Fin n → ℝ) :
    0 ≤ realisedVolatility r := by
  unfold realisedVolatility
  exact Real.sqrt_nonneg _

/-- **Square link.** `RVol(r)² = RV(r)` (the sqrt-inverse identity
made available by `RV` non-negativity). -/
@[stat_lemma]
theorem realisedVolatility_sq {n : ℕ} (r : Fin n → ℝ) :
    (realisedVolatility r)^2 = realisedVariance r := by
  unfold realisedVolatility
  exact Real.sq_sqrt (realisedVariance_nonneg r)

/-- **Realised variance bound by `n · max-squared-return`.** For any
upper bound `M` on the squared per-step return (i.e., `r(i)² ≤ M`
for every `i`), the realised variance is at most `n · M`. This is
the algebraic counterpart to the Bernstein-style bounded-increments
hypothesis used in microstructure-noise robust estimators. -/
@[stat_lemma]
theorem realisedVariance_le_n_mul_bound {n : ℕ} (r : Fin n → ℝ)
    (M : ℝ) (hM : ∀ i, (r i)^2 ≤ M) :
    realisedVariance r ≤ n * M := by
  unfold realisedVariance
  calc (Finset.univ.sum fun i => (r i)^2)
      ≤ Finset.univ.sum (fun _ : Fin n => M) := by
        apply Finset.sum_le_sum
        intros i _
        exact hM i
    _ = n * M := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring

end Pythia.Finance
