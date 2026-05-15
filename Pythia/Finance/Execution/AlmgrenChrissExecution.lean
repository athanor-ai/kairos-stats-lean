/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Almgren-Chriss Optimal Execution (closed-form expected cost)

For liquidating a position of `Q` shares over horizon `T` under
linear temporary market impact `η` (per-unit-rate cost), the
naive constant-rate (TWAP-style) execution incurs total expected
temporary-impact cost

    E[cost_TWAP] = η · Q² / T.

This is the closed-form kernel of the Almgren-Chriss optimal-
execution framework — the practitioner-standard model for splitting
a parent order into child slices.  This module surfaces the closed
form and its scaling / monotonicity properties at the algebraic
level (no stochastic-integral machinery).

The full Almgren-Chriss formulation adds a risk-aversion term
`λ · σ² · ∫ x_t² dt` and yields a `sinh`-shaped optimal trajectory;
that extension is deferred to a calculus-tier module.

## Main results

* `twapTemporaryCost`              : `η · Q² / T`
* `twapCost_nonneg`                : `0 ≤ η, T > 0 → 0 ≤ cost`
* `twapCost_quadratic_in_Q`        : doubling the parent order
  quadruples the cost (Q² scaling)
* `twapCost_antitone_in_T`         : longer horizon → lower temporary
  impact (the *patience pays off* identity)
* `twapCost_zero_at_zero_impact`   : `η = 0 → cost = 0`

## Why this lemma

Optimal execution is the practitioner-vocabulary surface where formal
verification differentiates concrete optimal-trading proofs from
hand-waved heuristics.  Almgren-Chriss-style closed forms underpin
every algorithmic-execution risk-engine sanity check; surfacing the
TWAP kernel in Pythia gives the `pythia` tactic cascade a clean
closure target for execution-cost analytics.

## References

* Almgren, R. and Chriss, N.
  "Optimal Execution of Portfolio Transactions."
  *Journal of Risk* 3(2): 5-39 (2001).
* Bertsimas, D. and Lo, A. W.
  "Optimal Control of Execution Costs."
  *Journal of Financial Markets* 1(1): 1-50 (1998).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- TWAP (constant-rate) expected temporary-impact cost under linear
impact coefficient `η`:
    `cost_TWAP(Q, T, η) = η · Q² / T`. -/
noncomputable def twapTemporaryCost (Q T η : ℝ) : ℝ :=
  η * Q^2 / T

/-- **Cost non-negativity.** For non-negative impact and strictly
positive horizon, the TWAP cost is non-negative. -/
@[stat_lemma]
theorem twapCost_nonneg {η T : ℝ} (hη : 0 ≤ η) (hT : 0 < T) (Q : ℝ) :
    0 ≤ twapTemporaryCost Q T η := by
  unfold twapTemporaryCost
  exact div_nonneg (mul_nonneg hη (sq_nonneg Q)) hT.le

/-- **Zero-impact specialisation.** At `η = 0`, TWAP cost is zero
(no temporary impact to pay). -/
@[stat_lemma]
theorem twapCost_zero_at_zero_impact (Q T : ℝ) (hT : T ≠ 0) :
    twapTemporaryCost Q T 0 = 0 := by
  unfold twapTemporaryCost; simp

/-- **Quadratic scaling in parent order size.** Doubling the parent
order quadruples the cost — the canonical `Q²`-scaling identity of
TWAP. -/
@[stat_lemma]
theorem twapCost_quadratic_in_Q (α Q T η : ℝ) (hT : T ≠ 0) :
    twapTemporaryCost (α * Q) T η = α^2 * twapTemporaryCost Q T η := by
  unfold twapTemporaryCost
  rw [mul_pow]; ring

/-- **Patience pays off (antitone in horizon).** For non-negative
impact, non-negative order size, and strictly positive horizons,
the TWAP cost is non-increasing in the execution horizon `T`. -/
@[stat_lemma]
theorem twapCost_antitone_in_T
    {η : ℝ} (hη : 0 ≤ η) {Q : ℝ}
    {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (hT : T₁ ≤ T₂) :
    twapTemporaryCost Q T₂ η ≤ twapTemporaryCost Q T₁ η := by
  unfold twapTemporaryCost
  have h_num : 0 ≤ η * Q^2 := mul_nonneg hη (sq_nonneg Q)
  exact div_le_div_of_nonneg_left h_num hT₁ hT

end Pythia.Finance
