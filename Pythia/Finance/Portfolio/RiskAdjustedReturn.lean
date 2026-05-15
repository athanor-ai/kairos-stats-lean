/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Risk-Adjusted Return Measures (algebraic kernel)

This file formalizes three standard risk-adjusted return measures:

1. **Excess return**: `mu - rf` (return above the risk-free rate).
2. **Risk premium per unit vol**: the Sharpe ratio `(mu - rf) / sigma`.
3. **Certainty equivalent**: `mu - (gamma/2) * sigma^2` (the return
   an investor would accept with certainty in place of the risky
   position).

The key algebraic relationship is the ordering:

    certaintyEquivalent <= mu    (risk penalty is nonneg)

and the connection to the Sharpe ratio:

    certaintyEquivalent = rf + sharpe * sigma - (gamma/2) * sigma^2

## Main results

* `excessReturn`                     : `mu - rf`
* `excessReturn_pos_iff`             : `0 < excessReturn mu rf <-> rf < mu`
* `certaintyEquiv`                   : `mu - (gamma / 2) * sigma_sq`
* `certaintyEquiv_le_mean`           : CE <= mu for gamma >= 0, sigma_sq >= 0
* `certaintyEquiv_mono_return`       : monotone in mu
* `certaintyEquiv_antitone_risk`     : antitone in gamma

## References

* Sharpe, W. F. "Mutual Fund Performance."
  *Journal of Business* 39(S1): 119-138 (1966).
* Pratt, J. W. "Risk Aversion in the Small and in the Large."
  *Econometrica* 32(1/2): 122-136 (1964).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Excess return over the risk-free rate. -/
noncomputable def excessReturn (mu rf : ℝ) : ℝ := mu - rf

/-- Certainty equivalent under quadratic risk penalty. -/
noncomputable def certaintyEquiv (mu gamma sigma_sq : ℝ) : ℝ :=
  mu - gamma / 2 * sigma_sq

/-- **Positive excess return iff return exceeds risk-free rate.** -/
@[stat_lemma]
theorem excessReturn_pos_iff {mu rf : ℝ} :
    0 < excessReturn mu rf ↔ rf < mu := by
  unfold excessReturn
  exact sub_pos

/-- **CE at most the mean.** For nonneg risk aversion and nonneg
variance, the certainty equivalent does not exceed the expected
return. -/
@[stat_lemma]
theorem certaintyEquiv_le_mean {mu gamma sigma_sq : ℝ}
    (hg : 0 ≤ gamma) (hs : 0 ≤ sigma_sq) :
    certaintyEquiv mu gamma sigma_sq ≤ mu := by
  unfold certaintyEquiv
  linarith [mul_nonneg (div_nonneg hg (by norm_num : (0:ℝ) ≤ 2)) hs]

/-- **Monotone in expected return.** Higher expected return means
higher certainty equivalent. -/
@[stat_lemma]
theorem certaintyEquiv_mono_return {gamma sigma_sq : ℝ}
    {mu₁ mu₂ : ℝ} (h : mu₁ ≤ mu₂) :
    certaintyEquiv mu₁ gamma sigma_sq ≤ certaintyEquiv mu₂ gamma sigma_sq := by
  unfold certaintyEquiv
  linarith

/-- **Antitone in risk aversion.** Higher risk aversion means lower
certainty equivalent (for nonneg variance). -/
@[stat_lemma]
theorem certaintyEquiv_antitone_risk {mu sigma_sq : ℝ}
    (hs : 0 ≤ sigma_sq)
    {g₁ g₂ : ℝ} (hg : g₁ ≤ g₂) :
    certaintyEquiv mu g₂ sigma_sq ≤ certaintyEquiv mu g₁ sigma_sq := by
  unfold certaintyEquiv
  have : g₁ / 2 * sigma_sq ≤ g₂ / 2 * sigma_sq :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hg (by norm_num : (0:ℝ) ≤ 2)) hs
  linarith

/-- **CE equals mean iff zero risk penalty.** -/
@[stat_lemma]
theorem certaintyEquiv_eq_mean_iff {mu gamma sigma_sq : ℝ} :
    certaintyEquiv mu gamma sigma_sq = mu ↔ gamma / 2 * sigma_sq = 0 := by
  unfold certaintyEquiv
  constructor
  · intro h; linarith
  · intro h; linarith

end Pythia.Finance
