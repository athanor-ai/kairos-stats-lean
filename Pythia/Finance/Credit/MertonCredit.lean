/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Merton Structural Credit Model (algebraic kernel)

In Merton's (1974) structural model, a firm's equity is a European
call option on its assets with strike equal to the face value of
debt. The distance to default (DD) is:

    DD = (log(V/D) + (mu - sigma^2/2) * T) / (sigma * sqrt(T))

where V is asset value, D is debt face value, mu is asset drift,
sigma is asset volatility, and T is time to maturity.

The probability of default is Phi(-DD) where Phi is the standard
normal CDF.

## Main results

* `distanceToDefault`           : the DD formula
* `distanceToDefault_pos`       : DD > 0 under typical conditions
* `distanceToDefault_mono_V`    : DD increases with asset value
* `equityAsCallPayoff`          : equity = max(V - D, 0) at maturity

## References

* Merton, R. C. "On the Pricing of Corporate Debt."
  Journal of Finance 29(2): 449-470 (1974).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- Distance to default in the Merton model.
DD = (log(V/D) + drift_adj * T) / (sigma * sqrt_T). -/
noncomputable def distanceToDefault (log_VD drift_adj T sigma sqrt_T : ℝ) : ℝ :=
  (log_VD + drift_adj * T) / (sigma * sqrt_T)

/-- Equity value at maturity: max(V - D, 0) (call payoff). -/
noncomputable def equityAtMaturity (V D : ℝ) : ℝ :=
  max (V - D) 0

/-- **DD positive under typical conditions.** When log(V/D) > 0
(assets exceed debt in log terms) and drift is nonneg, DD > 0
for positive vol and horizon. -/
@[stat_lemma]
theorem distanceToDefault_pos {log_VD drift_adj T sigma sqrt_T : ℝ}
    (h_log : 0 < log_VD) (h_drift : 0 ≤ drift_adj) (hT : 0 ≤ T)
    (h_vol : 0 < sigma) (h_sqrtT : 0 < sqrt_T) :
    0 < distanceToDefault log_VD drift_adj T sigma sqrt_T := by
  unfold distanceToDefault
  apply div_pos
  · linarith [mul_nonneg h_drift hT]
  · exact mul_pos h_vol h_sqrtT

/-- **DD monotone in asset value.** Higher log(V/D) means larger
distance to default (further from default). -/
@[stat_lemma]
theorem distanceToDefault_mono_logVD {drift_adj T sigma sqrt_T : ℝ}
    (h_vol : 0 < sigma) (h_sqrtT : 0 < sqrt_T)
    {l₁ l₂ : ℝ} (h : l₁ ≤ l₂) :
    distanceToDefault l₁ drift_adj T sigma sqrt_T ≤
      distanceToDefault l₂ drift_adj T sigma sqrt_T := by
  unfold distanceToDefault
  exact div_le_div_of_nonneg_right (by linarith) (le_of_lt (mul_pos h_vol h_sqrtT))

/-- **Equity nonneg.** Equity at maturity is always nonneg
(limited liability). -/
@[stat_lemma]
theorem equityAtMaturity_nonneg (V D : ℝ) :
    0 ≤ equityAtMaturity V D := by
  unfold equityAtMaturity
  exact le_max_right _ _

/-- **Equity equals excess when solvent.** When V >= D, equity
equals the surplus V - D. -/
@[stat_lemma]
theorem equityAtMaturity_solvent {V D : ℝ} (h : D ≤ V) :
    equityAtMaturity V D = V - D := by
  unfold equityAtMaturity
  exact max_eq_left (sub_nonneg.mpr h)

/-- **Equity zero when insolvent.** When V <= D, equity is zero
(shareholders get nothing). -/
@[stat_lemma]
theorem equityAtMaturity_insolvent {V D : ℝ} (h : V ≤ D) :
    equityAtMaturity V D = 0 := by
  unfold equityAtMaturity
  exact max_eq_right (sub_nonpos.mpr h)

end Pythia.Finance
