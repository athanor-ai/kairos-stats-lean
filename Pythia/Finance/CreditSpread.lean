/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Credit Spread Decomposition

The *credit spread* is the yield difference between a risky bond and
a risk-free bond of the same maturity:

    creditSpread(y_risky, y_rf) = y_risky - y_rf.

Under risk-neutral pricing the expected-loss decomposition gives:

    creditSpread ≈ pd * lgd + risk_premium,

where `pd` is the risk-neutral probability of default, `lgd` is the
loss-given-default (a fraction of face value), and `risk_premium`
captures the excess of the observed spread over expected loss (the
compensation for bearing systematic default risk that cannot be
diversified away).

This module formalises the algebraic skeleton of this decomposition:
the spread is non-negative when the risky yield exceeds the risk-free
yield, vanishes exactly when the yields coincide, expected loss is
non-negative and bounded above by `lgd` when `pd ≤ 1`, is monotone in
`pd`, and the decomposition identity holds by definition.

## Main results

* `creditSpread`                  : `y_risky - y_rf`
* `expectedLoss`                  : `pd * lgd`
* `riskPremium`                   : `spread - expectedLoss pd lgd`
* `creditSpread_nonneg`           : non-negative when `y_risky ≥ y_rf`
* `creditSpread_zero_iff`         : vanishes iff yields are equal
* `expectedLoss_nonneg`           : non-negative when `pd ≥ 0`, `lgd ≥ 0`
* `expectedLoss_le_lgd`           : `pd * lgd ≤ lgd` when `pd ≤ 1`, `lgd ≥ 0`
* `expectedLoss_mono_pd`          : monotone non-decreasing in `pd` for `lgd ≥ 0`
* `riskPremium_decomposition`     : spread = expectedLoss + riskPremium (ring identity)

## References

* Duffie, D. and Singleton, K.
  "Modeling Term Structures of Defaultable Bonds."
  *Review of Financial Studies* 12(4): 687-720 (1999).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Credit spread: the yield difference between a risky bond and a
risk-free bond of the same maturity. -/
def creditSpread (y_risky y_rf : ℝ) : ℝ := y_risky - y_rf

/-- Expected loss under risk-neutral pricing: `pd * lgd`. -/
def expectedLoss (pd lgd : ℝ) : ℝ := pd * lgd

/-- Risk premium: the portion of the credit spread in excess of the
expected loss, capturing compensation for systematic default risk. -/
def riskPremium (spread pd lgd : ℝ) : ℝ := spread - expectedLoss pd lgd

/-- **Non-negativity of the credit spread.** When the risky yield is
at least as large as the risk-free yield, the spread is non-negative. -/
@[stat_lemma]
theorem creditSpread_nonneg {y_risky y_rf : ℝ} (h : y_rf ≤ y_risky) :
    0 ≤ creditSpread y_risky y_rf := by
  unfold creditSpread
  exact sub_nonneg.mpr h

/-- **Zero-spread characterisation.** The credit spread is zero if and
only if the risky yield equals the risk-free yield. -/
@[stat_lemma]
theorem creditSpread_zero_iff (y_risky y_rf : ℝ) :
    creditSpread y_risky y_rf = 0 ↔ y_risky = y_rf := by
  unfold creditSpread
  exact sub_eq_zero

/-- **Non-negativity of expected loss.** For non-negative probability
of default and non-negative loss-given-default, the expected loss is
non-negative. -/
@[stat_lemma]
theorem expectedLoss_nonneg {pd lgd : ℝ} (hpd : 0 ≤ pd) (hlgd : 0 ≤ lgd) :
    0 ≤ expectedLoss pd lgd := by
  unfold expectedLoss
  exact mul_nonneg hpd hlgd

/-- **Expected loss bounded by LGD.** When the probability of default
is at most 1 and LGD is non-negative, the expected loss does not
exceed LGD. This is the risk-neutral no-over-recovery constraint. -/
@[stat_lemma]
theorem expectedLoss_le_lgd {pd lgd : ℝ} (hpd : pd ≤ 1) (hlgd : 0 ≤ lgd) :
    expectedLoss pd lgd ≤ lgd := by
  unfold expectedLoss
  exact mul_le_of_le_one_left hlgd hpd

/-- **Monotonicity in default probability.** For fixed non-negative
LGD, the expected loss is monotone non-decreasing in the probability
of default. -/
@[stat_lemma]
theorem expectedLoss_mono_pd {lgd : ℝ} (hlgd : 0 ≤ lgd)
    {pd₁ pd₂ : ℝ} (h : pd₁ ≤ pd₂) :
    expectedLoss pd₁ lgd ≤ expectedLoss pd₂ lgd := by
  unfold expectedLoss
  exact mul_le_mul_of_nonneg_right h hlgd

/-- **Spread decomposition identity.** The credit spread equals the
expected loss plus the risk premium by definition. -/
@[stat_lemma]
theorem riskPremium_decomposition (y_r y_rf pd lgd : ℝ) :
    creditSpread y_r y_rf =
      expectedLoss pd lgd + riskPremium (creditSpread y_r y_rf) pd lgd := by
  simp only [creditSpread, expectedLoss, riskPremium]
  ring

end Pythia.Finance
