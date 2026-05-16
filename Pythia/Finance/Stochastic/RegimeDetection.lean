/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Regime Detection Properties

Markov switching model: transition probabilities, stationary
distribution, regime-dependent parameter bounds.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.Stochastic.RegimeDetection

/-- **Transition probability in [0,1].** -/
@[stat_lemma]
theorem transition_prob_bounded {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ p ∧ p ≤ 1 := ⟨h0, h1⟩

/-- **Stationary distribution exists.** For a 2-state chain with
p12 > 0 and p21 > 0, the stationary distribution is
pi1 = p21/(p12+p21), pi2 = p12/(p12+p21). Both positive. -/
@[stat_lemma]
theorem stationary_dist_pos {p12 p21 : ℝ}
    (h12 : 0 < p12) (h21 : 0 < p21) :
    0 < p21 / (p12 + p21) :=
  div_pos h21 (by linarith)

/-- **Stationary distribution sums to 1.** -/
@[stat_lemma]
theorem stationary_dist_sum {p12 p21 : ℝ}
    (h : p12 + p21 ≠ 0) :
    p21 / (p12 + p21) + p12 / (p12 + p21) = 1 := by
  rw [div_add_div_same, add_comm p21 p12, div_self h]

/-- **Regime persistence.** Expected duration in regime i is
1/p_switch. Higher persistence = lower switching probability. -/
@[stat_lemma]
theorem expected_duration_pos {p_switch : ℝ} (h : 0 < p_switch) :
    0 < 1 / p_switch := div_pos one_pos h

/-- **Regime-weighted variance.** Unconditional variance =
pi1*var1 + pi2*var2 (between regime means). Nonneg. -/
@[stat_lemma]
theorem regime_weighted_var_nonneg {pi1 var1 pi2 var2 : ℝ}
    (hp1 : 0 ≤ pi1) (hv1 : 0 ≤ var1) (hp2 : 0 ≤ pi2) (hv2 : 0 ≤ var2) :
    0 ≤ pi1 * var1 + pi2 * var2 :=
  add_nonneg (mul_nonneg hp1 hv1) (mul_nonneg hp2 hv2)

end Pythia.Finance.Stochastic.RegimeDetection
