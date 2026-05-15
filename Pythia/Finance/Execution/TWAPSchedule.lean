/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# TWAP Schedule Properties

Proves properties of time-weighted average price scheduling
beyond optimality: completion guarantee, participation rate
bounds, and schedule adjustment.
-/
import Mathlib
import Pythia.Tactic.Pythia

open Finset

namespace Pythia.Finance.Execution.TWAPSchedule

/-- **Participation rate bounded.** TWAP targets Q/T shares per
unit time. Participation rate = (Q/T) / V where V is market volume.
For the rate to be below a limit: Q/(T*V) <= limit. -/
@[stat_lemma]
theorem participation_rate_bounded {Q T V limit : ℝ}
    (hT : 0 < T) (hV : 0 < V) (h : Q ≤ limit * T * V) :
    Q / (T * V) ≤ limit := by
  rwa [div_le_iff₀ (mul_pos hT hV)]

/-- **Lower participation reduces impact.** Slower execution
(longer T) means lower participation rate. -/
@[stat_lemma]
theorem longer_horizon_lower_rate {Q V : ℝ}
    (hQ : 0 ≤ Q) (hV : 0 < V)
    {T₁ T₂ : ℝ} (hT1 : 0 < T₁) (hT : T₁ ≤ T₂) :
    Q / (T₂ * V) ≤ Q / (T₁ * V) := by
  apply div_le_div_of_nonneg_left hQ (mul_pos hT1 hV)
  exact mul_le_mul_of_nonneg_right hT (le_of_lt hV)

/-- **Schedule completeness.** Sum of n equal slices of Q/n equals Q. -/
@[stat_lemma]
theorem schedule_completes {Q : ℝ} {n : ℕ} (hn : (n : ℝ) ≠ 0) :
    n • (Q / ↑n) = Q := by
  rw [nsmul_eq_mul, mul_div_cancel₀ Q hn]

/-- **Shortfall from incomplete execution.** If only k of n slices
execute, shortfall = (n-k)/n * Q. -/
@[stat_lemma]
theorem shortfall_nonneg {Q : ℝ} {k n : ℕ}
    (hQ : 0 ≤ Q) (h : k ≤ n) :
    0 ≤ (↑n - ↑k) / ↑n * Q := by
  apply mul_nonneg _ hQ
  apply div_nonneg
  · exact sub_nonneg.mpr (Nat.cast_le (α := ℝ) |>.mpr h)
  · exact Nat.cast_nonneg (α := ℝ) n

/-- **Adaptive TWAP: remaining quantity over remaining time.** -/
@[stat_lemma]
theorem adaptive_slice {Q_remaining T_remaining : ℝ}
    (hQ : 0 ≤ Q_remaining) (hT : 0 < T_remaining) :
    0 ≤ Q_remaining / T_remaining :=
  div_nonneg hQ (le_of_lt hT)

end Pythia.Finance.Execution.TWAPSchedule
