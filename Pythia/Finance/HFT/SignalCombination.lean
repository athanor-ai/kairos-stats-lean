/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Signal Combination (alpha construction)

Proves properties of linear signal combination for alpha generation.
A combined signal s = sum w_i * s_i inherits properties from components.
-/
import Mathlib
import Pythia.Tactic.Pythia

open Finset

namespace Pythia.Finance.HFT.SignalCombination

/-- Combined signal: weighted sum of component signals. -/
noncomputable def combinedSignal {n : ℕ} (w s : Fin n → ℝ) : ℝ :=
  ∑ i, w i * s i

/-- **Combined signal bounded.** If each signal is in [-B, B] and
weights are nonneg summing to 1, the combined signal is in [-B, B]. -/
@[stat_lemma]
theorem combinedSignal_bounded {n : ℕ} (w s : Fin n → ℝ) (B : ℝ)
    (h_w_nonneg : ∀ i, 0 ≤ w i)
    (h_w_sum : ∑ i, w i = 1)
    (h_bounded : ∀ i, |s i| ≤ B) :
    |combinedSignal w s| ≤ B := by
  unfold combinedSignal
  calc |∑ i, w i * s i|
      ≤ ∑ i, |w i * s i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, w i * |s i| := by
        congr 1; ext i; rw [abs_mul, abs_of_nonneg (h_w_nonneg i)]
    _ ≤ ∑ i, w i * B := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (h_bounded i) (h_w_nonneg i)
    _ = B := by rw [← Finset.sum_mul, h_w_sum, one_mul]

/-- **Zero signal from zero weights.** -/
@[stat_lemma]
theorem combinedSignal_zero_weights {n : ℕ} (s : Fin n → ℝ) :
    combinedSignal (fun _ => 0) s = 0 := by
  unfold combinedSignal; simp

/-- **Single signal extraction.** With weight 1 on signal j and
0 on others, the combined signal equals signal j. -/
@[stat_lemma]
theorem combinedSignal_single {n : ℕ} (s : Fin n → ℝ) (j : Fin n)
    (w : Fin n → ℝ) (h_j : w j = 1)
    (h_rest : ∀ i, i ≠ j → w i = 0) :
    combinedSignal w s = s j := by
  unfold combinedSignal
  have : ∑ i, w i * s i = w j * s j + ∑ i ∈ Finset.univ.erase j, w i * s i := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  rw [this, h_j, one_mul]
  have h_zero : ∑ i ∈ Finset.univ.erase j, w i * s i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [h_rest i (Finset.ne_of_mem_erase hi), zero_mul]
  linarith

end Pythia.Finance.HFT.SignalCombination
