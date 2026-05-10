import Mathlib

-- Synthesis floor confidence: after k consecutive refutations
-- with distinct counterexamples, the block is at synthesis floor.
-- Backs the "when to stop" signal in kairos.memory.

-- Each refutation provides a distinct counterexample
-- k independent refutations give confidence 1 - 2^{-k}

noncomputable def synthesisFloorConfidence (k : ℕ) : ℝ := 1 - (1/2)^k

/-
Confidence increases with more refutations
-/
theorem confidence_monotone (k : ℕ) :
    synthesisFloorConfidence k ≤ synthesisFloorConfidence (k + 1) := by
  exact sub_le_sub_left ( pow_le_pow_of_le_one ( by norm_num ) ( by norm_num ) ( by norm_num ) ) _

/-
Confidence is always in [0, 1)
-/
theorem confidence_bounded (k : ℕ) :
    0 ≤ synthesisFloorConfidence k ∧ synthesisFloorConfidence k < 1 := by
  exact ⟨ sub_nonneg.2 <| pow_le_one₀ ( by norm_num ) <| by norm_num, sub_lt_self _ <| by positivity ⟩

/-
At k=10, confidence > 0.999
-/
theorem confidence_10_high :
    synthesisFloorConfidence 10 > 999/1000 := by
  unfold synthesisFloorConfidence; norm_num;

/-
Zero refutations gives zero confidence
-/
theorem confidence_zero :
    synthesisFloorConfidence 0 = 0 := by
  -- By definition of $synthesisFloorConfidence$, we have $synthesisFloorConfidence 0 = 1 - (1/2)^0 = 1 - 1 = 0$.
  simp [synthesisFloorConfidence]

/-
Confidence approaches 1
-/
theorem confidence_approaches_one :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, 1 - ε < synthesisFloorConfidence k := by
  intro ε hε
  obtain ⟨k, hk⟩ : ∃ k, (1 / 2 : ℝ) ^ k < ε := by
    exact exists_pow_lt_of_lt_one hε one_half_lt_one;
  exact ⟨ k, by unfold synthesisFloorConfidence; linarith ⟩