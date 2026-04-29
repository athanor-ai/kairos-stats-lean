/-
Pythia.Frontier.Bio.WrightFisher -- fixation probability in the
Wright-Fisher model with directional selection.

Reference: Kimura, M. (1962). "On the probability of fixation of
mutant genes in a population." Genetics 47(6):713-719.

For an allele with selection coefficient s and initial frequency p
in a population of size N, the diffusion approximation gives the
fixation probability

    p_fix(p; s, N) = (1 - exp(-2 s N p)) / (1 - exp(-2 s N))

which reduces to p in the neutral limit (s → 0). The function is
continuous in p and monotone increasing in s for fixed (N, p).
-/
import Mathlib

namespace Pythia.Frontier.Bio

/-- Wright-Fisher fixation probability under directional selection. -/
noncomputable def wrightFisherFixation (s : ℝ) (N : ℕ) (p : ℝ) : ℝ :=
  if s = 0 then p
  else (1 - Real.exp (-2 * s * (N : ℝ) * p)) /
       (1 - Real.exp (-2 * s * (N : ℝ)))

/-
Fixation probability is in [0, 1] under standard hypotheses.
-/
theorem wrightFisherFixation_in_unit_interval
    {s : ℝ} {N : ℕ} {p : ℝ} (hN : 0 < N) (hp : 0 ≤ p ∧ p ≤ 1) :
    0 ≤ wrightFisherFixation s N p ∧ wrightFisherFixation s N p ≤ 1 := by
  unfold wrightFisherFixation;
  split_ifs <;> simp_all +decide;
  cases lt_or_gt_of_ne ‹_› <;> simp_all +decide [ div_nonneg_iff, div_le_one_iff ];
  · exact ⟨ Or.inr ⟨ by nlinarith [ show ( N : ℝ ) * p ≥ 0 by exact mul_nonneg ( Nat.cast_nonneg _ ) hp.1 ], by nlinarith [ show ( N : ℝ ) ≥ 1 by norm_cast ] ⟩, Or.inr <| Or.inr ⟨ by nlinarith [ show ( N : ℝ ) ≥ 1 by norm_cast ], by nlinarith [ Real.exp_pos ( - ( 2 * s * N * p ) ), Real.exp_le_exp.2 ( show - ( 2 * s * N * p ) ≤ - ( 2 * s * N ) by nlinarith [ show ( N : ℝ ) ≥ 1 by norm_cast, mul_le_mul_of_nonneg_left hp.2 ( show ( 0 :ℝ ) ≤ N by positivity ) ] ) ] ⟩ ⟩;
  · exact Or.inl ( by linarith [ Real.exp_le_exp.mpr ( show - ( 2 * s * N ) ≤ - ( 2 * s * N * p ) by nlinarith [ mul_nonneg ( mul_nonneg zero_le_two ( le_of_lt ‹0 < s› ) ) ( Nat.cast_nonneg N ) ] ) ] )

/-- Neutral limit: at s = 0, the fixation probability equals the
    initial frequency. -/
theorem wrightFisherFixation_neutral_limit (N : ℕ) (p : ℝ) :
    wrightFisherFixation 0 N p = p := by
  unfold wrightFisherFixation
  simp

/-
A beneficial allele (s > 0) has fixation probability at least p:
    selection cannot harm an allele's fixation chance.
-/
theorem wrightFisherFixation_beneficial_ge_neutral
    {s : ℝ} {N : ℕ} {p : ℝ}
    (hs : 0 < s) (hN : 0 < N) (hp : 0 ≤ p ∧ p ≤ 1) :
    p ≤ wrightFisherFixation s N p := by
  unfold wrightFisherFixation;
  rw [ if_neg hs.ne', le_div_iff₀ ] <;> norm_num;
  · have h_convex : ConvexOn ℝ (Set.univ : Set ℝ) Real.exp := by
      exact convexOn_exp;
    have := h_convex.2 ( Set.mem_univ 0 ) ( Set.mem_univ ( - ( 2 * s * N ) ) );
    have := @this ( 1 - p ) p ( by linarith ) ( by linarith ) ( by linarith ) ; norm_num at * ; ring_nf at * ; linarith;
  · positivity

end Pythia.Frontier.Bio