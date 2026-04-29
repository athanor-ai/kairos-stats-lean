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

/-- Fixation probability is in [0, 1] under standard hypotheses. -/
theorem wrightFisherFixation_in_unit_interval
    {s : ℝ} {N : ℕ} {p : ℝ} (hN : 0 < N) (hp : 0 ≤ p ∧ p ≤ 1) :
    0 ≤ wrightFisherFixation s N p ∧ wrightFisherFixation s N p ≤ 1 := by
  sorry

/-- Neutral limit: at s = 0, the fixation probability equals the
    initial frequency. -/
theorem wrightFisherFixation_neutral_limit (N : ℕ) (p : ℝ) :
    wrightFisherFixation 0 N p = p := by
  unfold wrightFisherFixation
  simp

/-- A beneficial allele (s > 0) has fixation probability at least p:
    selection cannot harm an allele's fixation chance. -/
theorem wrightFisherFixation_beneficial_ge_neutral
    {s : ℝ} {N : ℕ} {p : ℝ}
    (hs : 0 < s) (hN : 0 < N) (hp : 0 ≤ p ∧ p ≤ 1) :
    p ≤ wrightFisherFixation s N p := by
  sorry

end Pythia.Frontier.Bio
