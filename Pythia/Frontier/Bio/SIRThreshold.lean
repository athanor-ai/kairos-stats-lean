/-
Pythia.Frontier.Bio.SIRThreshold -- the basic reproduction number
R_0 and the SIR epidemic threshold theorem.

Reference: Kermack, W.O. & McKendrick, A.G. (1927). "A contribution
to the mathematical theory of epidemics." Proc. Roy. Soc. London A
115(772):700-721.

The SIR model with infection rate β and recovery rate γ has the
basic reproduction number R_0 = β / γ. The threshold theorem states:

    R_0 ≤ 1  ⟹  the infected population I(t) is monotonically
                 nonincreasing in t (no epidemic);
    R_0 > 1  ⟹  there is a window in which I(t) strictly increases
                 (epidemic outbreak).

Here we formalize the simplest form: the equilibrium threshold for
the proportional model dI/dt = β S I - γ I.
-/
import Mathlib

namespace Pythia.Frontier.Bio

/-- The basic reproduction number for the SIR model. -/
noncomputable def basicReproductionNumber (beta gamma : ℝ) : ℝ :=
  beta / gamma

/-
Threshold inequality: under R_0 ≤ 1, the rate of new infections
    βSI is at most the recovery rate γI for every (S, I) with
    S ≤ 1, I ≥ 0, β > 0, γ > 0.
-/
theorem sir_subcritical_recovery_dominates
    {beta gamma S I : ℝ}
    (hβ : 0 < beta) (hγ : 0 < gamma)
    (hR0 : basicReproductionNumber beta gamma ≤ 1)
    (hS : S ≤ 1) (hI : 0 ≤ I) :
    beta * S * I ≤ gamma * I := by
  unfold basicReproductionNumber at hR0;
  rw [ div_le_one hγ ] at hR0;
  gcongr;
  nlinarith

/-
Supercritical threshold: under R_0 > 1, there exists a
    susceptible level S∗ > 0 (specifically S∗ = γ/β = 1/R_0) such that
    βS∗I > γI strictly whenever I > 0; this S∗ is the herd-immunity
    threshold.
-/
theorem sir_supercritical_outbreak_threshold
    {beta gamma : ℝ}
    (hβ : 0 < beta) (hγ : 0 < gamma)
    (hR0 : 1 < basicReproductionNumber beta gamma) :
    ∃ S_star : ℝ, 0 < S_star ∧ S_star < 1 ∧
      ∀ S I : ℝ, S_star < S → 0 < I → gamma * I < beta * S * I := by
  exact ⟨ gamma / beta, div_pos hγ hβ, by rw [ div_lt_one hβ ] ; unfold basicReproductionNumber at hR0; rw [ lt_div_iff₀ hγ ] at *; linarith, fun S I hS hI => by nlinarith [ mul_lt_mul_of_pos_left hS hI, mul_div_cancel₀ gamma hβ.ne' ] ⟩

end Pythia.Frontier.Bio