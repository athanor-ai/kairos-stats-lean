/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# SIR Final Size Equation — Positive Solution When R₀ > 1

The Kermack-McKendrick final size relation for the SIR epidemic model states
that the fraction `r` of the population ultimately infected satisfies the
transcendental equation:

    r = 1 - exp(-R₀ · r)

## Main result

* `sir_final_size_positive_solution` — when R₀ > 1, there exists r ∈ (0, 1)
  satisfying r = 1 - exp(-R₀·r).

## Proof strategy

Define h(r) = 1 - exp(-R₀·r) - r. The key observations are:
1. h(0) = 0 and h'(0) = R₀ - 1 > 0, so h is strictly increasing near 0.
2. Specifically, h'(r) = R₀·exp(-R₀·r) - 1 > 0 for r < log(R₀)/R₀.
3. So h is strictly increasing on [0, log(R₀)/R₀] via `strictMonoOn_of_deriv_pos`.
4. Therefore h(δ) > h(0) = 0 for δ := log(R₀)/(2·R₀) ∈ (0, log(R₀)/R₀).
5. h(1) = -exp(-R₀) < 0.
6. By the Intermediate Value Theorem (`intermediate_value_Icc'`) on [δ, 1],
   there exists r ∈ [δ, 1] ⊆ (0, 1) with h(r) = 0.

## References

* Kermack, W.O. and McKendrick, A.G. "A contribution to the mathematical
  theory of epidemics." Proc. Roy. Soc. London A (1927) 115: 700-721.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Bio.SIRFinalSize

/-- **Kermack-McKendrick final size: positive epidemic fraction.**
When the basic reproduction number R₀ > 1, the final-size equation
r = 1 - exp(-R₀·r) has a solution r ∈ (0, 1). This r represents the
fraction of the population ultimately infected in an SIR epidemic. -/
@[stat_lemma]
theorem sir_final_size_positive_solution
    (R₀ : ℝ) (hR0 : 1 < R₀) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ r = 1 - Real.exp (-(R₀ * r)) := by
  have hR0pos : 0 < R₀ := by linarith
  have hlogR0 : 0 < Real.log R₀ := Real.log_pos hR0
  -- Test point δ = log(R₀)/(2·R₀) lies in (0, log(R₀)/R₀) ⊂ (0, 1)
  set δ := Real.log R₀ / (2 * R₀)
  have h2R0 : 0 < 2 * R₀ := by positivity
  have hδ_pos : 0 < δ := div_pos hlogR0 (by positivity)
  have hδ_lt_one : δ < 1 := by
    rw [div_lt_one h2R0]
    nlinarith [Real.add_one_le_exp (Real.log R₀), Real.exp_log hR0pos]
  have hδ_lt_half : δ < Real.log R₀ / R₀ := by
    show Real.log R₀ / (2 * R₀) < Real.log R₀ / R₀
    gcongr; linarith
  -- h(r) = 1 - exp(-R₀·r) - r is strictly increasing on [0, log(R₀)/R₀]
  -- because h'(r) = R₀·exp(-R₀·r) - 1 > 0 when r < log(R₀)/R₀
  have hstrictmono : StrictMonoOn (fun r : ℝ => 1 - Real.exp (-(R₀ * r)) - r)
      (Set.Icc 0 (Real.log R₀ / R₀)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (by fun_prop)
    intro r hr
    rw [interior_Icc] at hr
    obtain ⟨hr_pos, hr_lt⟩ := hr
    -- Compute deriv h r = R₀·exp(-R₀·r) - 1
    have hinner : HasDerivAt (fun r : ℝ => -(R₀ * r)) (-R₀) r := by
      have hh := (hasDerivAt_id r).const_mul R₀; simp at hh; exact hh.neg
    have hexp := (Real.hasDerivAt_exp _).comp r hinner
    have hd : HasDerivAt (fun r : ℝ => 1 - Real.exp (-(R₀ * r)) - r)
        (0 - Real.exp (-(R₀ * r)) * -R₀ - 1) r :=
      ((hasDerivAt_const _ _).sub hexp).sub (hasDerivAt_id _)
    rw [hd.deriv]
    -- Show R₀·exp(-R₀·r) - 1 > 0 using exp(-R₀·r) > 1/R₀ (since r < log(R₀)/R₀)
    have hexpbound : 1 / R₀ < Real.exp (-(R₀ * r)) := by
      rw [← Real.exp_log (div_pos one_pos hR0pos)]
      apply Real.exp_lt_exp.mpr
      rw [Real.log_div one_ne_zero (ne_of_gt hR0pos), Real.log_one, zero_sub]
      linarith [(lt_div_iff₀ hR0pos).mp hr_lt]
    nlinarith [mul_div_cancel₀ 1 (ne_of_gt hR0pos)]
  -- h(δ) > 0 = h(0) since δ > 0 and h is strictly increasing on [0, log(R₀)/R₀]
  have hhδ_pos : 0 < 1 - Real.exp (-(R₀ * δ)) - δ := by
    have hh0 : (1 : ℝ) - Real.exp (-(R₀ * 0)) - 0 = 0 := by simp
    calc 0 = 1 - Real.exp (-(R₀ * 0)) - 0 := hh0.symm
    _ < 1 - Real.exp (-(R₀ * δ)) - δ :=
      hstrictmono (by simp; positivity) ⟨le_of_lt hδ_pos, le_of_lt hδ_lt_half⟩ hδ_pos
  -- h(1) = -exp(-R₀) < 0
  have hh1_neg : 1 - Real.exp (-(R₀ * 1)) - 1 < 0 := by
    ring_nf; linarith [Real.exp_pos (-R₀)]
  -- Intermediate Value Theorem on [δ, 1]: ∃ r ∈ [δ, 1] with h(r) = 0
  obtain ⟨r, hr_mem, hr_eq⟩ :=
    intermediate_value_Icc' (le_of_lt hδ_lt_one)
      (by fun_prop : ContinuousOn (fun r : ℝ => 1 - Real.exp (-(R₀ * r)) - r) (Set.Icc δ 1))
      (show (0 : ℝ) ∈ Set.Icc (1 - Real.exp (-(R₀ * 1)) - 1) (1 - Real.exp (-(R₀ * δ)) - δ) from
        ⟨le_of_lt hh1_neg, le_of_lt hhδ_pos⟩)
  -- r ∈ [δ, 1] ⊂ (0, 1) and h(r) = 0 means r = 1 - exp(-R₀·r)
  refine ⟨r, lt_of_lt_of_le hδ_pos hr_mem.1, ?_, ?_⟩
  · rcases lt_or_eq_of_le hr_mem.2 with h | h
    · exact h
    · exfalso; simp only [← h] at hr_eq; ring_nf at hr_eq
      linarith [Real.exp_pos (-(r * R₀))]
  · linarith

end Pythia.Bio.SIRFinalSize
