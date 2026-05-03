/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bateman Equation — Oral-Dose PK Positivity

The Bateman equation describes the plasma concentration following an oral
(extravascular) dose in a one-compartment model with first-order absorption
and first-order elimination:

    C(t) = (F·D·k_a) / (V_d·(k_a - k_e)) · (exp(-k_e·t) - exp(-k_a·t))

## Main result

* `bateman_equation_positivity` — C(t) > 0 for t > 0 when k_a > k_e > 0.

## Proof strategy

The prefactor `(F·D·k_a) / (V_d·(k_a - k_e))` is positive since all
parameters are positive and k_a - k_e > 0. The difference term
`exp(-k_e·t) - exp(-k_a·t)` is positive because -k_a·t < -k_e·t for t > 0
(since k_a > k_e), so exp(-k_a·t) < exp(-k_e·t) by strict monotonicity of exp.

## References

* Bateman, H. "The solution of a system of differential equations occurring in
  the theory of radioactive transformations." Proc. Cambridge Phil. Soc. (1910)
  15: 423-427.
* Teorell, T. "Kinetics of distribution of substances administered to the body."
  Arch. Int. Pharmacodyn. (1937) 57: 205-240.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Bio.Bateman

/-- The Bateman oral-dose plasma concentration function.
`F` = bioavailability, `D` = dose, `k_a` = absorption rate constant,
`k_e` = elimination rate constant, `V_d` = volume of distribution, `t` = time. -/
noncomputable def batemanConc (F D k_a k_e V_d t : ℝ) : ℝ :=
  (F * D * k_a) / (V_d * (k_a - k_e)) *
  (Real.exp (-(k_e * t)) - Real.exp (-(k_a * t)))

/-- **Bateman equation positivity.**
For an oral-dose one-compartment PK model, the plasma concentration is strictly
positive for all t > 0 whenever 0 < k_e < k_a (faster absorption than elimination).

The prefactor is positive because F, D, k_a > 0 and k_a - k_e > 0.
The exponential difference is positive because -k_a·t < -k_e·t (since k_a > k_e),
so exp(-k_a·t) < exp(-k_e·t) by strict monotonicity of exp. -/
@[stat_lemma]
theorem bateman_equation_positivity
    (F D k_a k_e V_d t : ℝ)
    (hF : 0 < F) (hD : 0 < D) (hV : 0 < V_d)
    (hke : 0 < k_e) (hka : k_e < k_a) (ht : 0 < t) :
    0 < batemanConc F D k_a k_e V_d t := by
  unfold batemanConc
  apply mul_pos
  · apply div_pos
    · exact mul_pos (mul_pos hF hD) (by linarith)
    · exact mul_pos hV (by linarith)
  · apply sub_pos.mpr
    apply Real.exp_lt_exp.mpr
    nlinarith

end Pythia.Bio.Bateman
