/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pharmacokinetics / Pharmacodynamics (PK/PD)

One-compartment IV-bolus kinetics: AUC identity and half-life relation.

## Main results

* `one_compartment_auc` — AUC = D/(V_d · k_e) for IV-bolus one-compartment model.
* `half_life_clearance_relation` — concentration at half-life equals C_0/2.

## References

* Rowland, M. and Tozer, T.N. *Clinical Pharmacokinetics and Pharmacodynamics*,
  4th ed., Lippincott Williams & Wilkins (2011), Ch. 2.
* Wagner, J.G. *Biopharmaceutics and Relevant Pharmacokinetics*,
  Drug Intelligence Publications (1971).
-/
import Mathlib
import Pythia.Tactic.Pythia

open MeasureTheory Set Real

namespace Pythia.Bio.PKPD

/-!
## One-compartment IV-bolus AUC

For a one-compartment model with IV bolus dose `D`, volume of distribution `V_d`,
and elimination rate constant `k_e`, the plasma concentration at time `t ≥ 0` is

    C(t) = (D/V_d) · exp(-k_e · t).

The total AUC from 0 to ∞ equals `D/(V_d · k_e)`.
-/

/-- **One-compartment IV-bolus AUC.**
The area under the curve for an IV-bolus one-compartment model equals `D/(V_d · k_e)`.
The proof uses `integral_exp_mul_Ioi` with `a = -k_e < 0` evaluated at `c = 0`,
then simplifies the resulting expression by `field_simp` and `ring`. -/
@[stat_lemma]
theorem one_compartment_auc (D V_d k_e : ℝ) (hD : 0 < D) (hV : 0 < V_d) (hk : 0 < k_e) :
    ∫ t : ℝ in Set.Ioi 0, (D / V_d) * Real.exp (-(k_e * t)) = D / (V_d * k_e) := by
  have hrw : ∀ t : ℝ, (D / V_d) * Real.exp (-(k_e * t)) = (D / V_d) * Real.exp (-k_e * t) := by
    intro t; ring_nf
  simp_rw [hrw, integral_const_mul]
  have key : ∫ t : ℝ in Set.Ioi 0, Real.exp (-k_e * t) = 1 / k_e := by
    have h := integral_exp_mul_Ioi (a := -k_e) (by linarith) (0 : ℝ)
    simp only [mul_zero, Real.exp_zero] at h
    rw [h]; field_simp
  rw [key]
  field_simp

/-!
## Half-life and clearance relation

The half-life `t_{1/2} = ln(2)/k_e` is defined so that concentration drops by half:
`C_0 · exp(-k_e · t_{1/2}) = C_0 / 2`.
-/

/-- The half-life of a first-order elimination process with rate constant `k_e`. -/
noncomputable def halfLife (k_e : ℝ) : ℝ := Real.log 2 / k_e

/-- **Half-life and clearance relation.**
At time `t_{1/2} = ln(2)/k_e`, the plasma concentration is exactly half the initial value. -/
@[stat_lemma]
theorem half_life_clearance_relation (C0 k_e : ℝ) (hC : 0 < C0) (hk : 0 < k_e) :
    C0 * Real.exp (-(k_e * halfLife k_e)) = C0 / 2 := by
  unfold halfLife
  rw [show k_e * (Real.log 2 / k_e) = Real.log 2 from by field_simp]
  rw [Real.exp_neg, Real.exp_log two_pos]
  ring

end Pythia.Bio.PKPD
