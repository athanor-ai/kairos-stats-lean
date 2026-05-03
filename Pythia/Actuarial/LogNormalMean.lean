/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Log-Normal Mean via the Gaussian MGF

Proves the closed-form mean of the log-normal distribution:
  E[X] = exp(μ + v/2)  where X ~ LogNormal(μ, v).

The log-normal measure is defined as the pushforward of `gaussianReal μ v`
under `Real.exp`.
-/

import Mathlib

namespace Pythia.Actuarial.LogNormal

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal NNReal

/-! ### Definition -/

/-- The log-normal measure with parameters `μ` (log-mean) and `v` (log-variance),
defined as the pushforward of the Gaussian measure `gaussianReal μ v` under `exp`. -/
noncomputable def logNormalMeasureV (μ : ℝ) (v : NNReal) : Measure ℝ :=
  (gaussianReal μ v).map Real.exp

/-! ### Key algebraic identity: completion of the square -/

/-
Algebraic identity: `gaussianPDFReal μ v x * exp x = exp(μ + v/2) * gaussianPDFReal (μ + v) v x`.
This is the core "completing the square" step for the Gaussian MGF.
-/
lemma gaussianPDFReal_mul_exp (μ : ℝ) {v : NNReal} (hv : v ≠ 0) (x : ℝ) :
    gaussianPDFReal μ v x * Real.exp x =
    Real.exp (μ + (v : ℝ) / 2) * gaussianPDFReal (μ + (v : ℝ)) v x := by
  unfold gaussianPDFReal;
  -- Simplifying the exponents using properties of exponents.
  have h_exp : -(x - μ) ^ 2 / (2 * v) + x = μ + v / 2 + -(x - (μ + v)) ^ 2 / (2 * v) := by
    -- Combine like terms and simplify the expression.
    field_simp
    ring;
  rw [ mul_assoc, ← Real.exp_add, h_exp ] ; ring;
  simpa only [ mul_assoc, ← Real.exp_add ] using by ring;

/-! ### Integrability -/

/-
`exp` is integrable with respect to the Gaussian measure.
-/
lemma integrable_exp_gaussianReal (μ : ℝ) {v : NNReal} (hv : v ≠ 0) :
    Integrable (fun x => Real.exp x) (gaussianReal μ v) := by
  have h_integrable : MeasureTheory.Integrable (fun x => (gaussianPDFReal μ v x) * Real.exp x) MeasureTheory.volume := by
    rw [ show ( fun x => gaussianPDFReal μ v x * Real.exp x ) = fun x => Real.exp ( μ + ( v : ℝ ) / 2 ) * gaussianPDFReal ( μ + ( v : ℝ ) ) v x from funext fun x => gaussianPDFReal_mul_exp μ hv x ];
    fun_prop;
  rw [ gaussianReal_of_var_ne_zero ];
  · rw [ MeasureTheory.integrable_withDensity_iff ];
    · convert h_integrable using 1;
      ext; simp +decide [ gaussianPDFReal, mul_comm ];
    · fun_prop;
    · simp [gaussianPDF];
  · assumption

/-! ### Gaussian MGF at t=1 -/

/-- The Gaussian MGF evaluated at t=1:
  `∫ exp(x) d(gaussianReal μ v) = exp(μ + v/2)`. -/
theorem gaussianReal_mgf_one (μ : ℝ) {v : NNReal} (hv : v ≠ 0) :
    ∫ x, Real.exp x ∂(gaussianReal μ v) = Real.exp (μ + (v : ℝ) / 2) := by
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  have : (fun x => gaussianPDFReal μ v x * rexp x) =
         (fun x => rexp (μ + (v : ℝ) / 2) * gaussianPDFReal (μ + (v : ℝ)) v x) :=
    funext (gaussianPDFReal_mul_exp μ hv)
  rw [this, integral_const_mul, integral_gaussianPDFReal_eq_one (μ + (v : ℝ)) hv, mul_one]

/-! ### Main theorem -/

/-- **Log-normal mean.** If `X ~ LogNormal(μ, v)`, then `E[X] = exp(μ + v/2)`. -/
theorem logNormal_mean (μ : ℝ) (v : NNReal) :
    ∫ x, x ∂(logNormalMeasureV μ v) = Real.exp (μ + (v : ℝ) / 2) := by
  unfold logNormalMeasureV
  by_cases hv : v = 0
  · subst hv
    simp [gaussianReal_zero_var, Measure.map_dirac Real.measurable_exp, integral_dirac]
  · have h_aem : AEMeasurable Real.exp (gaussianReal μ v) :=
      Real.measurable_exp.aemeasurable
    have h_asm : AEStronglyMeasurable id (Measure.map Real.exp (gaussianReal μ v)) := by
      exact aestronglyMeasurable_id
    rw [show (fun x => x) = (id : ℝ → ℝ) from rfl,
        integral_map h_aem h_asm]
    simp only [id_eq]
    exact gaussianReal_mgf_one μ hv

end Pythia.Actuarial.LogNormal