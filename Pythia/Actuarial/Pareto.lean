/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pareto Distribution: Moment and Tail Formulas

Formalises the standard actuarial moment and tail formulas for the Type-I
Pareto distribution with scale `x_m > 0` and shape `alpha > 0`:

  f(x) = alpha * x_m^alpha / x^(alpha+1)   for x >= x_m, else 0.

## Main results

* `Pareto.tail`     -- survival function: P(X > t) = (x_m / t)^alpha
* `Pareto.mean`     -- E[X] = alpha * x_m / (alpha - 1)
* `Pareto.variance` -- Var(X) = alpha * x_m^2 / ((alpha-1)^2*(alpha-2))
* `Pareto.median`   -- Median X = x_m * 2^(1/alpha)

## References

* Klugman, Panjer, Willmot, *Loss Models: From Data to Decisions*, 5th ed. (2019).
* Mathlib: `Mathlib.Probability.Distributions.Pareto`
* Mathlib: `Mathlib.Analysis.SpecialFunctions.ImproperIntegrals`
-/

import Mathlib
import Pythia.Basic
import Pythia.Tactic.Pythia

namespace Pythia.Actuarial.Pareto

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal NNReal

/-! ### Setup -/

variable {x_m alpha : ℝ}

/-- The Pareto Type-I measure with scale `x_m` and shape `alpha`.
Re-exported from Mathlib's `paretoMeasure` for the actuarial namespace. -/
noncomputable def paretoMeasure : MeasureTheory.Measure ℝ :=
  ProbabilityTheory.paretoMeasure x_m alpha

/-- `paretoMeasure` is a probability measure when scale and shape are positive. -/
theorem isProbabilityMeasure_pareto (hm : 0 < x_m) (ha : 0 < alpha) :
    IsProbabilityMeasure (paretoMeasure (x_m := x_m) (alpha := alpha)) :=
  ProbabilityTheory.isProbabilityMeasure_paretoMeasure hm ha

/-! ### Helper lemmas for integration -/

/-
The integral of the Pareto PDF on `(t, ∞)` for `0 < x_m ≤ t`.
This is the core calculation: ∫ x in Ioi t, α · x_m^α · x^(-(α+1)) dx = (x_m/t)^α.
-/
private lemma pareto_integral_Ioi (hm : 0 < x_m) (ha : 0 < alpha) (t : ℝ) (ht : x_m ≤ t) :
    ∫ x in Ioi t, alpha * x_m ^ alpha * x ^ (-(alpha + 1)) =
    (x_m / t) ^ alpha := by
  rw [ MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt ];
  · rw [ Real.div_rpow ( by linarith ) ( by linarith ) ] ; ring;
    rw [ Real.rpow_neg ( by linarith ) ] ; norm_num [ mul_assoc, mul_comm alpha, ha.ne' ];
  · linarith;
  · linarith

/-
The CDF of the Pareto distribution: for `0 < x_m ≤ t`,
`cdf(t) = 1 − (x_m/t)^α`.
-/
private lemma pareto_cdf_eq (hm : 0 < x_m) (ha : 0 < alpha) (t : ℝ) (ht : x_m ≤ t) :
    (cdf (ProbabilityTheory.paretoMeasure x_m alpha)) t = 1 - (x_m / t) ^ alpha := by
  have h_cdf_integral : ∫ x in Iic t, (if x_m ≤ x then alpha * x_m ^ alpha * x ^ (-(alpha + 1)) else 0) = 1 - (x_m / t) ^ alpha := by
    have h_integral : ∫ x in Set.Icc x_m t, alpha * x_m ^ alpha * x ^ (-(alpha + 1)) = 1 - (x_m / t) ^ alpha := by
      rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht, intervalIntegral.integral_const_mul, integral_rpow ] <;> norm_num;
      · rw [ Real.div_rpow ( by positivity ) ( by linarith ) ] ; rw [ Real.rpow_neg ( by linarith ), Real.rpow_neg ( by linarith ) ] ; ring;
        -- Combine like terms and simplify the expression.
        field_simp
        ring;
      · exact Or.inr ⟨ ha.ne', Set.notMem_uIcc_of_lt hm ( by linarith ) ⟩;
    rw [ ← h_integral, ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
    grind;
  convert h_cdf_integral using 1;
  convert cdf_paretoMeasure_eq_integral hm ha t using 1

/-! ### Tail probability (survival function) -/

/-
**Pareto tail probability.**
For `t >= x_m`,  P(X > t) = (x_m / t)^alpha.
-/
@[stat_lemma]
theorem tail (hm : 0 < x_m) (ha : 0 < alpha) (t : ℝ) (ht : x_m ≤ t) :
    (paretoMeasure (x_m := x_m) (alpha := alpha)).real (Set.Ioi t) =
    (x_m / t) ^ alpha := by
  convert ( pareto_integral_Ioi hm ha t ht ) using 1;
  unfold paretoMeasure;
  rw [ MeasureTheory.measureReal_def, ProbabilityTheory.paretoMeasure ];
  rw [ MeasureTheory.withDensity_apply' ];
  rw [ MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
  · rw [ MeasureTheory.setLIntegral_congr_fun ];
    · norm_num;
    · intro x hx; simp +decide [ paretoPDF, hx.out.le ] ;
      rw [ paretoPDFReal ];
      rw [ if_pos ( by linarith [ hx.out ] ) ] ; ring;
  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with x hx using mul_nonneg ( mul_nonneg ha.le ( Real.rpow_nonneg hm.le _ ) ) ( Real.rpow_nonneg ( by linarith [ hx.out ] ) _ );
  · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( measurable_const ) ( measurable_id.pow_const _ ) )

/-
**Pareto tail probability (alternate signature).**
For `t ≥ x_m`, `P(X > t) = (x_m / t) ^ α`.

This is the same result as `tail` but stated directly in terms of
`ProbabilityTheory.paretoMeasure x_m α` (Mathlib convention: first arg = scale,
second arg = shape) with all parameters explicit.

Note: Mathlib's `paretoMeasure` takes `(scale, shape)`, so the correct call
for scale `x_m` and shape `α` is `paretoMeasure x_m α`, **not** `paretoMeasure α x_m`.
-/
theorem pareto_tail
    (α x_m : ℝ) (hα : 0 < α) (hxm : 0 < x_m)
    {t : ℝ} (ht : x_m ≤ t) :
    (ProbabilityTheory.paretoMeasure x_m α).real (Set.Ioi t) = (x_m / t) ^ α := by
  convert tail hxm hα t ht using 1

/-! ### Mean -/

/-
**Pareto mean.**
For `alpha > 1`,  E[X] = alpha * x_m / (alpha - 1).
-/
@[stat_lemma]
theorem mean (hm : 0 < x_m) (ha : 0 < alpha) (h1 : 1 < alpha) :
    ∫ x, x ∂(paretoMeasure (x_m := x_m) (alpha := alpha)) =
    alpha * x_m / (alpha - 1) := by
  unfold paretoMeasure;
  -- The integral of x over the Pareto distribution can be written as the integral of x times the PDF from x_m to infinity.
  have h_integral : ∫ x, x ∂(ProbabilityTheory.paretoMeasure x_m alpha) = ∫ x in Set.Ici x_m, x * (alpha * x_m ^ alpha * x ^ (-(alpha + 1))) := by
    rw [ ProbabilityTheory.paretoMeasure, MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
    · rw [ MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
      · rw [ MeasureTheory.lintegral_withDensity_eq_lintegral_mul ];
        · rw [ ← MeasureTheory.lintegral_indicator ] <;> norm_num [ Set.indicator ];
          congr with x ; rw [ paretoPDF ] ; split_ifs <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
          · rw [ ← ENNReal.ofReal_mul ( by linarith ) ] ; unfold paretoPDFReal ; ring;
            rw [ if_pos ‹_› ] ; ring;
          · exact Or.inr ( by rw [ paretoPDFReal ] ; split_ifs <;> norm_num ; linarith );
        · exact Measurable.ennreal_ofReal ( by exact Measurable.ite ( measurableSet_Ici ) ( by measurability ) measurable_const );
        · exact Measurable.ennreal_ofReal measurable_id;
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ici ] with x hx using mul_nonneg ( le_trans hm.le hx ) ( mul_nonneg ( mul_nonneg ha.le ( Real.rpow_nonneg hm.le _ ) ) ( Real.rpow_nonneg ( le_trans hm.le hx ) _ ) );
      · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul measurable_id ( by exact Measurable.mul ( measurable_const ) ( measurable_id.pow_const _ ) ) );
    · rw [ Filter.EventuallyLE, MeasureTheory.ae_withDensity_iff ];
      · simp +decide [ paretoPDF ];
        exact Filter.Eventually.of_forall fun x hx => le_of_not_gt fun hx' => hx.ne' <| by unfold paretoPDFReal; split_ifs <;> linarith;
      · exact Measurable.ennreal_ofReal ( by exact Measurable.ite ( measurableSet_Ici ) ( by measurability ) measurable_const );
    · exact measurable_id.aestronglyMeasurable;
  -- Simplify the integral expression.
  have h_simplify : ∫ x in Set.Ici x_m, x * (alpha * x_m ^ alpha * x ^ (-(alpha + 1))) = alpha * x_m ^ alpha * ∫ x in Set.Ici x_m, x ^ (-(alpha) : ℝ) := by
    rw [ ← MeasureTheory.integral_const_mul ] ; refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun x hx => _ ; rw [ show -alpha = - ( alpha + 1 ) + 1 by ring ] ; rw [ Real.rpow_add_one ( by linarith [ Set.mem_Ici.mp hx ] ) ] ; ring;
  rw [ h_integral, h_simplify, MeasureTheory.integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt ] <;> try linarith;
  rw [ Real.rpow_add hm, Real.rpow_one ] ; ring;
  norm_num [ mul_assoc, ← Real.rpow_add hm ];
  rw [ show ( -1 + alpha ) = - ( 1 - alpha ) by ring, inv_neg ] ; ring

/-! ### Variance -/

/-
**Pareto variance.**
For `alpha > 2`,  Var(X) = alpha * x_m^2 / ((alpha-1)^2 * (alpha-2)).
-/
@[stat_lemma]
theorem variance (hm : 0 < x_m) (ha : 0 < alpha) (h2 : 2 < alpha) :
    ProbabilityTheory.variance id (paretoMeasure (x_m := x_m) (alpha := alpha)) =
    alpha * x_m ^ 2 / ((alpha - 1) ^ 2 * (alpha - 2)) := by
  -- First, we need to compute the second moment of the Pareto distribution.
  have h_second_moment : ∫ x, (x - alpha * x_m / (alpha - 1))^2 ∂(ProbabilityTheory.paretoMeasure x_m alpha) = alpha * x_m^2 / ((alpha - 1)^2 * (alpha - 2)) := by
    have h_var : ∫ x in Set.Ici x_m, (x - alpha * x_m / (alpha - 1))^2 * (alpha * x_m^alpha * x^(-(alpha + 1))) = alpha * x_m^2 / ((alpha - 1)^2 * (alpha - 2)) := by
      -- Now use the provided solution to simplify the integral.
      have h_integral_simplified : ∫ x in Set.Ici x_m, (x - alpha * x_m / (alpha - 1))^2 * (alpha * x_m^alpha * x^(-(alpha + 1))) = alpha * x_m^alpha * (∫ x in Set.Ici x_m, x^(1 - alpha) - 2 * alpha * x_m / (alpha - 1) * x^(-alpha) + (alpha * x_m / (alpha - 1))^2 * x^(-(alpha + 1))) := by
        rw [ ← MeasureTheory.integral_const_mul ] ; refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun x hx => _ ; ring;
        rw [ show 1 - alpha = -1 - alpha + 2 by ring ] ; rw [ Real.rpow_add ( by linarith [ Set.mem_Ici.mp hx ] ) ] ; norm_num ; ring;
        rw [ show -alpha = -1 - alpha + 1 by ring, Real.rpow_add_one ( by linarith [ Set.mem_Ici.mp hx ] ) ] ; ring;
      rw [ h_integral_simplified, MeasureTheory.integral_add, MeasureTheory.integral_sub ];
      · rw [ MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, MeasureTheory.integral_Ici_eq_integral_Ioi, MeasureTheory.integral_Ici_eq_integral_Ioi, MeasureTheory.integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt, integral_Ioi_rpow_of_lt, integral_Ioi_rpow_of_lt ] <;> norm_num;
        any_goals linarith;
        rw [ show 1 - alpha + 1 = -alpha + 2 by ring, show -alpha + 1 = -alpha + 1 by ring, show -alpha = -alpha by ring ] ; norm_num [ Real.rpow_add hm, Real.rpow_neg hm.le ] ; ring;
        field_simp;
        rw [ neg_add_eq_sub, div_sub_div, div_add_div, div_eq_div_iff ] <;> nlinarith [ pow_pos ( sub_pos.mpr h2 ) 3 ];
      · have h_integrable : MeasureTheory.IntegrableOn (fun x => x ^ (1 - alpha)) (Set.Ioi x_m) := by
          rw [ integrableOn_Ioi_rpow_iff ] <;> linarith;
        simpa only [ MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici ] using h_integrable;
      · have h_integrable : MeasureTheory.IntegrableOn (fun x => x ^ (-alpha)) (Set.Ioi x_m) := by
          rw [ integrableOn_Ioi_rpow_iff ] <;> linarith;
        simpa only [ MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici ] using h_integrable.const_mul _;
      · refine' MeasureTheory.Integrable.sub _ _;
        · have h_integrable : MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (1 - alpha)) (Set.Ioi x_m) := by
            rw [ integrableOn_Ioi_rpow_iff ] <;> linarith;
          simpa only [ MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici ] using h_integrable;
        · have h_integrable : MeasureTheory.IntegrableOn (fun x => x ^ (-alpha)) (Set.Ici x_m) := by
            rw [ integrableOn_Ici_iff_integrableOn_Ioi ];
            rw [ integrableOn_Ioi_rpow_iff ] <;> linarith;
          exact h_integrable.const_mul _;
      · have h_integrable : MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-(alpha + 1))) (Set.Ici x_m) := by
          rw [ integrableOn_Ici_iff_integrableOn_Ioi ];
          rw [ integrableOn_Ioi_rpow_iff ] <;> linarith;
        exact h_integrable.const_mul _;
    convert h_var using 1;
    rw [ ProbabilityTheory.paretoMeasure ];
    rw [ MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
    · rw [ MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
      · rw [ MeasureTheory.lintegral_withDensity_eq_lintegral_mul ];
        · rw [ ← MeasureTheory.lintegral_indicator ] <;> norm_num [ Set.indicator, paretoPDF ];
          congr with x ; by_cases hx : x_m ≤ x <;> simp +decide [ hx, paretoPDFReal ];
          rw [ ← ENNReal.ofReal_mul ( by exact mul_nonneg ( mul_nonneg ha.le ( Real.rpow_nonneg hm.le _ ) ) ( Real.rpow_nonneg ( by linarith ) _ ) ), mul_comm ];
        · exact Measurable.ennreal_ofReal ( by exact Measurable.ite ( measurableSet_Ici ) ( by exact Measurable.mul ( by exact measurable_const ) ( by exact measurable_id.pow_const _ ) ) measurable_const );
        · exact Measurable.ennreal_ofReal ( by exact Measurable.pow_const ( measurable_id.sub measurable_const ) _ );
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ici ] with x hx using mul_nonneg ( sq_nonneg _ ) ( mul_nonneg ( mul_nonneg ha.le ( Real.rpow_nonneg hm.le _ ) ) ( Real.rpow_nonneg ( by linarith [ Set.mem_Ici.mp hx ] ) _ ) );
      · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( by exact Measurable.pow_const ( measurable_id.sub measurable_const ) _ ) ( by exact Measurable.mul ( measurable_const ) ( by exact measurable_id.pow_const _ ) ) );
    · exact Filter.Eventually.of_forall fun x => sq_nonneg _;
    · exact Continuous.aestronglyMeasurable ( by continuity );
  rw [ ← h_second_moment, ProbabilityTheory.variance, ProbabilityTheory.evariance_eq_lintegral_ofReal, ← MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
  · have := @mean x_m alpha hm ha ( by linarith ) ; aesop;
  · exact Filter.Eventually.of_forall fun x => sq_nonneg _;
  · exact Measurable.aestronglyMeasurable ( by measurability )

/-! ### Median -/

/-
**Pareto median.**
There exists m = x_m * 2^(1/alpha) such that CDF(m) = 1/2.
-/
theorem median (hm : 0 < x_m) (ha : 0 < alpha) :
    ∃ m : ℝ,
      (paretoMeasure (x_m := x_m) (alpha := alpha)).real (Set.Iic m) = 1 / 2 ∧
      m = x_m * (2 : ℝ) ^ (1 / alpha) := by
  refine' ⟨ _, _, rfl ⟩;
  have h_cdf : cdf (paretoMeasure (x_m := x_m) (alpha := alpha)) (x_m * 2 ^ (1 / alpha)) = 1 - (x_m / (x_m * 2 ^ (1 / alpha))) ^ alpha := by
    convert pareto_cdf_eq hm ha ( x_m * 2 ^ ( 1 / alpha ) ) ( by nlinarith [ Real.one_le_rpow ( by norm_num : ( 1 : ℝ ) ≤ 2 ) ( by positivity : 0 ≤ 1 / alpha ) ] ) using 1;
  convert h_cdf using 1 ; norm_num [ hm.ne', ha.ne' ];
  · convert ( MeasureTheory.measureReal_def _ _ ) |> Eq.symm using 1;
    convert ( ProbabilityTheory.cdf_eq_real _ _ ) using 1;
    exact?;
  · norm_num [ ← div_div, hm.ne', ha.ne' ];
    rw [ Real.inv_rpow ( by positivity ), ← Real.rpow_mul ( by positivity ), inv_mul_cancel₀ ( by positivity ), Real.rpow_one ] ; norm_num

end Pythia.Actuarial.Pareto