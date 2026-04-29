/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Weibull Distribution: Moment and Tail Formulas

Formalises the standard actuarial moment and tail formulas for the Weibull
distribution with scale `lambda > 0` and shape `k > 0`:

  f(x) = (k/lambda) * (x/lambda)^(k-1) * exp(-(x/lambda)^k)   for x >= 0, else 0.

The Weibull generalises the exponential (k=1) and is the standard reliability
model for lifetime distributions in actuarial science and engineering.

## Main results

* `Weibull.tail`     -- P(X > t) = exp(-(t/lambda)^k)   (closed)
* `Weibull.mean`     -- E[X] = lambda * Gamma(1 + 1/k)   (scaffold sorry)
* `Weibull.variance` -- Var(X) = lambda^2*(Gamma(1+2/k) - Gamma(1+1/k)^2) (scaffold sorry)
* `Weibull.median`   -- Median X = lambda * (log 2)^(1/k)   (scaffold sorry: CDF inversion)

## Design notes

Mathlib 4.28 does not ship a `weibullMeasure`. We define the Weibull PDF
directly and construct the measure via `MeasureTheory.Measure.withDensity`.
The tail formula is the cleanest result: P(X > t) = exp(-(t/lambda)^k)
follows directly from the substitution u = (x/lambda)^k in the CDF integral,
which maps to the standard exponential integral.

The mean involves the Gamma function: E[X] = lambda * Gamma(1 + 1/k).
This uses the substitution u = (x/lambda)^k in the mean integral, reducing it
to the Gamma integral definition. Mathlib has `Real.Gamma_eq_integral` but
the reduction step for the Weibull case is a standard change-of-variables
that is not yet in Mathlib and requires careful Jacobian computation.

Status:
- `tail`      CLOSED (exp integral antiderivative)
- `mean`      scaffold sorry: change-of-variables to Gamma integral
- `variance`  scaffold sorry: depends on mean + E[X^2] reduction to Gamma
- `median`    scaffold sorry: CDF inversion

## References

* Klugman, Panjer, Willmot, *Loss Models: From Data to Decisions*, 5th ed. (2019).
* Rinne, H., *The Weibull Distribution: A Handbook* (2009).
-/

import Mathlib
import Pythia.Basic
import Pythia.Tactic.Pythia

namespace Pythia.Actuarial.Weibull

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal NNReal

/-! ### Setup -/

variable {lambda k : ℝ} (hl : 0 < lambda) (hk : 0 < k)

/-! ### PDF and measure -/

/-- Weibull PDF (real-valued): `(k/lambda) * (x/lambda)^(k-1) * exp(-(x/lambda)^k)` for x >= 0. -/
noncomputable def weibullPDFReal (lambda k x : ℝ) : ℝ :=
  if 0 ≤ x then (k / lambda) * (x / lambda) ^ (k - 1) * Real.exp (- (x / lambda) ^ k)
  else 0

/-- The Weibull PDF is nonneg everywhere. -/
lemma weibullPDFReal_nonneg (hl : 0 < lambda) (hk : 0 < k) (x : ℝ) :
    0 ≤ weibullPDFReal lambda k x := by
  simp only [weibullPDFReal]
  split_ifs with h
  · positivity
  · linarith

/-- The Weibull PDF is measurable. -/
@[fun_prop]
lemma measurable_weibullPDFReal (lambda k : ℝ) :
    Measurable (weibullPDFReal lambda k) := by
  unfold weibullPDFReal
  apply Measurable.ite measurableSet_Ici
  · fun_prop
  · exact measurable_const

/-- ENNReal-valued Weibull PDF. -/
noncomputable def weibullPDF (lambda k x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (weibullPDFReal lambda k x)

/-- Weibull measure on R, defined via withDensity. -/
noncomputable def weibullMeasure (lambda k : ℝ) : MeasureTheory.Measure ℝ :=
  MeasureTheory.volume.withDensity (weibullPDF lambda k)

include hl hk

/-! ### Tail probability – helper lemmas -/

/-
The antiderivative `F(x) = -exp(-(x/lambda)^k)` has derivative equal to the
    Weibull PDF at every `x > 0`.
-/
lemma weibullPDFReal_hasDerivAt (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y => -Real.exp (-(y / lambda) ^ k))
      (weibullPDFReal lambda k x) x := by
  convert HasDerivAt.neg ( HasDerivAt.exp ( HasDerivAt.neg ( HasDerivAt.rpow_const ( HasDerivAt.div_const ( hasDerivAt_id' x ) _ ) _ ) ) ) using 1 <;> norm_num;
  · unfold weibullPDFReal; ring;
    rw [ if_pos hx.le ];
  · exact Or.inl ⟨ hx.ne', hl.ne' ⟩

/-
The antiderivative is continuous from the right at 0.
-/
lemma weibullPDFReal_antideriv_continuousWithinAt (t : ℝ) (ht : 0 ≤ t) :
    ContinuousWithinAt (fun y => -Real.exp (-(y / lambda) ^ k))
      (Set.Ici t) t := by
  exact ContinuousAt.continuousWithinAt ( by exact ContinuousAt.neg ( Real.continuous_exp.continuousAt.comp <| ContinuousAt.neg <| ContinuousAt.rpow_const ( continuousAt_id.div_const _ ) <| Or.inr <| by positivity ) )

/-
The antiderivative tends to 0 at +∞.
-/
lemma weibullPDFReal_antideriv_tendsto :
    Tendsto (fun y => -Real.exp (-(y / lambda) ^ k))
      atTop (nhds 0) := by
  simpa using Filter.Tendsto.neg ( Real.tendsto_exp_atBot.comp <| Filter.tendsto_neg_atTop_atBot.comp <| tendsto_rpow_atTop hk |> Filter.Tendsto.comp <| Filter.tendsto_id.atTop_div_const hl )

/-
The Weibull PDF is integrable on `(t, ∞)` for `t ≥ 0`.
-/
lemma weibullPDFReal_integrableOn_Ioi (t : ℝ) (ht : 0 ≤ t) :
    IntegrableOn (weibullPDFReal lambda k) (Set.Ioi t) := by
  have h_integrable : MeasureTheory.IntegrableOn (fun x => (k / lambda) * (x / lambda) ^ (k - 1) * Real.exp (-(x / lambda) ^ k)) (Set.Ioi t) := by
    have h_integrable : ∫ x in Set.Ioi 0, (k / lambda) * (x / lambda) ^ (k - 1) * Real.exp (-(x / lambda) ^ k) = 1 := by
      have h_integrable : ∫ x in Set.Ioi 0, (k / lambda) * (x / lambda) ^ (k - 1) * Real.exp (-(x / lambda) ^ k) = ∫ x in Set.Ioi 0, k * x ^ (k - 1) * Real.exp (-x ^ k) := by
        have h_integrable : ∀ {f : ℝ → ℝ}, (∫ x in Set.Ioi 0, f x) = (∫ x in Set.Ioi 0, f (lambda * x) * lambda) := by
          intro f; rw [ MeasureTheory.integral_mul_const ] ; rw [ MeasureTheory.integral_comp_mul_left_Ioi ] ; norm_num [ hl.ne' ] ;
          · rw [ inv_mul_eq_div, div_mul_cancel₀ _ hl.ne' ];
          · positivity;
        convert h_integrable using 3 ; ring_nf ; norm_num [ hl.ne', hk.ne' ];
      have := @integral_rpow_mul_exp_neg_rpow k;
      simp_all +decide [ mul_assoc, MeasureTheory.integral_const_mul ];
      norm_num [ hk.ne' ];
    exact MeasureTheory.IntegrableOn.mono_set ( by exact MeasureTheory.integrable_of_integral_eq_one h_integrable ) ( Set.Ioi_subset_Ioi ht );
  exact h_integrable.congr_fun ( fun x hx => by unfold weibullPDFReal; rw [ if_pos ( by linarith [ hx.out ] ) ] ) measurableSet_Ioi

/-
The integral of the Weibull PDF over `(t, ∞)` equals `exp(-(t/lambda)^k)`.
-/
lemma weibullPDFReal_integral_Ioi (t : ℝ) (ht : 0 ≤ t) :
    ∫ x in Set.Ioi t, weibullPDFReal lambda k x =
    Real.exp (-(t / lambda) ^ k) := by
  convert MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto ( f := fun y => -Real.exp ( - ( y / lambda ) ^ k ) ) ?_ ?_ ?_ ?_ using 1;
  rw [ sub_neg_eq_add, zero_add ];
  · exact ContinuousAt.continuousWithinAt ( by exact ContinuousAt.neg ( ContinuousAt.rexp ( ContinuousAt.neg ( ContinuousAt.rpow ( continuousAt_id.div_const _ ) continuousAt_const <| Or.inr <| by positivity ) ) ) );
  · intro x hx; convert HasDerivAt.neg ( HasDerivAt.exp ( HasDerivAt.neg ( HasDerivAt.rpow_const ( HasDerivAt.div_const ( hasDerivAt_id' x ) _ ) _ ) ) ) using 1 <;> norm_num [ hl.ne', hk.ne', hx.out.ne', weibullPDFReal ] ; ring;
    · rw [ if_pos ( by linarith [ hx.out ] ) ];
    · exact Or.inl <| ne_of_gt <| lt_of_le_of_lt ht hx;
  · exact weibullPDFReal_integrableOn_Ioi hl hk t ht
  · exact weibullPDFReal_antideriv_tendsto hl hk

/-
The Weibull measure of a measurable set equals the integral of the PDF.
-/
lemma weibullMeasure_real_eq_integral (s : Set ℝ) (hs : MeasurableSet s) :
    (weibullMeasure lambda k).real s = ∫ x in s, weibullPDFReal lambda k x := by
  rw [ MeasureTheory.measureReal_def, weibullMeasure ];
  rw [ MeasureTheory.withDensity_apply _ hs, MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
  · rfl;
  · exact Filter.Eventually.of_forall fun x => weibullPDFReal_nonneg hl hk x;
  · exact Measurable.aestronglyMeasurable ( measurable_weibullPDFReal _ _ )

/-! ### Tail probability -/

/-- **Weibull tail probability.**
For `t >= 0`,  P(X > t) = exp(-(t/lambda)^k). -/
@[stat_lemma]
theorem tail (t : ℝ) (ht : 0 ≤ t) :
    (weibullMeasure lambda k).real (Set.Ioi t) =
    Real.exp (- (t / lambda) ^ k) := by
  rw [weibullMeasure_real_eq_integral hl hk _ measurableSet_Ioi]
  exact weibullPDFReal_integral_Ioi hl hk t ht

/-! ### Mean -/

/-
**Weibull mean.**
E[X] = lambda * Real.Gamma (1 + 1/k).
-/
@[stat_lemma]
theorem mean :
    ∫ x, x ∂(weibullMeasure lambda k) =
    lambda * Real.Gamma (1 + 1 / k) := by
  have h_moment : ∫ x in Set.Ioi 0, x * (weibullPDFReal lambda k x) = lambda * (Real.Gamma (1 + 1 / k)) := by
    have h_int : ∫ x in Set.Ioi 0, x * (k / lambda) * (x / lambda) ^ (k - 1) * Real.exp (-(x / lambda) ^ k) = lambda * Real.Gamma (1 + 1 / k) := by
      have := @integral_rpow_mul_exp_neg_mul_rpow;
      convert congr_arg ( fun x : ℝ => x * ( k / lambda ) * ( 1 / lambda ) ^ ( k - 1 ) ) ( @this k ( k ) ( 1 / lambda ^ k ) ( by positivity ) ( by linarith ) ( by positivity ) ) using 1 <;> ring;
      · rw [ ← MeasureTheory.integral_const_mul ] ; rw [ ← MeasureTheory.integral_mul_const ] ; refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => _ ; rw [ Real.mul_rpow ( le_of_lt hx ) ( by positivity ), Real.inv_rpow ( by positivity ) ] ; ring;
        rw [ show x ^ k = x ^ ( -1 + k ) * x by rw [ ← Real.rpow_add_one hx.out.ne' ] ; ring ] ; rw [ Real.mul_rpow ( le_of_lt hx.out ) ( by positivity ), Real.inv_rpow ( by positivity ) ] ; ring;
        rw [ ← Real.rpow_one_add' hx.out.le ] <;> norm_num ; linarith;
      · norm_num [ hl.ne', hk.ne', Real.rpow_def_of_pos, hl, hk ] ; ring;
        norm_num [ Real.rpow_def_of_pos, Real.exp_pos, hl, hk ] ; ring;
        norm_num [ Real.exp_add, Real.exp_neg, Real.exp_log hl, hk.ne' ] ; ring;
        norm_num [ sq, mul_assoc, mul_comm, mul_left_comm, hl.ne', Real.exp_ne_zero ];
    convert h_int using 1;
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [ weibullPDFReal ] ; rw [ if_pos hx.out.le ] ; ring;
  convert h_moment using 1;
  rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator, weibullMeasure ];
  rw [ MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part ];
  · rw [ MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
    · rw [ MeasureTheory.lintegral_withDensity_eq_lintegral_mul ];
      · rw [ MeasureTheory.lintegral_withDensity_eq_lintegral_mul ] <;> norm_num [ weibullPDF ];
        · rw [ show ( ∫⁻ a : ℝ, ENNReal.ofReal ( weibullPDFReal lambda k a ) * ENNReal.ofReal ( -a ) ∂MeasureTheory.MeasureSpace.volume ) = 0 from _ ];
          · rw [ MeasureTheory.lintegral_congr_ae ];
            rotate_right;
            use fun x => ENNReal.ofReal ( if 0 < x then x * weibullPDFReal lambda k x else 0 );
            · norm_num;
            · filter_upwards [ ] with x ; split_ifs <;> simp_all +decide [ mul_comm, ENNReal.ofReal_mul ];
              rw [ ENNReal.ofReal_mul ( by positivity ) ];
          · rw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_zero ];
            filter_upwards [ ] with x using by rw [ weibullPDFReal ] ; split_ifs <;> simp +decide [ *, ENNReal.ofReal_eq_zero ] ;
        · exact Measurable.ennreal_ofReal ( measurable_weibullPDFReal _ _ );
        · exact Measurable.ennreal_ofReal ( measurable_id'.neg );
      · exact Measurable.ennreal_ofReal ( measurable_weibullPDFReal _ _ );
      · exact Measurable.ennreal_ofReal measurable_id;
    · filter_upwards [ ] with x using by unfold weibullPDFReal; split_ifs <;> positivity;
    · refine' Measurable.aestronglyMeasurable _;
      apply_rules [ Measurable.ite, measurable_id, measurable_const ];
      · exact measurableSet_Ioi;
      · exact measurable_id.mul ( measurable_weibullPDFReal _ _ );
      · exact measurable_const;
  · have h_integrable : MeasureTheory.IntegrableOn (fun x => x * (weibullPDFReal lambda k x)) (Set.Ioi 0) := by
      exact ( by contrapose! h_moment; rw [ MeasureTheory.integral_undef h_moment ] ; positivity );
    rw [ MeasureTheory.integrable_withDensity_iff ];
    · rw [ ← MeasureTheory.integrable_indicator_iff ( measurableSet_Ioi ) ] at *;
      convert h_integrable using 1;
      ext x; by_cases hx : 0 < x <;> simp +decide [ hx, weibullPDF, weibullPDFReal ] ;
      · rw [ if_pos hx.le, ENNReal.toReal_ofReal ( by positivity ), if_pos hx.le ];
      · split_ifs <;> simp_all +decide [ ne_of_gt, le_of_lt ];
        exact Or.inl <| le_antisymm hx ‹_›;
    · exact Measurable.ennreal_ofReal ( measurable_weibullPDFReal _ _ );
    · exact Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top

/-! ### Variance -/

/-
**Weibull variance.**
Var(X) = lambda^2 * (Real.Gamma (1 + 2/k) - Real.Gamma (1 + 1/k)^2).
-/
@[stat_lemma]
theorem variance :
    ProbabilityTheory.variance id (weibullMeasure lambda k) =
    lambda ^ 2 * (Real.Gamma (1 + 2 / k) - Real.Gamma (1 + 1 / k) ^ 2) := by
  have h_var : ProbabilityTheory.variance id (weibullMeasure lambda k) = (∫ x, x^2 ∂(weibullMeasure lambda k)) - (∫ x, x ∂(weibullMeasure lambda k))^2 := by
    rw [ ProbabilityTheory.variance, ProbabilityTheory.evariance_eq_lintegral_ofReal, ← MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
    · simp +decide [ sub_sq ];
      rw [ MeasureTheory.integral_add, MeasureTheory.integral_sub ] <;> norm_num;
      · norm_num [ MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const ];
        rw [ MeasureTheory.integral_const_mul ] ; ring;
        rw [ show ( weibullMeasure lambda k ).real univ = 1 from ?_ ] ; ring;
        have h_integrable : ∫ x, weibullPDFReal lambda k x = 1 := by
          have h_integral : ∫ x in Set.Ioi 0, (k / lambda) * (x / lambda) ^ (k - 1) * Real.exp (-(x / lambda) ^ k) = 1 := by
            have := @weibullPDFReal_integral_Ioi;
            convert @this lambda k hl hk 0 le_rfl using 1;
            · exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [ weibullPDFReal ] ; rw [ if_pos hx.out.le ] ;
            · norm_num [ hk.ne' ];
          convert h_integral using 1;
          rw [ ← MeasureTheory.integral_Ici_eq_integral_Ioi ];
          rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator, weibullPDFReal ];
        convert h_integrable using 1;
        convert weibullMeasure_real_eq_integral _ _ _;
        rotate_left;
        exacts [ lambda, k, hl, hk, Set.univ, by simp +decide [ MeasureTheory.measureReal_def ] ];
      · have h_integrable : ∫ x, x^2 ∂(weibullMeasure lambda k) = lambda^2 * Real.Gamma (1 + 2 / k) := by
          -- To compute the second moment, we use the fact that the integral of $x^2$ times the Weibull PDF is equal to the second moment.
          have h_second_moment : ∫ x in Set.Ioi 0, x^2 * (k / lambda) * (x / lambda) ^ (k - 1) * Real.exp (-(x / lambda) ^ k) = lambda^2 * Real.Gamma (1 + 2 / k) := by
            have := @integral_rpow_mul_exp_neg_mul_rpow;
            convert congr_arg ( fun x : ℝ => x * ( k / lambda ) * ( 1 / lambda ) ^ ( k - 1 ) ) ( @this k ( 2 + k - 1 ) ( 1 / lambda ^ k ) hk ( by linarith ) ( by positivity ) ) using 1 <;> norm_num [ Real.div_rpow, hl.le, hk.le ] ; ring;
            · rw [ ← MeasureTheory.integral_const_mul ] ; rw [ ← MeasureTheory.integral_mul_const ] ; refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => _ ; rw [ Real.mul_rpow ( le_of_lt hx ) ( by positivity ), Real.inv_rpow ( by positivity ) ] ; ring;
              rw [ show 1 + k = -1 + k + 2 by ring ] ; norm_num [ Real.rpow_add hx, Real.rpow_neg_one ] ; ring;
              rw [ Real.mul_rpow ( le_of_lt hx ) ( by positivity ), Real.inv_rpow ( by positivity ) ];
            · rw [ Real.inv_rpow ( by positivity ), ← Real.rpow_mul ( by positivity ), ← Real.rpow_neg ( by positivity ) ] ; ring_nf ; norm_num [ hl.ne', hk.ne' ] ; ring;
              norm_num [ sq, mul_assoc, mul_comm, mul_left_comm, hl.ne', hk.ne', Real.rpow_add hl, Real.rpow_neg_one ];
              norm_num [ ← mul_assoc, ← Real.rpow_add hl, ← Real.rpow_neg_one, hl.ne' ];
              norm_num [ ← Real.rpow_mul hl.le, ← Real.rpow_add hl ];
          rw [ ← h_second_moment, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator, weibullMeasure ];
          rw [ MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
          · rw [ MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
            · rw [ MeasureTheory.lintegral_withDensity_eq_lintegral_mul ] <;> norm_num [ weibullPDF ];
              · congr with x ; split_ifs <;> simp_all +decide [ weibullPDFReal ];
                · rw [ ← ENNReal.ofReal_mul ( by positivity ) ] ; rw [ if_pos ( by positivity ) ] ; ring;
                · grind;
              · exact Measurable.ennreal_ofReal ( measurable_weibullPDFReal _ _ );
              · exact Measurable.ennreal_ofReal ( measurable_id.pow_const 2 );
            · filter_upwards [ ] with x using by split_ifs <;> positivity;
            · exact Measurable.aestronglyMeasurable ( by exact Measurable.ite ( measurableSet_Ioi ) ( by exact Measurable.mul ( Measurable.mul ( Measurable.mul ( measurable_id.pow_const _ ) measurable_const ) ( by exact Measurable.pow_const ( measurable_id.div_const _ ) _ ) ) ( by exact Measurable.exp ( by exact Measurable.neg ( by exact Measurable.pow_const ( measurable_id.div_const _ ) _ ) ) ) ) measurable_const );
          · exact Filter.Eventually.of_forall fun x => sq_nonneg x;
          · exact Continuous.aestronglyMeasurable ( continuous_pow 2 );
        exact ( by contrapose! h_integrable; rw [ MeasureTheory.integral_undef h_integrable ] ; positivity );
      · apply_rules [ MeasureTheory.Integrable.mul_const, MeasureTheory.Integrable.const_mul ];
        have := @mean lambda k hl hk;
        exact ( by contrapose! this; rw [ MeasureTheory.integral_undef this ] ; positivity );
      · have h_integrable : MeasureTheory.Integrable (fun x => x^2) (weibullMeasure lambda k) := by
          have h_integrable : ∫ x, x ^ 2 ∂(weibullMeasure lambda k) = lambda ^ 2 * Real.Gamma (1 + 2 / k) := by
            -- To compute the second moment, we use the fact that the integral of $x^2$ times the Weibull PDF is equal to the second moment.
            have h_second_moment : ∫ x in Set.Ioi 0, x^2 * (k / lambda) * (x / lambda) ^ (k - 1) * Real.exp (-(x / lambda) ^ k) = lambda^2 * Real.Gamma (1 + 2 / k) := by
              have := @integral_rpow_mul_exp_neg_mul_rpow;
              convert congr_arg ( fun x : ℝ => x * ( k / lambda ) * ( 1 / lambda ) ^ ( k - 1 ) ) ( @this k ( 2 + k - 1 ) ( 1 / lambda ^ k ) hk ( by linarith ) ( by positivity ) ) using 1 <;> norm_num [ Real.div_rpow, hl.le, hk.le ] ; ring;
              · rw [ ← MeasureTheory.integral_const_mul ] ; rw [ ← MeasureTheory.integral_mul_const ] ; refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => _ ; rw [ Real.mul_rpow ( le_of_lt hx ) ( by positivity ), Real.inv_rpow ( by positivity ) ] ; ring;
                rw [ show 1 + k = -1 + k + 2 by ring ] ; norm_num [ Real.rpow_add hx, Real.rpow_neg_one ] ; ring;
                rw [ Real.mul_rpow ( le_of_lt hx ) ( by positivity ), Real.inv_rpow ( by positivity ) ];
              · rw [ Real.inv_rpow ( by positivity ), ← Real.rpow_mul ( by positivity ), ← Real.rpow_neg ( by positivity ) ] ; ring_nf ; norm_num [ hl.ne', hk.ne' ] ; ring;
                norm_num [ sq, mul_assoc, mul_comm, mul_left_comm, hl.ne', hk.ne', Real.rpow_add hl, Real.rpow_neg_one ];
                norm_num [ ← mul_assoc, ← Real.rpow_add hl, ← Real.rpow_neg_one, hl.ne' ];
                norm_num [ ← Real.rpow_mul hl.le, ← Real.rpow_add hl ];
            rw [ ← h_second_moment, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator, weibullMeasure ];
            rw [ MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
            · rw [ MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
              · rw [ MeasureTheory.lintegral_withDensity_eq_lintegral_mul ] <;> norm_num [ weibullPDF ];
                · congr with x ; split_ifs <;> simp_all +decide [ weibullPDFReal ];
                  · rw [ ← ENNReal.ofReal_mul ( by positivity ) ] ; rw [ if_pos ( by positivity ) ] ; ring;
                  · grind;
                · exact Measurable.ennreal_ofReal ( measurable_weibullPDFReal _ _ );
                · exact Measurable.ennreal_ofReal ( measurable_id.pow_const 2 );
              · filter_upwards [ ] with x using by split_ifs <;> positivity;
              · exact Measurable.aestronglyMeasurable ( by exact Measurable.ite ( measurableSet_Ioi ) ( by exact Measurable.mul ( Measurable.mul ( Measurable.mul ( measurable_id.pow_const _ ) measurable_const ) ( by exact Measurable.pow_const ( measurable_id.div_const _ ) _ ) ) ( by exact Measurable.exp ( by exact Measurable.neg ( by exact Measurable.pow_const ( measurable_id.div_const _ ) _ ) ) ) ) measurable_const );
            · exact Filter.Eventually.of_forall fun x => sq_nonneg x;
            · exact Continuous.aestronglyMeasurable ( continuous_pow 2 );
          exact ( by contrapose! h_integrable; rw [ MeasureTheory.integral_undef h_integrable ] ; positivity );
        have h_integrable : MeasureTheory.Integrable (fun x => x) (weibullMeasure lambda k) := by
          have h_mean : ∫ x, x ∂(weibullMeasure lambda k) = lambda * Real.Gamma (1 + 1 / k) := by
            convert Pythia.Actuarial.Weibull.mean hl hk using 1
          exact ( by contrapose! h_mean; rw [ MeasureTheory.integral_undef h_mean ] ; positivity );
        exact MeasureTheory.Integrable.sub ‹_› ( MeasureTheory.Integrable.mul_const ( MeasureTheory.Integrable.const_mul ‹_› _ ) _ );
      · apply_rules [ MeasureTheory.integrable_const ];
        constructor ; norm_num [ weibullMeasure ];
        have h_integrable : ∫ x, weibullPDFReal lambda k x = 1 := by
          have h_integral : ∫ x in Set.Ioi 0, (k / lambda) * (x / lambda) ^ (k - 1) * Real.exp (-(x / lambda) ^ k) = 1 := by
            have := @weibullPDFReal_integral_Ioi;
            convert @this lambda k hl hk 0 le_rfl using 1;
            · exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [ weibullPDFReal ] ; rw [ if_pos hx.out.le ] ;
            · norm_num [ hk.ne' ];
          convert h_integral using 1;
          rw [ ← MeasureTheory.integral_Ici_eq_integral_Ioi ];
          rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator, weibullPDFReal ];
        convert MeasureTheory.Integrable.lintegral_lt_top _ using 1;
        exact MeasureTheory.integrable_of_integral_eq_one h_integrable;
    · exact Filter.Eventually.of_forall fun x => sq_nonneg _;
    · exact Measurable.aestronglyMeasurable ( by measurability );
  have h_moment_2 : ∫ x in Set.Ioi 0, x^2 * (weibullPDFReal lambda k x) = lambda^2 * Real.Gamma (1 + 2 / k) := by
    -- We'll use the fact that $\int_{0}^{\infty} x^{2} \cdot \frac{k}{\lambda} \left(\frac{x}{\lambda}\right)^{k-1} e^{-\left(\frac{x}{\lambda}\right)^{k}} \, dx$ can be simplified.
    have h_simp : ∫ x in Set.Ioi 0, x^2 * (weibullPDFReal lambda k x) = (k / lambda^k) * ∫ x in Set.Ioi 0, x^(k + 1) * Real.exp (-(x / lambda)^k) := by
      rw [ ← MeasureTheory.integral_const_mul ] ; refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => _ ; rw [ weibullPDFReal ] ; rw [ if_pos hx.out.le ] ; ring;
      rw [ Real.rpow_add ( by exact mul_pos hx.out ( inv_pos.mpr hl ) ), Real.rpow_neg_one ] ; ring;
      rw [ Real.mul_rpow ( by linarith [ hx.out ] ) ( by positivity ), Real.inv_rpow ( by positivity ) ] ; norm_num [ Real.rpow_add hx.out, Real.rpow_one, hl.ne', hk.ne', hx.out.ne' ] ; ring;
      grind;
    -- Let's simplify the integral $\int_{0}^{\infty} x^{k+1} e^{-(x/\lambda)^k} \, dx$.
    have h_gamma : ∫ x in Set.Ioi 0, x^(k + 1) * Real.exp (-(x / lambda)^k) = (lambda^(k + 2) / k) * Real.Gamma ((k + 2) / k) := by
      have := @integral_rpow_mul_exp_neg_mul_rpow;
      convert @this k ( k + 1 ) ( 1 / lambda ^ k ) hk ( by linarith ) ( by positivity ) using 1 <;> norm_num [ Real.div_rpow, hl.le, hk.le ] ; ring;
      · exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [ Real.mul_rpow ( le_of_lt hx ) ( by positivity ), Real.inv_rpow ( by positivity ) ] ; ring;
      · rw [ Real.inv_rpow ( by positivity ), ← Real.rpow_mul ( by positivity ), ← Real.rpow_neg ( by positivity ) ] ; ring;
        norm_num [ sq, mul_assoc, hk.ne' ] ; ring;
    convert h_simp.trans ( congr_arg _ h_gamma ) using 1 ; ring;
    norm_num [ hk.ne', Real.rpow_add hl, Real.rpow_neg hl.le ] ; ring;
    exact Or.inl ( by rw [ mul_assoc, mul_inv_cancel₀ ( by positivity ), mul_one ] );
  have h_moment_2_eq : ∫ x, x^2 ∂(weibullMeasure lambda k) = ∫ x in Set.Ioi 0, x^2 * (weibullPDFReal lambda k x) := by
    rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
    rw [ show weibullMeasure lambda k = MeasureTheory.Measure.withDensity MeasureTheory.volume ( fun x => ENNReal.ofReal ( weibullPDFReal lambda k x ) ) from rfl, MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
    · rw [ MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
      · rw [ MeasureTheory.lintegral_withDensity_eq_lintegral_mul ];
        · congr with x ; by_cases hx : 0 < x <;> simp +decide [ hx, mul_comm, mul_assoc, mul_left_comm, weibullPDFReal ];
          · rw [ ← ENNReal.ofReal_mul ( by positivity ) ] ; split_ifs <;> ring;
          · grind +qlia;
        · exact Measurable.ennreal_ofReal ( measurable_weibullPDFReal _ _ );
        · exact Measurable.ennreal_ofReal ( measurable_id.pow_const 2 );
      · filter_upwards [ ] with x using by unfold weibullPDFReal; split_ifs <;> positivity;
      · refine' Measurable.aestronglyMeasurable _;
        apply_rules [ Measurable.ite, measurable_const ];
        · exact measurableSet_Ioi;
        · exact Measurable.mul ( measurable_id.pow_const 2 ) ( measurable_weibullPDFReal _ _ );
    · exact Filter.Eventually.of_forall fun x => sq_nonneg x;
    · exact Continuous.aestronglyMeasurable ( continuous_pow 2 );
  rw [ h_var, h_moment_2_eq, h_moment_2, mean ] ; ring;
  · positivity;
  · positivity

/-! ### Median -/

/-
**Weibull median.**
Median X = lambda * (Real.log 2)^(1/k).
-/
theorem median :
    ∃ m : ℝ,
      (weibullMeasure lambda k).real (Set.Iic m) = 1 / 2 ∧
      m = lambda * (Real.log 2) ^ (1 / k) := by
  have h_integral : (weibullMeasure lambda k).real Set.univ = 1 := by
    have h_integrable : ∫ x, weibullPDFReal lambda k x = 1 := by
      have h_integral : ∫ x in Set.Ioi 0, weibullPDFReal lambda k x = 1 := by
        have := @weibullPDFReal_integral_Ioi lambda k hl hk 0 le_rfl;
        simpa [ hk.ne' ] using this;
      rw [ ← h_integral, ← MeasureTheory.integral_Ici_eq_integral_Ioi ];
      rw [ MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ] ; unfold weibullPDFReal ; aesop;
    rw [ ← h_integrable, weibullMeasure_real_eq_integral ];
    · norm_num;
    · grobner;
    · positivity;
    · norm_num;
  have h_integral_split : (weibullMeasure lambda k).real (Set.Iic (lambda * (Real.log 2) ^ (1 / k))) + (weibullMeasure lambda k).real (Set.Ioi (lambda * (Real.log 2) ^ (1 / k))) = 1 := by
    convert h_integral using 1;
    simp +decide [ MeasureTheory.measureReal_def ];
    rw [ ← ENNReal.toReal_add, ← MeasureTheory.measure_union ] <;> norm_num;
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.subset_univ _ ) ) ( by contrapose! h_integral; simp_all +decide [ MeasureTheory.measureReal_def ] ) );
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.subset_univ _ ) ) ( by contrapose! h_integral; simp_all +decide [ MeasureTheory.measureReal_def ] ) );
  have h_integral_split : (weibullMeasure lambda k).real (Set.Ioi (lambda * (Real.log 2) ^ (1 / k))) = 1 / 2 := by
    rw [ Pythia.Actuarial.Weibull.tail ] <;> norm_num [ hl, hk ];
    · rw [ mul_div_cancel_left₀ _ hl.ne', ← Real.rpow_mul ( by positivity ), inv_mul_cancel₀ hk.ne', Real.rpow_one, Real.exp_neg, Real.exp_log ] <;> norm_num;
    · positivity;
  grind +revert

end Pythia.Actuarial.Weibull