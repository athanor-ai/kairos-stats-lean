/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Log-Normal Distribution: Moment and Tail Formulas

Formalises the standard actuarial moment and tail formulas for the log-normal
distribution with log-mean `mu` and log-std `sigma > 0`:

  f(x) = (1 / (x * sigma * sqrt(2*pi))) * exp(-(ln(x) - mu)^2 / (2*sigma^2))
  for x > 0, else 0.

The log-normal arises as exp(Z) where Z ~ N(mu, sigma^2). It is the standard
model for insurance claim sizes in non-life actuarial science.

## Main results

* `LogNormal.mean`          -- E[X] = exp(mu + sigma^2/2)
* `LogNormal.variance`      -- Var(X) = (exp(sigma^2)-1) * exp(2*mu + sigma^2)
* `LogNormal.median`        -- Median X = exp(mu)
* `LogNormal.tail_chebyshev`-- P(X > t) <= exp(2*mu + 2*sigma^2) / t^2

## Design notes

Mathlib 4.28 does not ship `logNormalMeasure` or `logNormalPDF` as named entities.
We define the measure as the pushforward of the real Gaussian measure under `exp`.
Specifically, if `gaussianReal mu sigma^2` is the Gaussian measure on R, then the
log-normal measure is its pushforward under the exponential map.

This design choice makes the median result essentially definitional: the median of
the log-normal is the point where CDF = 1/2, which corresponds to the median of
the underlying Gaussian (at `mu`), pushed through `exp`.

The Chebyshev bound `P(X > t) <= Var(X)/t^2` is closed without the full variance
formula by using the Markov/Chebyshev inequality from Mathlib directly, with the
variance upper-bounded by `exp(2*mu + 2*sigma^2)` (which is >= Var(X) since
`exp(sigma^2) - 1 <= exp(sigma^2)`).

## References

* Aitchison, J. and Brown, J.A.C., *The Lognormal Distribution* (1957).
* Klugman, Panjer, Willmot, *Loss Models*, 5th ed. (2019), Ch. 4.
-/

import Mathlib
import Pythia.Basic
import Pythia.Tactic.Pythia

namespace Pythia.Actuarial.LogNormal

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal NNReal

/-! ### Setup -/

variable {mu sigma : ℝ} (hs : 0 < sigma)

/-! ### Log-normal measure as pushforward of Gaussian -/

/-- The variance parameter for the log-normal as an NNReal. -/
noncomputable def lnVariance (sigma : ℝ) : ℝ≥0 :=
  ⟨sigma ^ 2, sq_nonneg sigma⟩

/-- The log-normal measure: pushforward of `gaussianReal mu (sigma^2)` under `exp`.
This is the canonical abstract definition; it makes `median` and `mean`
reduce to known Gaussian identities. -/
noncomputable def logNormalMeasure (mu sigma : ℝ) : MeasureTheory.Measure ℝ :=
  (ProbabilityTheory.gaussianReal mu (lnVariance sigma)).map Real.exp

/-- `logNormalMeasure` is a probability measure (pushforward preserves probability). -/
instance isProbabilityMeasure_logNormal :
    IsProbabilityMeasure (logNormalMeasure mu sigma) := by
  unfold logNormalMeasure
  exact Measure.isProbabilityMeasure_map (Real.measurable_exp.aemeasurable)

/-! ### Helper lemmas -/

private lemma lnVariance_ne_zero (hs : 0 < sigma) : lnVariance sigma ≠ 0 := by
  exact ne_of_gt ( Subtype.mk_lt_mk.mpr ( sq_pos_of_pos hs ) )

private lemma lnVariance_val (sigma : ℝ) : (lnVariance sigma : ℝ) = sigma ^ 2 := by
  rfl

/-
Key algebraic identity: completing the square in the Gaussian PDF times exp.
  `gaussianPDFReal μ v x * exp(t*x) = exp(μ*t + v*t^2/2) * gaussianPDFReal (μ + v*t) v x`
-/
private lemma gaussianPDFReal_mul_exp (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (t x : ℝ) :
    gaussianPDFReal μ v x * Real.exp (t * x) =
    Real.exp (μ * t + ↑v * t ^ 2 / 2) * gaussianPDFReal (μ + ↑v * t) v x := by
  unfold gaussianPDFReal;
  ring_nf;
  norm_num [ sq, mul_assoc, mul_comm, mul_left_comm, hv ] ; ring;
  simpa only [ mul_assoc, ← Real.exp_add ] using by ring;

/-
The Gaussian MGF: `∫ exp(t*x) d(gaussianReal μ v) = exp(μ*t + v*t²/2)`.
-/
theorem gaussianReal_mgf (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (t : ℝ) :
    ∫ x, Real.exp (t * x) ∂(gaussianReal μ v) = Real.exp (μ * t + ↑v * t ^ 2 / 2) := by
  -- Apply the lemma `integral_gaussianReal_eq_integral_smul` with `f = exp(t*x)`.
  have h_integral : ∫ x, Real.exp (t * x) ∂(gaussianReal μ v) = ∫ x, (gaussianPDFReal μ v x) * Real.exp (t * x) := by
    exact?;
  rw [ h_integral, funext fun x => gaussianPDFReal_mul_exp μ hv t x ];
  rw [ MeasureTheory.integral_const_mul, integral_gaussianPDFReal_eq_one ] ; aesop;
  assumption

/-
Gaussian symmetry: P(Z ≤ μ) = 1/2 for Z ~ N(μ, σ²).
-/
theorem gaussianReal_Iic_self (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (gaussianReal μ v).real (Iic μ) = 1 / 2 := by
  -- Use the symmetry of the Gaussian to rewrite the measure in terms of the CDF.
  have h_symm : (gaussianReal μ v).real (Set.Iic μ) = (gaussianReal 0 v).real (Set.Iic 0) := by
    have h_gaussian_symm : (gaussianReal μ v).real (Set.Iic μ) = (Measure.map (fun x => x + μ) (gaussianReal 0 v)).real (Set.Iic μ) := by
      rw [ gaussianReal_map_add_const ] ; aesop;
    erw [ h_gaussian_symm, Measure.real, Measure.real, Measure.map_apply ] <;> norm_num [ Set.Iic_def ];
    exact measurable_id.add_const μ;
  -- Use the symmetry of the Gaussian to rewrite the measure in terms of the CDF at 0.
  have h_symm : (gaussianReal 0 v).real (Set.Iic 0) = (gaussianReal 0 v).real (Set.Ioi 0) := by
    have h_symm : (gaussianReal 0 v).real (Set.Iic 0) = (gaussianReal 0 v).real (Set.Ici 0) := by
      have h_symm : Measure.map (fun x => -x) (gaussianReal 0 v) = gaussianReal 0 v := by
        convert gaussianReal_map_neg using 1;
        norm_num;
      rw [ ← h_symm, MeasureTheory.measureReal_def, MeasureTheory.measureReal_def, Measure.map_apply ] <;> norm_num;
      · rw [ h_symm ];
      · exact measurable_id.neg;
    rw [ h_symm, MeasureTheory.measureReal_def, MeasureTheory.measureReal_def, MeasureTheory.measure_congr ];
    rw [ MeasureTheory.ae_eq_set ] ; norm_num;
    rw [ gaussianReal ];
    simp +decide [ hv, gaussianPDF ];
  have h_total : (gaussianReal 0 v).real (Set.Iic 0) + (gaussianReal 0 v).real (Set.Ioi 0) = 1 := by
    rw [ ← MeasureTheory.measureReal_union ] <;> norm_num;
  linarith

/-! ### Mean -/

/-
**Log-normal mean.**
E[X] = exp(mu + sigma^2/2).
-/
@[stat_lemma]
theorem mean :
    ∫ x, x ∂(logNormalMeasure mu sigma) =
    Real.exp (mu + sigma ^ 2 / 2) := by
  by_cases h : sigma = 0 <;> simp_all +decide [ logNormalMeasure, gaussianReal_mgf, lnVariance_ne_zero ];
  · unfold gaussianReal; norm_num [ lnVariance ] ;
    rw [ MeasureTheory.integral_map ] <;> norm_num [ Real.exp_ne_zero ];
    · exact Real.continuous_exp.measurable.aemeasurable;
    · exact measurable_id.aestronglyMeasurable;
  · convert gaussianReal_mgf mu ( show lnVariance sigma ≠ 0 from ?_ ) 1 using 1;
    · rw [ MeasureTheory.integral_map ];
      · norm_num;
      · exact Real.continuous_exp.measurable.aemeasurable;
      · exact measurable_id.aestronglyMeasurable;
    · norm_num [ lnVariance ];
    · exact ne_of_gt ( Subtype.mk_lt_mk.mpr ( sq_pos_of_ne_zero h ) )

/-! ### Variance -/

/-
**Log-normal variance.**
Var(X) = (exp(sigma^2) - 1) * exp(2*mu + sigma^2).
-/
@[stat_lemma]
theorem variance :
    ProbabilityTheory.variance id (logNormalMeasure mu sigma) =
    (Real.exp (sigma ^ 2) - 1) * Real.exp (2 * mu + sigma ^ 2) := by
  -- First, let's establish that the integral of the square of the log-normal distribution equals exp(2mu + 2sigma^2).
  have h_mean_squared : ∫ x, x^2 ∂(logNormalMeasure mu sigma) = Real.exp (2 * mu + 2 * sigma^2) := by
    -- Use the fact that the integral of $x^2$ with respect to the log-normal measure is the same as the integral of $\exp(2x)$ with respect to the normal measure.
    have h_integral : ∫ x, x^2 ∂(logNormalMeasure mu sigma) = ∫ x, Real.exp (2 * x) ∂(gaussianReal mu (lnVariance sigma)) := by
      rw [ logNormalMeasure, MeasureTheory.integral_map ];
      · norm_num [ ← Real.exp_nat_mul ];
      · exact Real.continuous_exp.measurable.aemeasurable;
      · exact Continuous.aestronglyMeasurable ( continuous_pow 2 );
    by_cases h : lnVariance sigma = 0 <;> simp_all +decide [ gaussianReal_mgf ];
    · exact sq_eq_zero_iff.mp ( by simpa [ lnVariance_val ] using congr_arg NNReal.toReal h );
    · rw [ show ( lnVariance sigma : ℝ ) = sigma ^ 2 by exact? ] ; ring;
  rw [ ProbabilityTheory.variance, ProbabilityTheory.evariance_eq_lintegral_ofReal, ← MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
  · have h_mean : ∫ x, x ∂(logNormalMeasure mu sigma) = Real.exp (mu + sigma^2 / 2) := by
      exact?;
    simp_all +decide [ sub_sq, mul_assoc, mul_comm, mul_left_comm, ← Real.exp_add ];
    rw [ MeasureTheory.integral_add, MeasureTheory.integral_sub ];
    · simp_all +decide [ MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul ];
      ring;
      rw [ ← Real.exp_nat_mul ] ; ring;
      rw [ ← Real.exp_add ] ; ring;
    · exact ( by contrapose! h_mean_squared; rw [ MeasureTheory.integral_undef h_mean_squared ] ; positivity );
    · exact MeasureTheory.Integrable.mul_const ( by exact ( by contrapose! h_mean; rw [ MeasureTheory.integral_undef h_mean ] ; positivity ) ) _;
    · refine' MeasureTheory.Integrable.sub _ _;
      · exact ( by contrapose! h_mean_squared; rw [ MeasureTheory.integral_undef h_mean_squared ] ; positivity );
      · exact MeasureTheory.Integrable.mul_const ( by exact ( by contrapose! h_mean; rw [ MeasureTheory.integral_undef h_mean ] ; positivity ) ) _;
    · apply_rules [ MeasureTheory.integrable_const ];
  · exact Filter.Eventually.of_forall fun x => sq_nonneg _;
  · exact Measurable.aestronglyMeasurable ( by measurability )

/-! ### Median -/

/-
**Log-normal median.**
Median X = exp(mu).
-/
theorem median (hs : 0 < sigma) :
    ∃ m : ℝ,
      (logNormalMeasure mu sigma).real (Set.Iic m) = 1 / 2 ∧
      m = Real.exp mu := by
  refine' ⟨ Real.exp mu, _, rfl ⟩;
  unfold logNormalMeasure;
  rw [ Measure.real, Measure.map_apply ];
  · convert gaussianReal_Iic_self mu ( lnVariance_ne_zero hs ) using 1;
    congr ; ext ; aesop;
  · exact Real.continuous_exp.measurable;
  · norm_num

/-! ### Chebyshev tail bound -/

/-
**Log-normal Chebyshev tail bound.**
For `t > 0`,  P(X > t) <= exp(2*mu + 2*sigma^2) / t^2.
-/
@[stat_lemma]
theorem tail_chebyshev (t : ℝ) (ht : 0 < t) :
    (logNormalMeasure mu sigma).real (Set.Ioi t) <=
    Real.exp (2 * mu + 2 * sigma ^ 2) / t ^ 2 := by
  by_cases h_sigma : sigma = 0;
  · unfold logNormalMeasure;
    unfold gaussianReal; norm_num [ h_sigma ];
    unfold lnVariance; norm_num;
    rw [ MeasureTheory.Measure.real ];
    rw [ Measure.map_dirac ];
    · by_cases h : Real.exp mu > t <;> simp_all +decide [ two_mul, Real.exp_add ];
      · rw [ le_div_iff₀ ] <;> nlinarith [ Real.exp_pos mu ];
      · positivity;
    · exact Real.continuous_exp.measurable;
  · have h_second_moment : ∫ x, x ^ 2 ∂(logNormalMeasure mu sigma) = Real.exp (2 * mu + 2 * sigma ^ 2) := by
      convert gaussianReal_mgf mu ( show lnVariance sigma ≠ 0 from ?_ ) 2 using 1;
      · rw [ logNormalMeasure, MeasureTheory.integral_map ];
        · norm_num [ ← Real.exp_nat_mul ];
        · exact Real.continuous_exp.measurable.aemeasurable;
        · exact Continuous.aestronglyMeasurable ( continuous_pow 2 );
      · unfold lnVariance; norm_num; ring;
      · exact ne_of_gt ( Subtype.mk_lt_mk.mpr ( sq_pos_of_ne_zero h_sigma ) );
    have h_integral_le : ∫ x in Set.Ioi t, x ^ 2 ∂(logNormalMeasure mu sigma) ≥ t ^ 2 * (logNormalMeasure mu sigma).real (Set.Ioi t) := by
      have h_integral_le : ∫ x in Set.Ioi t, x ^ 2 ∂(logNormalMeasure mu sigma) ≥ ∫ x in Set.Ioi t, t ^ 2 ∂(logNormalMeasure mu sigma) := by
        refine' MeasureTheory.setIntegral_mono_on _ _ _ _ <;> norm_num;
        · exact MeasureTheory.Integrable.integrableOn ( by exact ( by contrapose! h_second_moment; rw [ MeasureTheory.integral_undef h_second_moment ] ; positivity ) );
        · exact fun x hx => by gcongr;
      simpa [ mul_comm ] using h_integral_le;
    rw [ le_div_iff₀' ( sq_pos_of_pos ht ) ];
    refine' le_trans h_integral_le ( h_second_moment ▸ MeasureTheory.setIntegral_le_integral _ _ );
    · exact ( by contrapose! h_second_moment; rw [ MeasureTheory.integral_undef h_second_moment ] ; positivity );
    · exact Filter.Eventually.of_forall fun x => sq_nonneg x

end Pythia.Actuarial.LogNormal