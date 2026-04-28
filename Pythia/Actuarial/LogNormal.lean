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

* `LogNormal.mean`          -- E[X] = exp(mu + sigma^2/2)   (scaffold sorry)
* `LogNormal.variance`      -- Var(X) = (exp(sigma^2)-1) * exp(2*mu + sigma^2)   (scaffold sorry)
* `LogNormal.median`        -- Median X = exp(mu)   (closed by rfl-level algebra)
* `LogNormal.tail_chebyshev`-- P(X > t) <= exp(2*mu + 2*sigma^2) / t^2   (CLOSED via Chebyshev)

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

Status:
- `mean`          scaffold sorry: Gaussian-to-lognormal MGF identity
- `variance`      scaffold sorry: depends on mean + E[X^2]
- `median`        scaffold sorry: pushforward + Gaussian median identity
- `tail_chebyshev` CLOSED (Markov inequality with E[X^2] bound)

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

/-! ### Mean -/

/-
**Log-normal mean.**
E[X] = exp(mu + sigma^2/2).

Proof: E[exp(Z)] where Z ~ N(mu, sigma^2) equals exp(mu + sigma^2/2).
This is the moment generating function of the normal evaluated at t=1:
  MGF_Z(1) = exp(mu * 1 + sigma^2 * 1^2 / 2) = exp(mu + sigma^2/2).
Mathlib has `ProbabilityTheory.gaussianReal_mgf` or an MGF identity for
the Gaussian, but the full chain from pushforward integral to the MGF
formula is not yet wired up in Mathlib 4.28.

Status: scaffold sorry. Requires
  (1) `MeasureTheory.integral_map` to rewrite the pushforward integral
  (2) Gaussian MGF identity `∫ exp(x) ∂(gaussianReal mu sigma^2) = exp(mu + sigma^2/2)`
Aristotle queue candidate.
-/
@[stat_lemma]
theorem mean :
    ∫ x, x ∂(logNormalMeasure mu sigma) =
    Real.exp (mu + sigma ^ 2 / 2) := by
  -- TODO (Aristotle):
  --   rw [logNormalMeasure, integral_map measurable_exp.aemeasurable]
  --   -- goal: ∫ x, exp(x) ∂(gaussianReal mu (lnVariance sigma)) = exp(mu + sigma^2/2)
  --   -- Apply Gaussian MGF at t = 1:
  --   --   ∫ exp(t*x) ∂(gaussianReal mu v) = exp(mu*t + v*t^2/2)  at t=1.
  -- Use the fact that the integral of $e^Z$ with respect to the Gaussian measure is the moment generating function of the normal distribution.
  have h_mgf : ∫ x, Real.exp x ∂(ProbabilityTheory.gaussianReal mu (lnVariance sigma)) = Real.exp (mu + (sigma)^2 / 2) := by
    have := @ProbabilityTheory.mgf_gaussianReal;
    convert this ( show Measure.map id ( gaussianReal mu ( lnVariance sigma ) ) = gaussianReal mu ( lnVariance sigma ) from Measure.map_id ) 1 using 1 <;> norm_num [ mgf ];
    exact?;
  erw [ ← h_mgf, MeasureTheory.integral_map ];
  · exact Real.continuous_exp.measurable.aemeasurable;
  · exact measurable_id.aestronglyMeasurable

/-! ### Variance -/

/-
**Log-normal variance.**
Var(X) = (exp(sigma^2) - 1) * exp(2*mu + sigma^2).

This equals E[X^2] - (E[X])^2 where E[X^2] = exp(2*mu + 2*sigma^2)
(MGF of normal evaluated at t=2).

Status: scaffold sorry. Depends on mean + second-moment MGF evaluation.
Aristotle queue candidate.
-/
@[stat_lemma]
theorem variance :
    ProbabilityTheory.variance id (logNormalMeasure mu sigma) =
    (Real.exp (sigma ^ 2) - 1) * Real.exp (2 * mu + sigma ^ 2) := by
  -- TODO (Aristotle): expand via variance_eq, then close E[X^2] by MGF at t=2.
  have h_var : ∫ x, x^2 ∂(logNormalMeasure mu sigma) = Real.exp (2 * mu + 2 * sigma^2) := by
    -- By definition of log-normal measure, we have:
    have h_log_normal : ∫ x, x ^ 2 ∂(logNormalMeasure mu sigma) = ∫ z, (Real.exp z) ^ 2 ∂(ProbabilityTheory.gaussianReal mu (lnVariance sigma)) := by
      unfold logNormalMeasure;
      rw [ MeasureTheory.integral_map ];
      · exact Real.continuous_exp.measurable.aemeasurable;
      · exact Continuous.aestronglyMeasurable ( continuous_pow 2 );
    rw [ h_log_normal, show ( fun z => Real.exp z ^ 2 ) = fun z => Real.exp ( 2 * z ) by ext; rw [ ← Real.exp_nat_mul ] ; ring ];
    have := @ProbabilityTheory.mgf_gaussianReal;
    convert @this ℝ _ ( gaussianReal mu ( lnVariance sigma ) ) mu ( lnVariance sigma ) id _ 2 using 1 <;> norm_num [ lnVariance ] ; ring
  generalize_proofs at *; (
  have h_mean : ∫ x, x ∂(logNormalMeasure mu sigma) = Real.exp (mu + sigma^2 / 2) := by
    grind +suggestions
  generalize_proofs at *; (
  have h_var : ProbabilityTheory.variance id (logNormalMeasure mu sigma) = (∫ x, x^2 ∂(logNormalMeasure mu sigma)) - (∫ x, x ∂(logNormalMeasure mu sigma))^2 := by
    rw [ ProbabilityTheory.variance, ProbabilityTheory.evariance_eq_lintegral_ofReal, ← MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
    · simp +decide [ sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, mul_assoc, mul_comm, mul_left_comm, MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const ];
      rw [ MeasureTheory.integral_add, MeasureTheory.integral_sub ] <;> norm_num [ MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul ] ; ring!; (
      exact ( by contrapose! h_var; rw [ MeasureTheory.integral_undef h_var ] ; positivity ));
      · exact MeasureTheory.Integrable.mul_const ( by exact ( by contrapose! h_mean; rw [ MeasureTheory.integral_undef h_mean ] ; positivity ) ) _;
      · refine' MeasureTheory.Integrable.sub _ _;
        · exact ( by contrapose! h_var; rw [ MeasureTheory.integral_undef h_var ] ; positivity );
        · exact MeasureTheory.Integrable.mul_const ( by exact ( by contrapose! h_mean; rw [ MeasureTheory.integral_undef h_mean ] ; positivity ) ) _;
    · exact Filter.Eventually.of_forall fun x => sq_nonneg _;
    · exact Measurable.aestronglyMeasurable ( by measurability )
  generalize_proofs at *; (
  rw [ h_var, ‹∫ x : ℝ, x ^ 2 ∂logNormalMeasure mu sigma = Real.exp ( 2 * mu + 2 * sigma ^ 2 ) ›, h_mean ] ; ring; norm_num [ ← Real.exp_nat_mul, ← Real.exp_add ] ; ring;)))

/-! ### Median -/

/-! ### Gaussian CDF at its mean -/

/-
When `v ≠ 0`, the Gaussian measure is absolutely continuous w.r.t. Lebesgue,
so singletons have measure zero and `P(Z ≤ mu) = 1/2` by symmetry.
-/
lemma lnVariance_ne_zero (hs : 0 < sigma) : lnVariance sigma ≠ 0 := by
  exact ne_of_gt ( Subtype.mk_lt_mk.mpr ( sq_pos_of_pos hs ) )

/-
P(Z ≤ 0) = 1/2 for Z ~ N(0, v) with v ≠ 0, by symmetry.
-/
lemma gaussianReal_real_Iic_zero {v : ℝ≥0} (hv : v ≠ 0) :
    (gaussianReal 0 v).real (Set.Iic 0) = 1 / 2 := by
  -- By symmetry of the Gaussian measure, we have (gaussianReal 0 v).real (Iic 0) = (gaussianReal 0 v).real (Ioi 0).
  have h_symm : (gaussianReal 0 v).real (Iic 0) = (gaussianReal 0 v).real (Ioi 0) := by
    have h_symm : (gaussianReal 0 v).real (Set.Iic 0) = (gaussianReal 0 v).real (Set.Ici 0) := by
      have h_symm : (gaussianReal 0 v).real (Set.Iic 0) = (MeasureTheory.Measure.map (fun x => -x) (gaussianReal 0 v)).real (Set.Ici 0) := by
        rw [ MeasureTheory.Measure.real, MeasureTheory.Measure.real ];
        rw [ Measure.map_apply ] <;> norm_num;
        exact measurable_id.neg;
      rw [ h_symm, gaussianReal_map_neg, neg_zero ];
    rw [ h_symm, MeasureTheory.measureReal_def, MeasureTheory.measureReal_def, MeasureTheory.measure_congr ];
    rw [ MeasureTheory.ae_eq_set ] ; norm_num;
    have h_abs_cont : MeasureTheory.Measure.AbsolutelyContinuous (gaussianReal 0 v) MeasureTheory.volume := by
      exact?;
    exact h_abs_cont ( by norm_num );
  have h_union : (gaussianReal 0 v).real (Iic 0 ∪ Ioi 0) = 1 := by
    norm_num [ MeasureTheory.measureReal_def ];
  rw [ MeasureTheory.measureReal_union ] at h_union <;> norm_num at * ; linarith

/-
P(Z ≤ mu) = 1/2 for Z ~ N(mu, v) with v ≠ 0.
-/
lemma gaussianReal_real_Iic_mean {v : ℝ≥0} (hv : v ≠ 0) :
    (gaussianReal mu v).real (Set.Iic mu) = 1 / 2 := by
  -- By definition of $gaussianReal$, we have $gaussianReal mu v = (gaussianReal 0 v).map (fun x => mu + x)$.
  have h_map : gaussianReal mu v = (gaussianReal 0 v).map (fun x => mu + x) := by
    rw [ gaussianReal_map_const_add ] ; norm_num;
  rw [ h_map, MeasureTheory.Measure.real ];
  rw [ Measure.map_apply ] <;> norm_num;
  · convert gaussianReal_real_Iic_zero hv using 1;
  · exact measurable_const.add measurable_id

/-
**Log-normal median.**
Median X = exp(mu).

The log-normal CDF satisfies F(exp(mu)) = 1/2 because:
  P(X <= exp(mu)) = P(exp(Z) <= exp(mu)) = P(Z <= mu) = 1/2
since Z ~ N(mu, sigma^2) and the normal CDF at its own mean equals 1/2.

Note: requires `0 < sigma` since the Gaussian must be non-degenerate for median = mu.
-/
theorem median (hs : 0 < sigma) :
    ∃ m : ℝ,
      (logNormalMeasure mu sigma).real (Set.Iic m) = 1 / 2 ∧
      m = Real.exp mu := by
  -- TODO (Aristotle): use pushforward + Gaussian symmetry P(Z <= mu) = 1/2.
  refine' ⟨ _, _, rfl ⟩;
  convert gaussianReal_real_Iic_mean ( lnVariance_ne_zero hs ) using 1;
  rw [ MeasureTheory.Measure.real, MeasureTheory.Measure.real ];
  rw [ logNormalMeasure, MeasureTheory.Measure.map_apply ];
  rotate_right;
  exact mu;
  · congr with x ; aesop;
  · exact Real.continuous_exp.measurable;
  · norm_num

/-! ### Chebyshev tail bound -/

/-
**Log-normal Chebyshev tail bound.**
For `t > 0`,  P(X > t) <= exp(2*mu + 2*sigma^2) / t^2.

Proof:
  P(X > t) <= E[X^2] / t^2          (Markov inequality applied to X^2)
           = exp(2*mu + 2*sigma^2) / t^2.

The Markov inequality gives P(|X| > t) <= E[|X|^2] / t^2.
Since X > 0 a.s. (log-normal), |X| = X and E[X^2] = exp(2*mu + 2*sigma^2).

Status: scaffold sorry. The bound is CORRECT by Markov. Closure requires:
  (1) `ProbabilityTheory.measure_ge_le_lintegral_div` (Markov)
  (2) E[X^2] = exp(2*mu + 2*sigma^2) -- same scaffold sorry as `variance`
Partial closure: the Chebyshev structure is correct; blocks on E[X^2] computation.
Aristotle queue candidate (unblocked once `variance` sorry closes).
-/
@[stat_lemma]
theorem tail_chebyshev (t : ℝ) (ht : 0 < t) :
    (logNormalMeasure mu sigma).real (Set.Ioi t) <=
    Real.exp (2 * mu + 2 * sigma ^ 2) / t ^ 2 := by
  -- TODO (Aristotle): apply Markov to X^2 with bound exp(2*mu + 2*sigma^2).
  -- Key steps:
  --   have hX2 : ∫ x, x^2 ∂(logNormalMeasure mu sigma) = exp(2*mu + 2*sigma^2) := ...
  --   have markov := ProbabilityTheory.mul_meas_ge_le_lintegral₀ ...
  --   linarith [markov, hX2, sq_pos_of_pos ht]
  -- We'll use the fact that $E[X^2] = \exp(2\mu + 2\sigma^2)$.
  have h_exp : ∫ x, x^2 ∂(logNormalMeasure mu sigma) = Real.exp (2 * mu + 2 * sigma ^ 2) := by
    -- The second moment of the log-normal distribution is given by the exponential of the second moment of the normal distribution.
    have h_second_moment : ∫ x, x^2 ∂(logNormalMeasure mu sigma) = ∫ x, Real.exp (2 * x) ∂(gaussianReal mu (lnVariance sigma)) := by
      rw [ logNormalMeasure, MeasureTheory.integral_map ];
      · norm_num [ ← Real.exp_nat_mul ];
      · exact Real.continuous_exp.measurable.aemeasurable;
      · exact Continuous.aestronglyMeasurable ( continuous_pow 2 );
    have := @ProbabilityTheory.mgf_gaussianReal;
    convert @this ℝ _ ( gaussianReal mu ( lnVariance sigma ) ) mu ( lnVariance sigma ) id _ 2 using 1 <;> norm_num [ mgf ];
    unfold lnVariance; norm_num; ring;
  rw [ ← h_exp, le_div_iff₀ ( sq_pos_of_pos ht ) ];
  have h_markov : (∫ x in Set.Ioi t, t^2 ∂(logNormalMeasure mu sigma)) ≤ (∫ x in Set.Ioi t, x^2 ∂(logNormalMeasure mu sigma)) := by
    refine' MeasureTheory.setIntegral_mono_on _ _ _ _ <;> norm_num;
    · exact MeasureTheory.Integrable.integrableOn ( by exact ( by contrapose! h_exp; rw [ MeasureTheory.integral_undef h_exp ] ; positivity ) );
    · exact fun x hx => by gcongr;
  convert h_markov.trans ( MeasureTheory.setIntegral_le_integral _ _ ) using 1;
  · norm_num [ mul_comm ];
  · exact ( by contrapose! h_exp; rw [ MeasureTheory.integral_undef h_exp ] ; positivity );
  · exact Filter.Eventually.of_forall fun x => sq_nonneg x

end Pythia.Actuarial.LogNormal