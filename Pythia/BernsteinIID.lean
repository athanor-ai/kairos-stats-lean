/-
Pythia.BernsteinIID — Bernstein's inequality for iid bounded RVs,
proved via the Chernoff bound + independence + MGF bound.

This module provides `bernstein_iid_corrected`, the corrected version of
the false `bernstein_iid_textbook` in MiniPythia.lean. The original
statement used `IndepFun (X 0) (X t)` (pairwise independence with X_0),
which forces X_0 to be a.s. constant but does not give mutual independence.
The corrected version uses `iIndepFun X μ` (mutual independence) and adds
`Measurable (X t)` for each t.
-/
import Mathlib
import Pythia.MGFBoundedSubGamma

namespace Pythia

open MeasureTheory ProbabilityTheory ENNReal Real
open scoped NNReal

/-! ### Step 1: MGF product bound for independent bounded centered RVs -/

/-- Each individual MGF is bounded by the sub-gamma rate. -/
private lemma mgf_single_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {b sigma_sq : ℝ}
    (hb : 0 ≤ b) (hX : Measurable X)
    (h_bounded : ∀ᵐ ω ∂μ, |X ω| ≤ b)
    (h_zero_mean : ∫ ω, X ω ∂μ = 0)
    (h_var : ∫ ω, (X ω) ^ 2 ∂μ ≤ sigma_sq)
    {lam : ℝ} (hlam : 0 ≤ lam) (hbl : b * lam < 3) :
    mgf X μ lam ≤ Real.exp (sigma_sq * lam ^ 2 / (2 * (1 - b * lam / 3))) :=
  mgf_le_subGamma_of_bounded hX hb h_bounded h_zero_mean h_var hlam hbl

/-- Finset.prod bound: if each 0 ≤ factor ≤ exp(r), then ∏ ≤ exp(n*r). -/
private lemma prod_le_exp_mul
    {n : ℕ} {r : ℝ} {f : ℕ → ℝ}
    (hf_nn : ∀ i ∈ Finset.range n, 0 ≤ f i)
    (hf : ∀ i ∈ Finset.range n, f i ≤ Real.exp r) :
    ∏ i ∈ Finset.range n, f i ≤ Real.exp (↑n * r) := by
  exact le_trans (Finset.prod_le_prod (fun i hi ↦ hf_nn i hi) hf)
    (by norm_num [← Real.exp_nat_mul])

/-- The MGF of a sum of n mutually independent bounded centered RVs is bounded. -/
lemma mgf_sum_iid_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {b sigma_sq : ℝ}
    (hb : 0 ≤ b)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ t, Measurable (X t))
    (h_bounded : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ b)
    (h_zero_mean : ∀ t, ∫ ω, X t ω ∂μ = 0)
    (h_var_bound : ∀ t, ∫ ω, (X t ω) ^ 2 ∂μ ≤ sigma_sq)
    {lam : ℝ} (hlam : 0 ≤ lam) (hbl : b * lam < 3)
    (n : ℕ) :
    mgf (∑ i ∈ Finset.range n, X i) μ lam ≤
      Real.exp (↑n * sigma_sq * lam ^ 2 / (2 * (1 - b * lam / 3))) := by
  convert prod_le_exp_mul _ _ using 2
  convert iIndepFun.mgf_sum h_indep h_meas _ using 1
  rw [mul_assoc, mul_div_assoc]
  · exact fun i _ => integral_nonneg fun ω => Real.exp_nonneg _
  · exact fun i _ => mgf_single_le hb (h_meas i) (h_bounded i)
      (h_zero_mean i) (h_var_bound i) hlam hbl

/-! ### Step 2: Key algebraic identity for the optimal λ -/

/-- With λ = eps / D where D = n*sigma_sq + b*eps/3,
    the Chernoff exponent simplifies to -eps²/(2*D). -/
private lemma bernstein_exponent_eq
    {eps b sigma_sq : ℝ} {n : ℕ}
    (_heps : 0 < eps) (_hb : 0 < b) (_hsigma : 0 < sigma_sq) (_hn : 0 < n) :
    -(eps / (↑n * sigma_sq + b * eps / 3) * eps) +
      ↑n * sigma_sq * (eps / (↑n * sigma_sq + b * eps / 3)) ^ 2 /
      (2 * (1 - b * (eps / (↑n * sigma_sq + b * eps / 3)) / 3))
      = -(eps ^ 2) / (2 * (↑n * sigma_sq + b * eps / 3)) := by
  field_simp
  grobner

/-! ### Step 3: Zero-variance case -/

/-
If X is bounded, measurable, and ∫ X² ≤ 0, then X = 0 a.e.
    Boundedness ensures integrability of X².
-/
private lemma ae_zero_of_bounded_integral_sq_le_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {b : ℝ}
    (hX : Measurable X)
    (h_bounded : ∀ᵐ ω ∂μ, |X ω| ≤ b)
    (h : ∫ ω, (X ω) ^ 2 ∂μ ≤ 0) :
    ∀ᵐ ω ∂μ, X ω = 0 := by
  have h_zero_ae : ∫ ω, (X ω) ^ 2 ∂μ = 0 := by
    exact le_antisymm h ( MeasureTheory.integral_nonneg fun ω => sq_nonneg _ );
  rw [ MeasureTheory.integral_eq_zero_iff_of_nonneg ] at h_zero_ae;
  · exact h_zero_ae.mono fun ω hω => sq_eq_zero_iff.mp hω;
  · exact fun _ => sq_nonneg _;
  · refine' MeasureTheory.Integrable.mono' ( MeasureTheory.integrable_const ( b ^ 2 ) ) _ _;
    · exact hX.pow_const 2 |> Measurable.aestronglyMeasurable;
    · filter_upwards [ h_bounded ] with ω hω using by simpa using pow_le_pow_left₀ ( abs_nonneg _ ) hω 2

/-
If each X_t is bounded with ∫ X_t² ≤ 0, the sum is 0 a.s.
-/
private lemma sum_ae_zero_of_bounded_var_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {b : ℝ}
    (h_meas : ∀ t, Measurable (X t))
    (h_bounded : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ b)
    (h_var_bound : ∀ t, ∫ ω, (X t ω) ^ 2 ∂μ ≤ 0)
    (n : ℕ) :
    ∀ᵐ ω ∂μ, (∑ i ∈ Finset.range n, X i) ω = 0 := by
  have h_sum_zero : ∀ t, ∀ᵐ ω ∂μ, X t ω = 0 := by
    exact fun t => ae_zero_of_bounded_integral_sq_le_zero (h_meas t) (h_bounded t) (h_var_bound t)
  filter_upwards [ MeasureTheory.ae_all_iff.2 h_sum_zero ] with ω hω using by simp +decide [ hω ] ;

/-! ### Step 4: Integrability of exp(λ · S_n) -/

/-- exp(λ · S_n) is integrable for bounded RVs. -/
private lemma integrable_exp_sum
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {b : ℝ}
    (h_meas : ∀ t, Measurable (X t))
    (h_bounded : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ b)
    (lam : ℝ) (n : ℕ) :
    Integrable (fun ω => Real.exp (lam * (∑ i ∈ Finset.range n, X i) ω)) μ := by
  have h_bounded : ∀ᵐ ω ∂μ, |∑ i ∈ Finset.range n, X i ω| ≤ n * b := by
    filter_upwards [ae_all_iff.2 h_bounded] with ω hω using
      le_trans (Finset.abs_sum_le_sum_abs _ _)
        (le_trans (Finset.sum_le_sum fun _ _ => hω _) (by simp +decide))
  refine' Integrable.mono' _ _ _
  refine' fun ω => Real.exp (|lam| * (n * b))
  · norm_num
  · exact Measurable.aestronglyMeasurable (by measurability)
  · filter_upwards [h_bounded] with ω hω using by
      simpa using Real.exp_le_exp.2
        (by cases abs_cases lam <;> nlinarith [abs_le.mp hω])

/-! ### Step 5: Conversion from .toReal to ENNReal -/

/-- Convert Chernoff bound from .toReal to ENNReal. -/
private lemma measure_le_ofReal_of_real_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {s : Set Ω} {r : ℝ} (hr : 0 ≤ r) (h : μ.real s ≤ r) :
    μ s ≤ ENNReal.ofReal r := by
  rwa [ENNReal.le_ofReal_iff_toReal_le]
  · exact measure_ne_top _ _
  · exact hr

/-! ### Main theorem -/

/-
**Bernstein's inequality for iid bounded RVs** (corrected version).

    Given mutually independent `X_i` with `|X_i| ≤ b` a.s.,
    `E[X_i] = 0`, `E[X_i²] ≤ σ²`, for `n` samples and `ε > 0`:
    ```
    P(S_n ≥ ε) ≤ exp(−ε² / (2(nσ² + bε/3)))
    ```

    The original `bernstein_iid_textbook` was false: it used
    `IndepFun (X 0) (X t)` which only forces X_0 to be a.s. constant but
    does not provide mutual independence of `X_1, X_2, ...`. This version
    uses `iIndepFun X μ` (mutual independence) and `Measurable (X t)`.

    Proved via Chernoff bound + independence factorization of MGF +
    Bernstein–Bennett MGF bound from `mgf_le_subGamma_of_bounded`.
-/
theorem bernstein_iid_corrected
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {b : ℝ} {sigma_sq : ℝ}
    (hb_pos : 0 < b) (hsigma_sq_nonneg : 0 ≤ sigma_sq)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ t, Measurable (X t))
    (h_bounded : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ b)
    (h_zero_mean : ∀ t, ∫ ω, X t ω ∂μ = 0)
    (h_var_bound : ∀ t, ∫ ω, (X t ω) ^ 2 ∂μ ≤ sigma_sq)
    (n : ℕ) (eps : ℝ) (hε : 0 < eps) :
    μ {ω | (Finset.range n).sum (fun i => X i ω) ≥ eps} ≤
      ENNReal.ofReal
        (Real.exp (-(eps ^ 2) / (2 * (↑n * sigma_sq + b * eps / 3)))) := by
  by_cases hn : n = 0;
  · simp +decide [ hn, hε.not_ge ];
  · by_cases hsigma_sq_zero : sigma_sq = 0;
    · have h_sum_zero : ∀ᵐ ω ∂μ, (∑ i ∈ Finset.range n, X i) ω = 0 := by
        apply sum_ae_zero_of_bounded_var_zero;
        exacts [ h_meas, h_bounded, fun t => by simpa [ hsigma_sq_zero ] using h_var_bound t ];
      exact le_trans ( MeasureTheory.measure_mono ( show { ω | eps ≤ ∑ i ∈ Finset.range n, X i ω } ⊆ { ω | (∑ i ∈ Finset.range n, X i) ω ≠ 0 } from fun ω hω => by simp_all +decide [ Finset.sum_apply ] ; linarith ) ) ( by rw [ MeasureTheory.measure_mono_null ( show { ω | ( ∑ i ∈ Finset.range n, X i ) ω ≠ 0 } ⊆ { ω | ( ∑ i ∈ Finset.range n, X i ) ω ≠ 0 } from fun ω hω => hω ) h_sum_zero ] ; norm_num );
    · convert measure_le_ofReal_of_real_le _ _;
      · infer_instance;
      · positivity;
      · refine' le_trans ( ProbabilityTheory.measure_ge_le_exp_mul_mgf _ _ _ ) _;
        exact eps / ( n * sigma_sq + b * eps / 3 );
        · positivity;
        · convert integrable_exp_sum h_meas h_bounded ( eps / ( n * sigma_sq + b * eps / 3 ) ) n using 1;
          simp +decide [ Finset.sum_apply ];
        · convert mul_le_mul_of_nonneg_left ( mgf_sum_iid_le ( show 0 ≤ b by positivity ) h_indep h_meas h_bounded h_zero_mean h_var_bound ( show 0 ≤ eps / ( n * sigma_sq + b * eps / 3 ) by positivity ) ( show b * ( eps / ( n * sigma_sq + b * eps / 3 ) ) < 3 by rw [ mul_div, div_lt_iff₀ ] <;> nlinarith [ show ( n : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hn ), show ( sigma_sq : ℝ ) > 0 by positivity, mul_div_cancel₀ ( b * eps ) ( show ( 3 : ℝ ) ≠ 0 by positivity ) ] ) n ) ( Real.exp_nonneg _ ) using 1 ; ring;
          congr! 1;
          · congr! 2;
            rw [ Finset.sum_apply ];
          · rw [ ← Real.exp_add ] ; congr 1 ; field_simp ; ring

end Pythia