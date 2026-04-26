/-
Pythia.MGFBoundedSubGamma — Bernstein-Bennett MGF bound for bounded RVs.

# Main result

`mgf_le_subGamma_of_bounded`: For `X : Ω → ℝ` measurable with
`|X| ≤ b` a.s., `∫ X ∂μ = 0` (centered), `∫ X² ∂μ ≤ σ²` (bounded
second moment), `λ ≥ 0`, and `b·λ < 3`:

    mgf X μ λ ≤ exp(σ² λ² / (2(1 − bλ/3))).

This is the textbook Bernstein–Bennett MGF bound — the missing piece
blocking `bennett_iid`, `bernstein_iid`, `bernstein_martingale`,
`freedman` in `Pythia/Bernstein.lean`.

# Proof overview

1. **Pointwise Taylor bound** (`exp_le_one_add_add_sq_div`):
   For `|x| ≤ b`, `λ ≥ 0`, `bλ < 3`:
   `exp(λx) ≤ 1 + λx + (λx)² / (2(1 − bλ/3))`.

2. **Integration**: using `E[X] = 0` and `E[X²] ≤ σ²`,
   `E[exp(λX)] ≤ 1 + σ²λ² / (2(1 − bλ/3))`.

3. **exp closure**: `1 + u ≤ exp(u)` gives the final bound.

The pointwise bound decomposes into:
- `exp_sub_one_sub_le_sq_div_nonneg`: for `0 ≤ u < 3`,
  `exp(u) − 1 − u ≤ u²/(2(1 − u/3))`.
- `exp_sub_one_sub_le_sq_nonpos`: for `u ≤ 0`,
  `exp(u) − 1 − u ≤ u²/2`.
-/

import Mathlib
import Pythia.Basic

namespace Pythia

open MeasureTheory ProbabilityTheory

/-! ## Pointwise exponential Taylor bounds -/

/-
For `0 ≤ u < 3`: `exp(u) − 1 − u ≤ u² / (2(1 − u/3))`.

Proof: The Taylor series gives `exp(u) − 1 − u = Σ_{k≥2} uᵏ/k!`.
For `k ≥ 2` and `u ≥ 0`, `uᵏ/k! ≤ u² · (u/3)^{k−2}/2` (since
`2 · 3^{k−2} ≤ k!` for `k ≥ 2`). Summing the geometric series:
`Σ ≤ (u²/2) · 1/(1 − u/3) = u²/(2(1 − u/3))`.
-/
lemma exp_sub_one_sub_le_sq_div_nonneg {u : ℝ} (hu : 0 ≤ u) (hu3 : u < 3) :
    Real.exp u - 1 - u ≤ u ^ 2 / (2 * (1 - u / 3)) := by
  -- We'll use the exponential property to simplify the expression. Note that $e^u = \sum_{k=0}^{\infty} \frac{u^k}{k!}$.
  have h_exp : Real.exp u = ∑' k, u^k / Nat.factorial k := by
    simp +decide [ Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div ];
  -- We'll use the fact that $\sum_{k=2}^{\infty} \frac{u^k}{k!} \leq \frac{u^2}{2} \sum_{k=0}^{\infty} \left(\frac{u}{3}\right)^k$.
  have h_sum_bound : ∑' k, u^k / Nat.factorial k - 1 - u ≤ u^2 / 2 * ∑' k, (u / 3)^k := by
    have h_sum_bound : ∑' k, u^k / Nat.factorial k - 1 - u = ∑' k, u^(k+2) / Nat.factorial (k+2) := by
      rw [ ← Summable.sum_add_tsum_nat_add 2 ];
      · norm_num [ Finset.sum_range_succ ] ; ring;
      · exact Real.summable_pow_div_factorial u;
    rw [ h_sum_bound, ← tsum_mul_left ];
    refine' Summable.tsum_le_tsum _ _ _;
    · intro i; rw [ div_pow ] ; rw [ div_mul_div_comm ] ; rw [ div_le_div_iff₀ ] <;> first | positivity | ring_nf;
      -- We'll use the fact that $3^i * 2 \leq (2 + i)!$ for all $i \geq 0$.
      have h_factorial : ∀ i : ℕ, 3^i * 2 ≤ (2 + i).factorial := by
        intro i; induction i <;> simp_all +decide [ Nat.factorial, pow_succ' ];
        nlinarith [ pow_pos ( by decide : 0 < 3 ) ‹_› ];
      nlinarith only [ show 0 ≤ u ^ 2 * u ^ i by positivity, show ( 3 ^ i * 2 : ℝ ) ≤ ( 2 + i ).factorial by exact_mod_cast h_factorial i ];
    · exact Real.summable_pow_div_factorial _ |> Summable.comp_injective <| Nat.succ_injective.comp <| Nat.succ_injective;
    · exact Summable.mul_left _ ( summable_geometric_of_lt_one ( by positivity ) ( by linarith ) );
  rw [ tsum_geometric_of_lt_one ( by positivity ) ( by linarith ) ] at h_sum_bound ; rw [ ← div_div ] ; aesop;

/-
For `u ≤ 0`: `exp(u) − 1 − u ≤ u²/2`.

Proof: Let `f(u) = exp(u) − 1 − u − u²/2`. Then `f(0) = 0`,
`f'(u) = exp(u) − 1 − u`, and for `u ≤ 0`, `f'(u) ≥ 0` (since
`exp(u) ≥ 1 + u`), so `f` is increasing on `(−∞, 0]`, hence
`f(u) ≤ f(0) = 0`.
-/
lemma exp_sub_one_sub_le_sq_nonpos {u : ℝ} (hu : u ≤ 0) :
    Real.exp u - 1 - u ≤ u ^ 2 / 2 := by
  -- Let $f(u) = \exp(u) - 1 - u - \frac{u^2}{2}$.
  set f : ℝ → ℝ := fun u => Real.exp u - 1 - u - u^2 / 2;
  -- We'll use the fact that $f(u)$ is differentiable and that its derivative is non-negative on $(-\infty, 0]$.
  have h_deriv_nonneg : ∀ u ≤ 0, 0 ≤ deriv f u := by
    norm_num +zetaDelta at *;
    exact fun u hu => by linarith [ Real.add_one_le_exp u ] ;
  by_contra h_contra;
  -- Apply the mean value theorem to $f$ on the interval $[u, 0]$.
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo u 0, deriv f c = (f 0 - f u) / (0 - u) := by
    apply_rules [ exists_deriv_eq_slope ];
    · exact hu.lt_of_ne ( by rintro rfl; norm_num at h_contra );
    · fun_prop;
    · fun_prop;
  norm_num +zetaDelta at *;
  rw [ eq_div_iff ] at hc <;> nlinarith [ h_deriv_nonneg c hc.1.2.le ]

/-
Combined pointwise bound for the Bernstein–Bennett MGF argument:
for `|x| ≤ b`, `λ ≥ 0`, `bλ < 3`:
`exp(λx) ≤ 1 + λx + (λx)² / (2(1 − bλ/3))`.
-/
lemma exp_mul_le_one_add_add_sq_div {x b lam : ℝ}
    (hb : 0 ≤ b) (hx : |x| ≤ b) (hlam : 0 ≤ lam) (hbl : b * lam < 3) :
    Real.exp (lam * x) ≤
      1 + lam * x + (lam * x) ^ 2 / (2 * (1 - b * lam / 3)) := by
  by_cases h_case : lam * x ≥ 0;
  · have := exp_sub_one_sub_le_sq_div_nonneg h_case ?_;
    · rw [ le_div_iff₀ ] at *;
      · rw [ add_div', le_div_iff₀ ] <;> nlinarith [ mul_le_mul_of_nonneg_left ( show x ≤ b by linarith [ abs_le.mp hx ] ) hlam ];
      · nlinarith [ abs_le.mp hx ];
    · nlinarith [ abs_le.mp hx ];
  · have := exp_sub_one_sub_le_sq_nonpos ( by linarith : lam * x ≤ 0 );
    rw [ add_div', le_div_iff₀ ] <;> nlinarith [ mul_nonneg hlam ( sq_nonneg ( lam * x ) ) ]

/-! ## Integration step -/

/-
Integrability of `exp(λ X)` for bounded `X` on a probability space.
-/
lemma integrable_exp_mul_of_bounded
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {b lam : ℝ}
    (hX_meas : Measurable X)
    (h_bounded : ∀ᵐ ω ∂μ, |X ω| ≤ b) :
    Integrable (fun ω => Real.exp (lam * X ω)) μ := by
  refine' MeasureTheory.Integrable.mono' ( MeasureTheory.integrable_const ( Real.exp ( |lam| * b ) ) ) _ _;
  · exact Real.continuous_exp.comp_aestronglyMeasurable ( hX_meas.aestronglyMeasurable.const_mul _ );
  · filter_upwards [ h_bounded ] with ω hω using by simpa using Real.exp_le_exp.2 ( by cases abs_cases lam <;> nlinarith [ abs_le.mp hω ] ) ;

/-! ## Main theorem -/

/-
**Bernstein–Bennett MGF bound.**

For `X : Ω → ℝ` measurable with `|X| ≤ b` a.s., `∫ X ∂μ = 0`,
`∫ X² ∂μ ≤ σ²`, `λ ≥ 0`, and `b · λ < 3`:

    mgf X μ λ ≤ exp(σ² · λ² / (2 · (1 − b · λ / 3))).
-/
theorem mgf_le_subGamma_of_bounded
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {b σ_sq : ℝ}
    (hX_meas : Measurable X)
    (hb : 0 ≤ b)
    (h_bounded : ∀ᵐ ω ∂μ, |X ω| ≤ b)
    (h_centered : ∫ ω, X ω ∂μ = 0)
    (h_var : ∫ ω, (X ω) ^ 2 ∂μ ≤ σ_sq)
    {lam : ℝ} (hlam : 0 ≤ lam) (hbl : b * lam < 3) :
    mgf X μ lam ≤ Real.exp (σ_sq * lam ^ 2 / (2 * (1 - b * lam / 3))) := by
  refine' le_trans _ ( Real.add_one_le_exp _ );
  -- Apply the pointwise bound `exp_mul_le_one_add_add_sq_div` to each term in the integral.
  have h_integral_bound : ∫ ω, Real.exp (lam * X ω) ∂μ ≤ ∫ ω, (1 + lam * X ω + (lam * X ω) ^ 2 / (2 * (1 - b * lam / 3))) ∂μ := by
    refine' MeasureTheory.integral_mono_of_nonneg _ _ _;
    · exact Filter.Eventually.of_forall fun ω => Real.exp_nonneg _;
    · apply_rules [ MeasureTheory.Integrable.add, MeasureTheory.Integrable.div_const, MeasureTheory.Integrable.const_mul ];
      · norm_num;
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        exacts [ fun ω => b, MeasureTheory.integrable_const _, hX_meas.aestronglyMeasurable, h_bounded ];
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun ω => ( lam * b ) ^ 2;
        · fun_prop;
        · exact MeasureTheory.AEStronglyMeasurable.pow ( MeasureTheory.AEStronglyMeasurable.const_mul ( hX_meas.aestronglyMeasurable ) _ ) _;
        · filter_upwards [ h_bounded ] with ω hω using by simpa [ abs_mul, abs_of_nonneg hlam ] using pow_le_pow_left₀ ( by positivity ) ( mul_le_mul_of_nonneg_left hω hlam ) 2;
    · filter_upwards [ h_bounded ] with ω hω using exp_mul_le_one_add_add_sq_div hb hω hlam hbl;
  refine' le_trans h_integral_bound _;
  rw [ MeasureTheory.integral_add, MeasureTheory.integral_add ] <;> norm_num [ MeasureTheory.integral_const_mul, h_centered ];
  · simp +decide [ mul_pow, MeasureTheory.integral_div, MeasureTheory.integral_const_mul, add_comm ];
    exact div_le_div_of_nonneg_right ( by nlinarith ) ( mul_nonneg zero_le_two ( by nlinarith ) );
  · refine' MeasureTheory.Integrable.const_mul _ _;
    refine' MeasureTheory.Integrable.mono' _ _ _;
    exacts [ fun ω => b, MeasureTheory.integrable_const _, hX_meas.aestronglyMeasurable, h_bounded ];
  · refine' MeasureTheory.Integrable.const_mul _ _;
    refine' MeasureTheory.Integrable.mono' _ _ _;
    exacts [ fun ω => b, MeasureTheory.integrable_const _, hX_meas.aestronglyMeasurable, h_bounded ];
  · refine' MeasureTheory.Integrable.div_const _ _;
    refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun ω => ( lam * b ) ^ 2;
    · exact MeasureTheory.integrable_const _;
    · exact MeasureTheory.AEStronglyMeasurable.pow ( MeasureTheory.AEStronglyMeasurable.const_mul ( hX_meas.aestronglyMeasurable ) _ ) _;
    · filter_upwards [ h_bounded ] with ω hω using by simpa [ abs_mul, abs_of_nonneg hlam ] using pow_le_pow_left₀ ( by positivity ) ( mul_le_mul_of_nonneg_left hω hlam ) 2;

end Pythia