/-
Pythia.Concentration — Sub-Gaussian concentration inequalities.

Hoeffding's inequality, Bennett's inequality, and sub-exponential
tail bounds. Each theorem decomposes into standalone lemmas suitable
for independent Rust crate verification:
  (1) MGF existence under boundedness/moment conditions
  (2) Exponential Markov inequality application
  (3) Optimization over the tilting parameter λ

All proofs are original, building on Pythia.SubGamma and Mathlib.
-/
import Mathlib
import Pythia.Basic
import Pythia.SubGamma

namespace Pythia.Concentration

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-! ## Section 1 — MGF existence lemmas -/

/-- MGF of a bounded random variable exists for all λ. -/
theorem mgf_exists_of_bounded
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X)
    {a b : ℝ} (hab : a ≤ b)
    (h_bounded : ∀ᵐ ω ∂μ, a ≤ X ω ∧ X ω ≤ b)
    (lam : ℝ) :
    Integrable (fun ω => Real.exp (lam * X ω)) μ := by
  refine Integrable.mono' (f := fun _ => Real.exp (|lam| * b.max (-a))) ?_ ?_ ?_
  · exact integrable_const _
  · exact (hX.const_mul lam).exp.aestronglyMeasurable
  · filter_upwards [h_bounded] with ω ⟨ha, hb⟩
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by nlinarith [abs_nonneg lam])

/-- MGF of a centered bounded variable is bounded by the sub-Gaussian form. -/
theorem mgf_le_subGaussian_of_bounded
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X)
    {a b : ℝ} (hab : a < b)
    (h_bounded : ∀ᵐ ω ∂μ, a ≤ X ω ∧ X ω ≤ b)
    (h_mean : ∫ ω, X ω ∂μ = 0)
    (lam : ℝ) :
    ∫ ω, Real.exp (lam * X ω) ∂μ ≤
      Real.exp (lam ^ 2 * (b - a) ^ 2 / 8) := by
  -- Hoeffding's lemma: for X ∈ [a,b] with E[X]=0,
  -- E[exp(λX)] ≤ exp(λ²(b-a)²/8).
  -- Proof via convexity of exp on [a,b] + Jensen optimality.
  have h_int := mgf_exists_of_bounded hX hab.le h_bounded lam
  have h_ba_pos : (0 : ℝ) < b - a := sub_pos.mpr hab
  by_cases hlam : lam = 0
  · simp [hlam]
  · -- By convexity of exp on [a,b]:
    -- For x ∈ [a,b]: exp(λx) ≤ ((b-x)/(b-a))·exp(λa) + ((x-a)/(b-a))·exp(λb)
    have h_convex_bound : ∀ᵐ ω ∂μ,
        Real.exp (lam * X ω) ≤
          ((b - X ω) / (b - a)) * Real.exp (lam * a) +
          ((X ω - a) / (b - a)) * Real.exp (lam * b) := by
      filter_upwards [h_bounded] with ω ⟨ha_ω, hb_ω⟩
      have h_convex := Real.convexOn_exp.2 (Set.mem_Icc.mpr ⟨le_refl a, hab.le⟩)
        (Set.mem_Icc.mpr ⟨hab.le, le_refl b⟩)
        (show (b - X ω) / (b - a) ≥ 0 by positivity)
        (show (X ω - a) / (b - a) ≥ 0 by positivity)
        (show (b - X ω) / (b - a) + (X ω - a) / (b - a) = 1 by field_simp)
      convert h_convex using 1
      · congr 1; field_simp; ring
      · congr 1 <;> (congr 1; ring)
    -- Take expectation of the convex bound
    have h_integral_bound :
        ∫ ω, Real.exp (lam * X ω) ∂μ ≤
          (b / (b - a)) * Real.exp (lam * a) +
          (-a / (b - a)) * Real.exp (lam * b) := by
      calc ∫ ω, Real.exp (lam * X ω) ∂μ
          ≤ ∫ ω, (((b - X ω) / (b - a)) * Real.exp (lam * a) +
                   ((X ω - a) / (b - a)) * Real.exp (lam * b)) ∂μ :=
            MeasureTheory.integral_mono_ae h_int
              (by exact Integrable.add (Integrable.const_mul (integrable_const _) _)
                                       (Integrable.const_mul h_int _) |>.mono_ae
                (by filter_upwards [h_bounded] with ω ⟨ha_ω, hb_ω⟩; positivity))
              h_convex_bound
        _ = (b / (b - a)) * Real.exp (lam * a) +
            (-a / (b - a)) * Real.exp (lam * b) := by
          simp_rw [MeasureTheory.integral_add
            (Integrable.const_mul (integrable_const _) _)
            (Integrable.const_mul h_int _)]
          simp_rw [MeasureTheory.integral_mul_right, MeasureTheory.integral_div]
          rw [show ∫ ω, (b - X ω) ∂μ = b - ∫ ω, X ω ∂μ from by
            simp [MeasureTheory.integral_sub (integrable_const _) (h_int.mono_ae (by
              filter_upwards [h_bounded] with ω ⟨ha_ω, hb_ω⟩; exact ⟨_, _⟩ <;> nlinarith)),
              MeasureTheory.integral_const, MeasureTheory.IsProbabilityMeasure.measure_univ]]
          rw [show ∫ ω, (X ω - a) ∂μ = (∫ ω, X ω ∂μ) - a from by
            simp [MeasureTheory.integral_sub (h_int.mono_ae (by
              filter_upwards [h_bounded] with ω ⟨ha_ω, hb_ω⟩; exact ⟨_, _⟩ <;> nlinarith))
              (integrable_const _),
              MeasureTheory.integral_const, MeasureTheory.IsProbabilityMeasure.measure_univ]]
          rw [h_mean]; ring_nf
    -- Now use the cosh bound: (b/(b-a))e^{λa} + (-a/(b-a))e^{λb} ≤ e^{λ²(b-a)²/8}
    -- This follows from: let p = -a/(b-a), h = λ(b-a), then
    -- (1-p)e^{λa} + pe^{λb} = e^{λa}(1-p+pe^h) and
    -- log(1-p+pe^h) - ph ≤ h²/8 (proved by Taylor with f''≤1/4)
    calc ∫ ω, Real.exp (lam * X ω) ∂μ
        ≤ (b / (b - a)) * Real.exp (lam * a) +
          (-a / (b - a)) * Real.exp (lam * b) := h_integral_bound
      _ ≤ Real.exp (lam ^ 2 * (b - a) ^ 2 / 8) := by
        -- The algebraic inequality (b/(b-a))e^{λa} + (-a/(b-a))e^{λb} ≤ e^{λ²(b-a)²/8}
        -- This is the core "cosh bound" and requires a separate lemma.
        -- For now we leave this final algebraic step.
        sorry

/-! ## Section 2 — Exponential Markov inequality -/

/-- Exponential Markov: Pr(X ≥ t) ≤ exp(-λt) · E[exp(λX)] for λ > 0. -/
theorem exponential_markov
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X)
    (h_int : Integrable (fun ω => Real.exp (lam * X ω)) μ)
    {lam : ℝ} (hlam : 0 < lam)
    (t : ℝ) :
    μ {ω | X ω ≥ t} ≤
      ENNReal.ofReal (Real.exp (-lam * t) *
        ∫ ω, Real.exp (lam * X ω) ∂μ) := by
  -- Standard: {X ≥ t} = {exp(λX) ≥ exp(λt)}, apply Markov.
  have h_eq : {ω | X ω ≥ t} = {ω | Real.exp (lam * X ω) ≥ Real.exp (lam * t)} := by
    ext ω; simp [Real.exp_le_exp, mul_le_mul_left hlam]
  rw [h_eq]
  have h_markov := @MeasureTheory.meas_ge_le_integral_div μ
    (fun ω => Real.exp (lam * X ω)) (Real.exp (lam * t)) ?_ ?_ ?_
  · convert ENNReal.ofReal_le_ofReal ?_ using 1
    · simp [measureReal_def]
    · rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
      ring_nf
      exact le_refl _
  · exact Real.exp_pos _
  · exact h_int
  · filter_upwards with ω; exact (Real.exp_pos _).le

/-! ## Section 3 — Hoeffding's inequality -/

/-- **Hoeffding's inequality** for independent bounded random variables.

For independent X_i ∈ [a_i, b_i] with E[X_i] = μ_i,
  Pr(S_n - E[S_n] ≥ t) ≤ exp(-2t² / Σ(b_i - a_i)²)

Decomposition: MGF existence (Section 1) + sub-Gaussian MGF bound
(Hoeffding's lemma) + exponential Markov (Section 2) + λ optimization. -/
theorem hoeffding_iid
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {a b : ℝ} (hab : a < b)
    (hX_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ)
    (h_bounded : ∀ i, ∀ᵐ ω ∂μ, a ≤ X i ω ∧ X i ω ≤ b)
    (h_zero_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    μ {ω | (Finset.range n).sum (fun i => X i ω) ≥ t} ≤
      ENNReal.ofReal (Real.exp (-2 * t ^ 2 / (↑n * (b - a) ^ 2))) := by
  -- Step 1: MGF of sum factorizes by independence
  -- Step 2: Each factor bounded by sub-Gaussian form (Hoeffding's lemma)
  -- Step 3: Product gives exp(λ² · n · (b-a)² / 8)
  -- Step 4: Apply exponential Markov with the product bound
  -- Step 5: Optimize λ* = 4t / (n(b-a)²), yielding the Hoeffding rate
  sorry

/-! ## Section 4 — Bennett's inequality -/

/-- **Bennett's inequality** for bounded centered independent variables.

Tighter than Bernstein when variance is much smaller than the range.
For |X_i| ≤ b, E[X_i] = 0, Var(X_i) ≤ σ²:
  Pr(S_n ≥ t) ≤ exp(-nσ²/b² · h(bt/(nσ²)))
where h(u) = (1+u)log(1+u) - u is the Bennett function. -/
theorem bennett
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {b sigma_sq : ℝ}
    (hb_pos : 0 < b) (hsigma_pos : 0 < sigma_sq)
    (hX_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ)
    (h_bounded : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b)
    (h_zero_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (h_var : ∀ i, ∫ ω, (X i ω) ^ 2 ∂μ ≤ sigma_sq)
    (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    μ {ω | (Finset.range n).sum (fun i => X i ω) ≥ t} ≤
      ENNReal.ofReal (Real.exp (-(↑n * sigma_sq / b ^ 2) *
        ((1 + b * t / (↑n * sigma_sq)) *
          Real.log (1 + b * t / (↑n * sigma_sq)) -
          b * t / (↑n * sigma_sq)))) := by
  -- Bennett uses the tighter MGF bound:
  -- E[exp(λX)] ≤ exp(σ²/b² · (exp(λb) - λb - 1))
  -- Combined with exponential Markov and optimized λ*.
  sorry

/-! ## Section 5 — Sub-exponential tail bounds -/

/-- A random variable is sub-exponential with parameters (ν², α) if its
MGF satisfies E[exp(λX)] ≤ exp(ν²λ²/2) for |λ| < 1/α. -/
def IsSubExponential
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    (X : Ω → ℝ) (nu_sq alpha : ℝ) : Prop :=
  0 < alpha ∧ 0 ≤ nu_sq ∧
  ∀ lam : ℝ, |lam| < 1 / alpha →
    Integrable (fun ω => Real.exp (lam * X ω)) μ ∧
    ∫ ω, Real.exp (lam * X ω) ∂μ ≤ Real.exp (nu_sq * lam ^ 2 / 2)

/-- **Bernstein condition implies sub-exponential.**
If |X| ≤ b a.s. and E[X] = 0, then X is sub-exponential with
parameters (Var(X), b/3). -/
theorem bounded_is_subExponential
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X)
    {b : ℝ} (hb : 0 < b)
    (h_bounded : ∀ᵐ ω ∂μ, |X ω| ≤ b)
    (h_mean : ∫ ω, X ω ∂μ = 0)
    (sigma_sq : ℝ) (h_var : ∫ ω, (X ω) ^ 2 ∂μ ≤ sigma_sq) :
    IsSubExponential μ X sigma_sq (b / 3) := by
  sorry

/-- **Sub-exponential tail bound** (Bernstein-type).
For sub-exponential X with parameters (ν², α):
  Pr(X ≥ t) ≤ exp(-min(t²/(2ν²), t/(2α)))
This gives Gaussian tails for small t and exponential tails for large t. -/
theorem subExponential_tail
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X)
    {nu_sq alpha : ℝ}
    (h_subexp : IsSubExponential μ X nu_sq alpha)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | X ω ≥ t} ≤
      ENNReal.ofReal (Real.exp (-min (t ^ 2 / (2 * nu_sq))
                                     (t / (2 * alpha)))) := by
  sorry

end Pythia.Concentration
