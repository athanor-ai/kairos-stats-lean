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

/-! ## Cosh bound (Hoeffding's key inequality) -/

/--
The second derivative of `f(h) = log(1-p+p·exp(h)) - p·h` is bounded by 1/4.
Specifically: `p(1-p)·exp(h) / (1-p+p·exp(h))² ≤ 1/4`.
This holds because for any `x, y ≥ 0`: `xy/(x+y)² ≤ 1/4`.
Here `x = (1-p)·exp(-h/2)²` and `y = p·exp(h/2)²` (after rescaling).
-/
private lemma hoeffding_f_snd_deriv_le (p h : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * (1 - p) * Real.exp h / (1 - p + p * Real.exp h) ^ 2 ≤ 1 / 4 := by
  have h_mixture_pos : (0 : ℝ) < 1 - p + p * Real.exp h := by
    nlinarith [Real.exp_pos h]
  -- Use AM-GM: for a,b ≥ 0, ab ≤ (a+b)²/4
  -- Here a = (1-p), b = p·exp(h), so a·b = p(1-p)·exp(h) and a+b = 1-p+p·exp(h)
  have h_sq_pos : (0 : ℝ) < (1 - p + p * Real.exp h) ^ 2 := by positivity
  rw [div_le_div_iff₀ h_sq_pos (by positivity : (0 : ℝ) < (4 : ℝ))]
  -- Need: 4 * (p * (1-p) * exp(h)) ≤ 1 * (1-p+p·exp(h))²
  -- This is 4ab ≤ (a+b)² where a = 1-p, b = p·exp(h)
  nlinarith [sq_nonneg (1 - p - p * Real.exp h), Real.exp_pos h]

/--
Taylor-based bound: `f(h) = log(1-p+p·exp(h)) - p·h ≤ h²/8`.

Proved via concavity: let `g(t) = f(t) - t²/8`. Then `g(0) = 0`, `g'(0) = 0`,
and `g''(t) = f''(t) - 1/4 ≤ 0` (by `hoeffding_f_snd_deriv_le`), so `g` is concave.
Since `g'` is antitone with `g'(0) = 0`, `g` is maximized at 0, giving `g(h) ≤ 0`.
-/
private lemma hoeffding_log_bound (p h : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.log (1 - p + p * Real.exp h) - p * h ≤ h ^ 2 / 8 := by
  -- Define g(t) = log(1-p+p·exp(t)) - p·t - t²/8. We show g(h) ≤ 0.
  -- Key facts: g(0) = 0, g'(0) = 0, g''(t) = f''(t) - 1/4 ≤ 0 (so g is concave).
  -- A concave function with g(0) = g'(0) = 0 satisfies g ≤ 0 everywhere.
  -- Proof: g' is antitone (g concave), g'(0)=0, so g'≤0 on [0,∞) and g'≥0 on (-∞,0].
  -- Hence g is non-increasing on [0,∞) and non-decreasing on (-∞,0], maximized at 0.
  suffices h_suffices : Real.log (1 - p + p * Real.exp h) - p * h - h ^ 2 / 8 ≤ 0 by linarith
  -- Let g(t) = log(1-p+p*exp(t)) - p*t - t²/8
  set g : ℝ → ℝ := fun t => Real.log (1 - p + p * Real.exp t) - p * t - t ^ 2 / 8
  -- The mixture 1-p+p*exp(t) is always positive
  have h_mix_pos : ∀ t, (0 : ℝ) < 1 - p + p * Real.exp t :=
    fun t => by nlinarith [Real.exp_pos t]
  -- g is differentiable (needed for antitoneOn_of_deriv_nonpos)
  have hg_diff : Differentiable ℝ g := by
    intro t
    have h_pos := h_mix_pos t
    have h_inner_diff : DifferentiableAt ℝ (fun x => 1 - p + p * Real.exp x) t :=
      (differentiableAt_const (1 - p)).add ((differentiableAt_const p).mul differentiableAt_exp)
    apply DifferentiableAt.sub
    · apply DifferentiableAt.sub
      · exact h_inner_diff.log h_pos.ne'
      · exact (differentiableAt_const p).mul differentiableAt_id'
    · exact (differentiableAt_pow 2).div_const 8
  -- g'(t) = p·exp(t)/(1-p+p·exp(t)) - p - t/4
  have hg_deriv : ∀ t, HasDerivAt g
      (p * Real.exp t / (1 - p + p * Real.exp t) - p - t / 4) t := by
    intro t
    have h_pos := h_mix_pos t
    have h_ne : (1 : ℝ) - p + p * Real.exp t ≠ 0 := h_pos.ne'
    have hd1 : HasDerivAt (fun x => 1 - p + p * Real.exp x) (p * Real.exp t) t :=
      ((hasDerivAt_exp t).const_mul p).const_add (1 - p)
    have hd2 : HasDerivAt (fun x => Real.log (1 - p + p * Real.exp x))
        (p * Real.exp t / (1 - p + p * Real.exp t)) t :=
      hd1.log h_ne
    have hd3 : HasDerivAt (fun x => p * x) p t := hasDerivAt_const_mul p
    have hd4 : HasDerivAt (fun x => x ^ 2 / 8) (t / 4) t := by
      have h := (hasDerivAt_pow 2 t).div_const (8 : ℝ)
      convert h using 1; ring
    exact (hd2.sub hd3).sub hd4
  -- g(0) = 0
  have hg_zero : g 0 = 0 := by
    show Real.log (1 - p + p * Real.exp 0) - p * 0 - 0 ^ 2 / 8 = 0
    have : (1 : ℝ) - p + p * Real.exp 0 = 1 := by rw [Real.exp_zero]; ring
    rw [this, Real.log_one]; ring
  -- g'(0) = 0
  have hg'_zero : p * Real.exp 0 / (1 - p + p * Real.exp 0) - p - 0 / 4 = 0 := by
    have h0_pos : (0 : ℝ) < 1 - p + p * Real.exp 0 := h_mix_pos 0
    rw [Real.exp_zero] at h0_pos ⊢
    field_simp [show (1 : ℝ) - p + p * 1 ≠ 0 from by linarith]
    ring
  -- g' is differentiable (for deriv computation)
  have hg'_diff : Differentiable ℝ (deriv g) := by
    have hg'_eq : deriv g = fun t => p * Real.exp t / (1 - p + p * Real.exp t) - p - t / 4 := by
      ext t; exact (hg_deriv t).deriv
    rw [hg'_eq]
    intro t
    have h_pos := h_mix_pos t
    apply DifferentiableAt.sub
    · apply DifferentiableAt.sub
      · exact ((differentiableAt_const p).mul differentiableAt_exp).div
          ((differentiableAt_const (1 - p)).add
            ((differentiableAt_const p).mul differentiableAt_exp))
          h_pos.ne'
      · exact differentiableAt_const p
    · exact differentiableAt_id'.div_const 4
  -- g''(t) = f''(t) - 1/4 ≤ 0 for all t
  -- (f''(t) = p(1-p)exp(t)/(1-p+p·exp(t))² ≤ 1/4 by hoeffding_f_snd_deriv_le)
  have hg''_nonpos : ∀ t, deriv (deriv g) t ≤ 0 := by
    intro t
    -- g''(t) = d/dt [p·exp(t)/(1-p+p·exp(t)) - p - t/4]
    --        = p(1-p)·exp(t)/(1-p+p·exp(t))² - 1/4
    --        ≤ 0  (by hoeffding_f_snd_deriv_le)
    have hg'_eq : deriv g = fun t => p * Real.exp t / (1 - p + p * Real.exp t) - p - t / 4 := by
      ext t; exact (hg_deriv t).deriv
    rw [hg'_eq]
    have h_pos := h_mix_pos t
    -- The derivative of p·exp(t)/(1-p+p·exp(t)) is p(1-p)·exp(t)/(1-p+p·exp(t))²
    have hd_quot : HasDerivAt (fun x => p * Real.exp x / (1 - p + p * Real.exp x))
        (p * (1 - p) * Real.exp t / (1 - p + p * Real.exp t) ^ 2) t := by
      have hnum : HasDerivAt (fun x => p * Real.exp x) (p * Real.exp t) t :=
        (hasDerivAt_exp t).const_mul p
      have hden : HasDerivAt (fun x => 1 - p + p * Real.exp x) (p * Real.exp t) t :=
        ((hasDerivAt_exp t).const_mul p).const_add (1 - p)
      have := hnum.div hden h_pos.ne'
      convert this using 1
      field_simp [h_pos.ne']
      ring
    have hd_full : HasDerivAt (fun x => p * Real.exp x / (1 - p + p * Real.exp x) - p - x / 4)
        (p * (1 - p) * Real.exp t / (1 - p + p * Real.exp t) ^ 2 - 1 / 4) t := by
      have hd_const : HasDerivAt (fun _ : ℝ => p) 0 t := hasDerivAt_const t p
      have hd_lin : HasDerivAt (fun x : ℝ => x / 4) (1 / 4) t := by
        have h : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id' (𝕜 := ℝ)
        exact h.div_const 4
      convert (hd_quot.sub hd_const).sub hd_lin using 1; ring
    rw [hd_full.deriv]
    linarith [hoeffding_f_snd_deriv_le p t hp0 hp1]
  -- Now: g is concave on ℝ (g'' ≤ 0), so g' is antitone.
  -- g'(0) = 0, so g' ≤ 0 on [0, ∞) and g' ≥ 0 on (-∞, 0].
  -- This means g is non-increasing on [0, ∞) and non-decreasing on (-∞, 0].
  -- Combined with g(0) = 0, we get g(h) ≤ 0 for all h.
  have hg'_antitone : Antitone (deriv g) :=
    antitone_of_deriv_nonpos hg'_diff hg''_nonpos
  have hg'_eq_at_zero : deriv g 0 = 0 := by
    rw [(hg_deriv 0).deriv]; linarith [hg'_zero]
  -- For h ≥ 0: g'(h) ≤ g'(0) = 0 (antitone), so g is non-increasing on [0,∞)
  -- For h ≤ 0: g'(h) ≥ g'(0) = 0 (antitone), so g is non-decreasing on (-∞,0]
  -- In both cases g(h) ≤ g(0) = 0.
  rcases le_or_lt 0 h with hh | hh
  · -- Case h ≥ 0: g is antitone on [0, h], so g(h) ≤ g(0) = 0
    have hg_anti : AntitoneOn g (Set.Icc 0 h) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 h)
      · exact hg_diff.continuous.continuousOn
      · exact hg_diff.differentiableOn
      · intro x hx
        have hx_nn : 0 ≤ x := (interior_subset hx).1
        have : deriv g x ≤ deriv g 0 := hg'_antitone hx_nn
        linarith [hg'_eq_at_zero]
    have hh_mem : h ∈ Set.Icc 0 h := ⟨hh, le_refl _⟩
    have h0_mem : (0 : ℝ) ∈ Set.Icc 0 h := ⟨le_refl _, hh⟩
    have := hg_anti h0_mem hh_mem hh
    linarith [hg_zero]
  · -- Case h < 0: g is monotone on [h, 0], so g(h) ≤ g(0) = 0
    have hg_mono : MonotoneOn g (Set.Icc h 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc h 0)
      · exact hg_diff.continuous.continuousOn
      · exact hg_diff.differentiableOn
      · intro x hx
        have hx_le : x ≤ 0 := (interior_subset hx).2
        have : deriv g 0 ≤ deriv g x := hg'_antitone hx_le
        linarith [hg'_eq_at_zero]
    have hh_mem : h ∈ Set.Icc h 0 := ⟨le_refl _, hh.le⟩
    have h0_mem : (0 : ℝ) ∈ Set.Icc h 0 := ⟨hh.le, le_refl _⟩
    have := hg_mono hh_mem h0_mem hh.le
    linarith [hg_zero]

/--
**Hoeffding's cosh bound.** For `p ∈ [0,1]` and any `h : ℝ`:
  `(1 - p) · exp(-p · h) + p · exp((1-p) · h) ≤ exp(h² / 8)`.

This is the core analytic inequality in Hoeffding's lemma. It states
that the moment generating function of a Bernoulli(p) random variable
Y ∈ {0,1}, centered at its mean, is sub-Gaussian with parameter 1/8:
  `E[exp(h(Y - p))] = (1-p)exp(-ph) + p·exp((1-p)h) ≤ exp(h²/8)`.

Proof: factor out `exp(-ph)`, take logs, apply `hoeffding_log_bound`.
-/
lemma hoeffding_cosh_bound (p h : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * Real.exp (-p * h) + p * Real.exp ((1 - p) * h) ≤ Real.exp (h ^ 2 / 8) := by
  -- Factor: (1-p)·exp(-ph) + p·exp((1-p)h) = exp(-ph) · (1-p + p·exp(h))
  have h_factor : (1 - p) * Real.exp (-p * h) + p * Real.exp ((1 - p) * h) =
      Real.exp (-p * h) * (1 - p + p * Real.exp h) := by
    have : Real.exp ((1 - p) * h) = Real.exp (-p * h) * Real.exp h := by
      rw [← Real.exp_add]; ring_nf
    rw [this]; ring
  rw [h_factor]
  -- The mixture 1-p+p·exp(h) is positive
  have h_mixture_pos : (0 : ℝ) < 1 - p + p * Real.exp h := by
    nlinarith [Real.exp_pos h]
  -- Rewrite target: exp(-ph)·(1-p+p·exp(h)) ≤ exp(h²/8)
  -- ⟺ -ph + log(1-p+p·exp(h)) ≤ h²/8  (since both sides positive, take log)
  -- ⟺ log(1-p+p·exp(h)) - ph ≤ h²/8
  rw [show Real.exp (h ^ 2 / 8) = Real.exp (-p * h) * Real.exp (p * h + h ^ 2 / 8) from by
    rw [← Real.exp_add]; ring_nf]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  -- Suffices: 1 - p + p · exp(h) ≤ exp(p·h + h²/8)
  calc 1 - p + p * Real.exp h
      = Real.exp (Real.log (1 - p + p * Real.exp h)) :=
        (Real.exp_log h_mixture_pos).symm
    _ ≤ Real.exp (p * h + h ^ 2 / 8) := by
        apply Real.exp_le_exp.mpr
        linarith [hoeffding_log_bound p h hp0 hp1]

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
        -- Apply hoeffding_cosh_bound with p = -a/(b-a), h = lam*(b-a).
        set p' := -a / (b - a)
        set h' := lam * (b - a)
        have hp'_nn : 0 ≤ p' := by unfold_let p'; positivity
        have hp'_le : p' ≤ 1 := by
          unfold_let p'; rw [neg_div, div_le_one h_ba_pos]; linarith
        -- Show LHS equals the form expected by hoeffding_cosh_bound
        have h_lhs_eq : (b / (b - a)) * Real.exp (lam * a) +
            (-a / (b - a)) * Real.exp (lam * b) =
            (1 - p') * Real.exp (-p' * h') + p' * Real.exp ((1 - p') * h') := by
          unfold_let p' h'; field_simp; ring
        have h_rhs_eq : Real.exp (lam ^ 2 * (b - a) ^ 2 / 8) =
            Real.exp (h' ^ 2 / 8) := by
          unfold_let h'; ring_nf
        rw [h_lhs_eq, h_rhs_eq]
        exact hoeffding_cosh_bound p' h' hp'_nn hp'_le

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
  -- Step 1: Rewrite the set {X ≥ t} as {ofReal(exp(λX)) ≥ ofReal(exp(λt))}
  -- for the ENNReal-valued Markov inequality.
  have h_exp_t_pos : (0 : ℝ) < Real.exp (lam * t) := Real.exp_pos _
  have h_exp_pos : ∀ ω, (0 : ℝ) < Real.exp (lam * X ω) := fun ω => Real.exp_pos _
  -- The ENNReal-valued function
  set Y : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (lam * X ω))
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (lam * t))
  -- Set equality: {X ≥ t} = {c ≤ Y}
  have h_set_eq : {ω | X ω ≥ t} = {ω | c ≤ Y ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Y, c, ge_iff_le]
    rw [ENNReal.ofReal_le_ofReal_iff (h_exp_pos ω).le, Real.exp_le_exp,
        mul_le_mul_iff_of_pos_left hlam]
  rw [h_set_eq]
  -- Step 2: Apply Markov's inequality (ENNReal version)
  have hc_ne_zero : c ≠ 0 := by
    simp only [c]; exact ENNReal.ofReal_ne_zero_iff.mpr h_exp_t_pos
  have hc_ne_top : c ≠ ⊤ := by simp only [c]; exact ENNReal.ofReal_ne_top
  have hY_meas : AEMeasurable Y μ :=
    ((hX.const_mul lam).exp.ennreal_ofReal).aemeasurable
  -- meas_ge_le_lintegral_div: μ {x | c ≤ Y x} ≤ (∫⁻ a, Y a ∂μ) / c
  have h_markov := MeasureTheory.meas_ge_le_lintegral_div hY_meas hc_ne_zero hc_ne_top
  -- Step 3: Convert lintegral to Bochner integral and simplify
  -- ∫⁻ ω, Y ω ∂μ = ENNReal.ofReal (∫ ω, exp(lam * X ω) ∂μ)
  have h_nn : 0 ≤ᵐ[μ] (fun ω => Real.exp (lam * X ω)) :=
    Eventually.of_forall (fun ω => (h_exp_pos ω).le)
  have h_lintegral_eq : ∫⁻ ω, Y ω ∂μ = ENNReal.ofReal (∫ ω, Real.exp (lam * X ω) ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal h_int h_nn).symm
  -- Step 4: Combine and simplify
  calc μ {ω | c ≤ Y ω}
      ≤ (∫⁻ ω, Y ω ∂μ) / c := h_markov
    _ = ENNReal.ofReal (∫ ω, Real.exp (lam * X ω) ∂μ) / c := by
        rw [h_lintegral_eq]
    _ = ENNReal.ofReal ((∫ ω, Real.exp (lam * X ω) ∂μ) / Real.exp (lam * t)) := by
        simp only [c]
        exact (ENNReal.ofReal_div_of_pos h_exp_t_pos).symm
    _ = ENNReal.ofReal (Real.exp (-lam * t) * ∫ ω, Real.exp (lam * X ω) ∂μ) := by
        congr 1
        rw [neg_mul, Real.exp_neg, div_eq_inv_mul]

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
