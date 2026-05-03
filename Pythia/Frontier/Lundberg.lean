/-
Pythia.Lundberg — Lundberg's inequality (Cramér-Lundberg ruin bound)

Theorem: In the Cramér-Lundberg model with claim arrival rate `lam`, premium
rate `c`, and iid claim sizes `X_i ≥ 0`, if the adjustment coefficient `R > 0`
satisfies `lam * E[exp(R X) - 1] = R c`, then:

1. The ruin probability ψ(u) ≤ exp(-R u).
2. R is the unique positive solution of the adjustment equation.

The ruin bound uses Ville's inequality for nonneg supermartingales.
The uniqueness uses strict convexity of the exponential function.

References:
  - Lundberg (1932), "Some supplementary researches on the collective risk theory"
  - Asmussen–Albrecher, Ch. III
-/
import Mathlib
import Pythia.VilleSupermartingale

namespace Pythia

open MeasureTheory ProbabilityTheory Finset Real Filter

set_option maxHeartbeats 800000

/-! ## Part 1: Helper lemmas for the uniqueness of R -/

/-- The classical inequality `1 + x ≤ exp x` for all `x : ℝ`. -/
lemma one_add_le_exp (x : ℝ) : 1 + x ≤ exp x := by linarith [add_one_le_exp x]

/-- Strict monotonicity of the secant `(exp(r·x) - 1) / r` in `r > 0` for fixed `x > 0`.
    Derived from `strictConvexOn_exp` and `StrictConvexOn.secant_strict_mono`. -/
lemma secant_exp_strict_mono {x : ℝ} (hx : 0 < x) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (h : r₁ < r₂) :
    (exp (r₁ * x) - 1) / r₁ < (exp (r₂ * x) - 1) / r₂ := by
  have h_secant : (Real.exp (r₁ * x) - Real.exp 0) / (r₁ * x - 0) <
      (Real.exp (r₂ * x) - Real.exp 0) / (r₂ * x - 0) := by
    have h_secant : StrictConvexOn ℝ (Set.univ : Set ℝ) Real.exp := strictConvexOn_exp
    have := h_secant.secant_strict_mono (Set.mem_univ 0) (Set.mem_univ (r₁ * x))
      (Set.mem_univ (r₂ * x)) (by nlinarith) (by nlinarith) (by nlinarith)
    aesop
  convert mul_lt_mul_of_pos_right h_secant hx using 1 <;>
    norm_num [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, hx.ne']

/-- Weak monotonicity: `(exp(r₁·x) - 1) / r₁ ≤ (exp(r₂·x) - 1) / r₂`
    when `0 < r₁ ≤ r₂` and `x ≥ 0`. -/
lemma secant_exp_mono {x : ℝ} (hx : 0 ≤ x) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (h : r₁ ≤ r₂) :
    (exp (r₁ * x) - 1) / r₁ ≤ (exp (r₂ * x) - 1) / r₂ := by
  rcases h.eq_or_lt with rfl | hlt
  · rfl
  · rcases hx.eq_or_lt with rfl | hx_pos
    · norm_num
    · exact le_of_lt (secant_exp_strict_mono hx_pos hr₁ hr₂ hlt)

/-! ## Part 2: Uniqueness of the adjustment coefficient -/

/-- From the adjustment equation and positivity, X₀ is not a.e. zero. -/
lemma X_not_ae_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (lam : ℝ) (_hlam : 0 < lam)
    {X : Ω → ℝ}
    (_h_pos : ∀ ω, 0 ≤ X ω)
    (R : ℝ) (hR_pos : 0 < R)
    (hR_def : lam * (∫ ω, exp (R * X ω) - 1 ∂μ) = R * c) :
    ¬ (X =ᵐ[μ] 0) := by
  intro h
  rw [MeasureTheory.integral_eq_zero_of_ae] at hR_def
  · nlinarith
  · filter_upwards [h] with ω hω using by simp [hω]

/-
Derive integrability of `exp(r * X)` from the adjustment equation.
-/
lemma integrable_exp_of_adjustment
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (lam : ℝ) (hlam : 0 < lam)
    {X : Ω → ℝ}
    (r : ℝ) (hr : 0 < r)
    (h_adj : lam * (∫ ω, exp (r * X ω) - 1 ∂μ) = r * c) :
    Integrable (fun ω => exp (r * X ω)) μ := by
  by_contra h;
  rw [ MeasureTheory.integral_undef ] at h_adj;
  · nlinarith;
  · contrapose! h;
    convert h.add ( MeasureTheory.integrable_const 1 ) using 1 ; ext ; simp +decide

/-- Uniqueness of the adjustment coefficient: if `R'` and `R` both satisfy
    `lam * E[exp(r·X) - 1] = r·c` with `r > 0`, then `R' = R`.
    Uses the strict convexity of `exp`. -/
theorem adjustment_coeff_unique
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (lam : ℝ) (hlam : 0 < lam)
    {X : Ω → ℝ}
    (h_pos : ∀ ω, 0 ≤ X ω)
    (R : ℝ) (hR_pos : 0 < R)
    (hR_def : lam * (∫ ω, exp (R * X ω) - 1 ∂μ) = R * c)
    (h_int_R : Integrable (fun ω => exp (R * X ω)) μ)
    (R' : ℝ) (hR'_pos : 0 < R')
    (hR'_def : lam * (∫ ω, exp (R' * X ω) - 1 ∂μ) = R' * c)
    (h_int_R' : Integrable (fun ω => exp (R' * X ω)) μ) :
    R' = R := by
  wlog h_lt : R' < R generalizing R R'
  · grind +splitImp
  · have h_exp : ∀ᵐ ω ∂μ,
        (Real.exp (R * X ω) - 1) / R = (Real.exp (R' * X ω) - 1) / R' := by
      have h_exp : ∫ ω, ((Real.exp (R * X ω) - 1) / R -
          (Real.exp (R' * X ω) - 1) / R') ∂μ = 0 := by
        rw [MeasureTheory.integral_sub, MeasureTheory.integral_div,
          MeasureTheory.integral_div]
        · grind
        · exact (h_int_R.sub (integrable_const _)).div_const _
        · exact (h_int_R'.sub (integrable_const _)).div_const _
      rw [MeasureTheory.integral_eq_zero_iff_of_nonneg_ae] at h_exp
      · exact h_exp.mono fun ω hω => sub_eq_zero.mp hω
      · exact .of_forall fun ω => sub_nonneg_of_le <| secant_exp_mono (h_pos ω) hR'_pos hR_pos h_lt.le
      · exact ((h_int_R.sub (integrable_const _)).div_const _).sub
          ((h_int_R'.sub (integrable_const _)).div_const _)
    have h_X_zero : X =ᵐ[μ] 0 := by
      filter_upwards [h_exp] with ω hω
      by_contra hne
      exact absurd hω (ne_of_gt (secant_exp_strict_mono
        (lt_of_le_of_ne (h_pos ω) (Ne.symm hne)) hR'_pos hR_pos h_lt))
    exact absurd (X_not_ae_zero c hc lam hlam h_pos R hR_pos hR_def) (by aesop)

/-! ## Part 3: MGF bound for the ruin probability -/

/-- The exponential moment bound: `exp(-R c/lam) * (1 + R c/lam) ≤ 1`,
    which follows from `1 + x ≤ exp x`. -/
lemma mgf_net_loss_le_one
    (c : ℝ) (_hc : 0 < c) (lam : ℝ) (_hlam : 0 < lam)
    (R : ℝ) (_hR_pos : 0 < R) :
    exp (-(R * c / lam)) * (1 + R * c / lam) ≤ 1 := by
  nlinarith [Real.exp_pos (-(R * c / lam)), Real.exp_neg (R * c / lam),
    mul_inv_cancel₀ (ne_of_gt (Real.exp_pos (R * c / lam))),
    Real.add_one_le_exp (R * c / lam),
    Real.add_one_le_exp (-(R * c / lam))]

/-! ## Part 4: Ruin bound helper lemmas -/

/-
For each individual time `n`, the probability `P(S_n ≥ u)` is bounded by `exp(-R u)`.
    This follows from exponential Markov inequality and the MGF bound.
-/
lemma individual_ruin_bound
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (u : ℝ) (hu : 0 ≤ u)
    (c : ℝ) (hc : 0 < c)
    (lam : ℝ) (hlam : 0 < lam)
    {X : ℕ → Ω → ℝ}
    (h_iid : iIndepFun X μ)
    (h_dist : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (h_pos : ∀ i ω, 0 ≤ X i ω)
    (h_meas : ∀ i, Measurable (X i))
    (R : ℝ) (hR_pos : 0 < R)
    (hR_def : lam * (∫ ω, exp (R * X 0 ω) - 1 ∂μ) = R * c)
    (n : ℕ) :
    μ {ω | (∑ i ∈ range n, (X i ω - c / lam)) ≥ u} ≤
      ENNReal.ofReal (exp (-R * u)) := by
  -- By definition of `IdentDistrib`, we know that `X i` are identically distributed.
  have h_identical : ∀ i, ∫ ω, Real.exp (R * (X i ω - c / lam)) ∂μ = Real.exp (-R * c / lam) * (1 + R * c / lam) := by
    intro i
    have h_integrable : ∫ ω, Real.exp (R * (X i ω)) ∂μ = 1 + R * c / lam := by
      rw [ ← hR_def, mul_div_cancel_left₀ _ hlam.ne', add_comm ];
      rw [ MeasureTheory.integral_sub ] <;> norm_num;
      · exact h_dist i |> fun h => h.comp ( measurable_id'.const_mul R |> Measurable.exp ) |> fun h => h.integral_eq;
      · contrapose! hR_def;
        rw [ MeasureTheory.integral_undef ];
        · nlinarith;
        · intro h_integrable
          have h_integrable_exp : Integrable (fun ω => Real.exp (R * X 0 ω)) μ := by
            convert h_integrable.add ( MeasureTheory.integrable_const 1 ) using 1 ; ext ; simp +decide [ Real.exp_ne_zero ]
          contradiction;
    rw [ ← h_integrable, ← MeasureTheory.integral_const_mul ] ; congr ; ext ω ; rw [ ← Real.exp_add ] ; ring;
  -- By independence, we have $\mathbb{E}[\exp(RS_n)] = \prod_{i=0}^{n-1} \mathbb{E}[\exp(R(X_i - c/lam))]$.
  have h_indep : ∫ ω, Real.exp (R * ∑ i ∈ Finset.range n, (X i ω - c / lam)) ∂μ = (∫ ω, Real.exp (R * (X 0 ω - c / lam)) ∂μ) ^ n := by
    have h_indep : ∀ (n : ℕ) (f : ℕ → Ω → ℝ), (∀ i, Measurable (f i)) → (∀ i, Integrable (fun ω => Real.exp (R * f i ω)) μ) → (iIndepFun f μ) → (∫ ω, Real.exp (R * ∑ i ∈ Finset.range n, f i ω) ∂μ) = (∏ i ∈ Finset.range n, ∫ ω, Real.exp (R * f i ω) ∂μ) := by
      intro n f hf_meas hf_int hf_indep
      have h_indep : ∀ (s : Finset ℕ), ∫ ω, ∏ i ∈ s, Real.exp (R * f i ω) ∂μ = ∏ i ∈ s, ∫ ω, Real.exp (R * f i ω) ∂μ := by
        intro s;
        induction' s using Finset.induction with i s hi ih;
        · simp +decide;
        · simp +decide [ *, Finset.prod_insert hi ];
          rw [ ← ih, ← ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral ];
          · rfl;
          · have := hf_indep.indepFun_finset s;
            specialize this { i } ; simp_all +decide [ ProbabilityTheory.IndepFun ];
            rw [ Kernel.indepFun_iff_measure_inter_preimage_eq_mul ] at *;
            intro s_1 t hs_1 ht; specialize this ( ( fun x => ∏ i : s, Real.exp ( R * x i ) ) ⁻¹' t ) ( ( fun x => Real.exp ( R * x ⟨ i, by simp +decide ⟩ ) ) ⁻¹' s_1 ) ; simp_all +decide [ Set.preimage ] ;
            convert this _ _ using 1;
            · simp +decide [ Finset.prod_attach, Set.inter_comm ];
              congr! 3;
              ext x; rw [ ← Finset.prod_attach ] ;
            · rw [ mul_comm ];
              congr! 2;
              ext x; simp +decide [ Finset.prod_attach ] ;
              conv_lhs => rw [ ← Finset.prod_attach ] ;
            · exact measurableSet_preimage ( Finset.measurable_prod _ fun _ _ => Measurable.exp ( measurable_const.mul ( measurable_pi_apply _ ) ) ) ht |> MeasurableSet.mem;
            · exact measurableSet_preimage ( measurable_id'.comp ( measurable_const.mul ( measurable_pi_apply _ ) ) |> Measurable.exp ) hs_1 |> MeasurableSet.mem;
          · exact ( hf_int i |> MeasureTheory.Integrable.aestronglyMeasurable );
          · fun_prop;
      convert h_indep ( Finset.range n ) using 3 ; simp +decide [ ← Real.exp_sum, Finset.mul_sum _ _ _ ];
    convert h_indep n ( fun i ω => X i ω - c / lam ) ( fun i => Measurable.sub ( h_meas i ) measurable_const ) ( fun i => ?_ ) ( ?_ ) using 1;
    · aesop;
    · exact ( by by_contra h; specialize h_identical i; rw [ MeasureTheory.integral_undef h ] at h_identical; exact absurd h_identical ( by positivity ) );
    · rw [ iIndepFun_iff_measure_inter_preimage_eq_mul ] at *;
      intro S sets hsets; convert h_iid S ( fun i hi => MeasurableSet.preimage ( hsets i hi ) ( measurable_id.sub measurable_const ) ) using 1;
  -- By Markov's inequality, we have $\mathbb{P}(S_n \geq u) \leq \frac{\mathbb{E}[\exp(RS_n)]}{\exp(Ru)}$.
  have h_markov : μ {ω | ∑ i ∈ Finset.range n, (X i ω - c / lam) ≥ u} ≤ ENNReal.ofReal ((∫ ω, Real.exp (R * ∑ i ∈ Finset.range n, (X i ω - c / lam)) ∂μ) / Real.exp (R * u)) := by
    have h_markov : ∀ {Y : Ω → ℝ}, (∀ ω, 0 ≤ Y ω) → MeasureTheory.Integrable Y μ → ∀ ε > 0, μ {ω | Y ω ≥ ε} ≤ ENNReal.ofReal ((∫ ω, Y ω ∂μ) / ε) := by
      intro Y hY_nonneg hY_integrable ε hε_pos;
      have := @MeasureTheory.mul_meas_ge_le_integral_of_nonneg Ω mΩ μ Y;
      rw [ ENNReal.le_ofReal_iff_toReal_le ] <;> norm_num;
      · rw [ le_div_iff₀' hε_pos ] ; specialize this ( Filter.Eventually.of_forall hY_nonneg ) hY_integrable ε ; aesop;
      · exact div_nonneg ( MeasureTheory.integral_nonneg hY_nonneg ) hε_pos.le;
    convert h_markov _ _ ( Real.exp ( R * u ) ) ( Real.exp_pos _ ) using 1;
    · simp +decide [ Real.exp_le_exp, mul_le_mul_iff_right₀ hR_pos ];
    · exact fun ω => Real.exp_nonneg _;
    · contrapose! h_indep;
      rw [ MeasureTheory.integral_undef h_indep ] ; norm_num [ h_identical ];
      exact ne_of_lt ( pow_pos ( mul_pos ( Real.exp_pos _ ) ( add_pos_of_pos_of_nonneg zero_lt_one ( div_nonneg ( mul_nonneg hR_pos.le hc.le ) hlam.le ) ) ) _ );
  simp_all +decide [ neg_div, Real.exp_neg ];
  refine' h_markov.trans ( ENNReal.ofReal_le_ofReal _ );
  exact mul_le_of_le_one_left ( by positivity ) ( pow_le_one₀ ( by positivity ) ( by rw [ inv_mul_le_iff₀ ( by positivity ) ] ; linarith [ Real.add_one_le_exp ( R * c / lam ) ] ) )

/-- The ruin event `{∃ n, S_n ≥ u}` is the monotone union of `{∃ k ≤ n, S_k ≥ u}`. -/
lemma ruin_event_eq_union
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X : ℕ → Ω → ℝ) (c lam u : ℝ) :
    {ω : Ω | ∃ n : ℕ, (∑ i ∈ range n, (X i ω - c / lam)) ≥ u} =
    ⋃ n : ℕ, {ω | (∑ i ∈ range n, (X i ω - c / lam)) ≥ u} := by
  ext ω; simp

/-
The exponential process `M_n = exp(R * S_n^Y)` is a supermartingale with respect
    to a suitable filtration (the "shifted" natural filtration where
    `𝔾_n = σ(X_0, ..., X_{n-1})`), via the standard exponential
    tilting argument.

    This is the core measure-theoretic step of Lundberg's inequality.
    The proof constructs a shifted filtration `𝔾` where `𝔾_n = σ(X_0,...,X_{n-1})`
    (one step behind the natural filtration) so that M_n is 𝔾_n-adapted
    and the next increment `exp(R·Y_n)` is independent of `𝔾_n`.
    The supermartingale property then follows from `E[exp(R·Y)] ≤ 1`.
-/
lemma exp_process_supermartingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (lam : ℝ) (hlam : 0 < lam)
    {X : ℕ → Ω → ℝ}
    (h_iid : iIndepFun X μ)
    (h_dist : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (h_meas : ∀ i, Measurable (X i))
    (R : ℝ) (hR_pos : 0 < R)
    (hR_def : lam * (∫ ω, exp (R * X 0 ω) - 1 ∂μ) = R * c) :
    let M : ℕ → Ω → ℝ := fun n ω => exp (R * ∑ i ∈ range n, (X i ω - c / lam))
    ∃ 𝔾 : Filtration ℕ mΩ, Supermartingale M 𝔾 μ := by
  intro M
  -- Define the shifted natural filtration: 𝔾_n = σ(X_0, ..., X_{n-1})
  set 𝔾 : Filtration ℕ mΩ := ⟨
    fun n => ⨆ (j : ℕ) (_ : j < n), MeasurableSpace.comap (X j) inferInstance,
    fun _ _ hmn => biSup_mono fun _ hj => lt_of_lt_of_le hj hmn,
    fun _ => iSup₂_le fun j _ => MeasurableSpace.comap_le_iff_le_map.mpr (h_meas j)⟩ with h𝔾
  -- Key fact: X j is measurable w.r.t. 𝔾 n when j < n
  have hX_meas_𝔾 : ∀ n j, j < n →
      @Measurable Ω ℝ (𝔾 n) inferInstance (X j) := by
    intro n j hjn
    exact (comap_measurable (X j)).mono (le_iSup₂_of_le j hjn le_rfl) le_rfl
  -- M n is @Measurable w.r.t. 𝔾 n
  have hM_meas : ∀ n, @Measurable Ω ℝ (𝔾 n) inferInstance (M n) := by
    intro n
    apply Measurable.exp
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    exact (hX_meas_𝔾 n i (Finset.mem_range.mp hi)).sub measurable_const
  -- Integrability of exp(R * X_i)
  have h_int_exp : Integrable (fun ω => exp (R * X 0 ω)) μ :=
    integrable_exp_of_adjustment c hc lam hlam R hR_pos hR_def
  -- Integral of exp(R * (X n - c/lam)) equals exp(-R*c/lam) * (1 + R*c/lam)
  have h_exp_integral : ∀ n, ∫ ω, exp (R * (X n ω - c / lam)) ∂μ =
      exp (-(R * c / lam)) * (1 + R * c / lam) := by
    -- By the properties of the exponential function and the definition of the moment generating function, we can rewrite the integral.
    have h_int_exp : ∀ n, ∫ ω, Real.exp (R * (X n ω - c / lam)) ∂μ = Real.exp (-(R * c / lam)) * ∫ ω, Real.exp (R * X n ω) ∂μ := by
      intro n; rw [ ← MeasureTheory.integral_const_mul ] ; congr; ext ω; rw [ ← Real.exp_add ] ; ring;
    intro n
    have h_int_exp_n : ∫ ω, Real.exp (R * X n ω) ∂μ = ∫ ω, Real.exp (R * X 0 ω) ∂μ := by
      have := h_dist n;
      exact this.comp ( measurable_id'.const_mul R |> Measurable.exp ) |> IdentDistrib.integral_eq;
    rw [ h_int_exp, h_int_exp_n, MeasureTheory.integral_sub ] at * <;> norm_num at *;
    · rw [ ← hR_def, mul_div_cancel_left₀ _ hlam.ne', add_sub_cancel ];
    · assumption
  -- Integral of exp(R * (X n - c/lam)) ≤ 1
  have h_exp_le_one : ∀ n, ∫ ω, exp (R * (X n ω - c / lam)) ∂μ ≤ 1 := by
    intro n; rw [h_exp_integral]; exact mgf_net_loss_le_one c hc lam hlam R hR_pos
  -- Integrability of exp(R * (X n - c/lam))
  have h_int_net : ∀ n, Integrable (fun ω => exp (R * (X n ω - c / lam))) μ := by
    intro n;
    exact ( by have := h_exp_integral n; exact ( by by_contra h; rw [ MeasureTheory.integral_undef h ] at this; exact absurd this ( by positivity ) ) )
  -- Independence: X n is independent of 𝔾 n
  have h_indep : ∀ n, ProbabilityTheory.Indep
      (MeasurableSpace.comap (X n) inferInstance) (𝔾 n) μ := by
    intro n;
    induction' n with n ih;
    · simp [𝔾];
      exact?;
    · have h_indep_succ : Indep (MeasurableSpace.comap (X (n + 1)) inferInstance) (⨆ j < n + 1, MeasurableSpace.comap (X j) inferInstance) μ := by
        have h_indep_succ : Indep (MeasurableSpace.comap (X (n + 1)) inferInstance) (⨆ j ≤ n, MeasurableSpace.comap (X j) inferInstance) μ := by
          have h_indep_succ : ∀ (n : ℕ), Indep (MeasurableSpace.comap (X (n + 1)) inferInstance) (⨆ j ≤ n, MeasurableSpace.comap (X j) inferInstance) μ := by
            intro n;
            convert h_iid.indep_comap_natural_of_lt _ using 1;
            rotate_left;
            exact n;
            exact n + 1;
            exact fun i => h_meas i |> Measurable.stronglyMeasurable;
            simp +decide [ Filtration.natural ];
          exact h_indep_succ n;
        simpa only [ Nat.lt_succ_iff ] using h_indep_succ;
      exact h_indep_succ
  -- M n is integrable
  have h_int_M : ∀ n, Integrable (M n) μ := by
    -- By induction on $n$, we can show that $M_n$ is integrable for all $n$.
    have h_int_M_ind : ∀ n, Integrable (M n) μ := by
      have h_base : Integrable (M 0) μ := by
        simp +zetaDelta at *
      have h_step : ∀ n, Integrable (M n) μ → Integrable (M (n + 1)) μ := by
        intro n hn
        have h_prod : Integrable (fun ω => M n ω * Real.exp (R * (X n ω - c / lam))) μ := by
          apply_rules [ ProbabilityTheory.IndepFun.integrable_mul, h_indep ];
          have h_indep : IndepFun (fun ω => M n ω) (fun ω => X n ω) μ := by
            have := h_indep n;
            rw [ ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul ];
            intro s t hs ht;
            convert this ( ( fun ω => X n ω ) ⁻¹' t ) ( ( fun ω => M n ω ) ⁻¹' s ) ( by
              exact ⟨ t, ht, rfl ⟩ ) ( by
              exact hM_meas n hs ) using 1;
            simp +decide [ Set.inter_comm, MeasureTheory.ae_dirac_eq ];
            rw [ mul_comm ];
          exact h_indep.comp ( measurable_id' ) ( measurable_id'.exp.comp ( measurable_const.mul ( measurable_id'.sub measurable_const ) ) );
        convert h_prod using 1;
        ext ω; simp +decide [ M, Finset.sum_range_succ ] ; ring;
        rw [ ← Real.exp_add ] ; ring
      exact fun n => Nat.recOn n h_base h_step;
    exact h_int_M_ind
  refine ⟨𝔾, supermartingale_nat ?_ ?_ ?_⟩
  -- StronglyAdapted: M n is strongly measurable w.r.t. 𝔾 n
  · intro n
    exact (hM_meas n).stronglyMeasurable
  -- Integrable
  · exact h_int_M
  -- Conditional expectation inequality: μ[M(n+1) | 𝔾 n] ≤ M n  a.e.
  · intro n
    -- Rewrite M(n+1) = M n * exp(R * (X n - c/lam))
    set g : Ω → ℝ := fun ω => exp (R * (X n ω - c / lam))
    have h_eq : M (n + 1) = M n * g := by
      ext ω; simp only [M, g, Pi.mul_apply, Finset.sum_range_succ, mul_add, Real.exp_add]
    rw [h_eq]
    -- Pull out M n using condExp_mul_of_stronglyMeasurable_left
    have h_sm : @StronglyMeasurable Ω ℝ _ (𝔾 n) (M n) := (hM_meas n).stronglyMeasurable
    have h_int_Mg : Integrable (M n * g) μ := (h_int_M (n + 1)).congr (by rw [h_eq])
    have h_pullout := condExp_mul_of_stronglyMeasurable_left (m := 𝔾 n)
      h_sm h_int_Mg (h_int_net n)
    -- Independence gives condexp = integral
    have hle1 : MeasurableSpace.comap (X n) inferInstance ≤ mΩ :=
      MeasurableSpace.comap_le_iff_le_map.mpr (h_meas n)
    haveI : SigmaFinite (μ.trim (𝔾.le' n)) := by
      haveI : IsFiniteMeasure (μ.trim (𝔾.le' n)) := isFiniteMeasure_trim _
      infer_instance
    have h_sm_net : @StronglyMeasurable Ω ℝ _
        (MeasurableSpace.comap (X n) inferInstance) g := by
      apply @Measurable.stronglyMeasurable (mα := MeasurableSpace.comap (X n) inferInstance)
      exact ((comap_measurable (X n)).sub measurable_const |>.const_mul R |>.exp)
    have h_condexp_eq := condExp_indep_eq (m := mΩ) hle1 (𝔾.le' n)
      h_sm_net (h_indep n)
    -- Combine: μ[M n * g | 𝔾 n] =ᵐ M n * E[g] ≤ M n
    have h_step1 : μ[M n * g | 𝔾 n] =ᵐ[μ] M n * μ[g | 𝔾 n] := h_pullout
    have h_step2 : μ[g | 𝔾 n] =ᵐ[μ] fun _ => ∫ ω, g ω ∂μ := h_condexp_eq
    filter_upwards [h_step1, h_step2] with ω h1 h2
    simp only [Pi.mul_apply] at h1 ⊢
    rw [h1, h2]
    exact mul_le_of_le_one_right (exp_nonneg _) (h_exp_le_one n)

lemma ruin_prob_le_exp
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (u : ℝ) (hu : 0 ≤ u)
    (c : ℝ) (hc : 0 < c)
    (lam : ℝ) (hlam : 0 < lam)
    {X : ℕ → Ω → ℝ}
    (h_iid : iIndepFun X μ)
    (h_dist : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (h_pos : ∀ i ω, 0 ≤ X i ω)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : Integrable (X 0) μ)
    (R : ℝ) (hR_pos : 0 < R)
    (hR_def : lam * (∫ ω, exp (R * X 0 ω) - 1 ∂μ) = R * c) :
    (μ {ω | ∃ n : ℕ, (∑ i ∈ range n, (X i ω - c / lam)) ≥ u}).toReal ≤
      exp (-R * u) := by
  have := @ville_supermartingale_unit_initial;
  contrapose! this;
  refine' ⟨ Ω, mΩ, μ, _, _ ⟩;
  · infer_instance;
  · obtain ⟨𝔾, hsup⟩ := exp_process_supermartingale c hc lam hlam h_iid h_dist h_meas R hR_pos hR_def;
    refine' ⟨ _, 𝔾, hsup, _, _, _ ⟩;
    · exact fun _ _ => Real.exp_nonneg _;
    · norm_num;
    · refine' ⟨ Real.exp ( R * u ), Real.exp_pos _, _ ⟩;
      convert ENNReal.ofReal_lt_ofReal_iff ( show 0 < ( μ { ω | ∃ n, ∑ i ∈ range n, ( X i ω - c / lam ) ≥ u } ).toReal from lt_of_le_of_lt ( by positivity ) this ) |>.2 this using 1;
      · simp +decide [ Real.exp_neg, ENNReal.ofReal ];
      · simp +decide [ Real.exp_le_exp, mul_le_mul_iff_right₀ hR_pos ]

/-! ## Part 5: The main theorem -/

/-- **Lundberg's inequality.** In the Cramér-Lundberg model, if the adjustment
    coefficient `R > 0` satisfies `λ E[exp(R X) − 1] = R c`, then:
    1. The ruin probability `ψ(u) ≤ exp(−R u)`.
    2. `R` is the unique positive solution of the adjustment equation.

    Note: `lam` stands for the claim arrival rate λ (a Lean reserved keyword).
    The hypothesis `h_meas` (measurability of claim sizes) is a standard
    regularity condition in the Cramér-Lundberg model. -/
theorem lundberg_inequality
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (u : ℝ) (hu : 0 ≤ u)
    (c : ℝ) (hc : 0 < c)
    (lam : ℝ) (hlam : 0 < lam)
    {X : ℕ → Ω → ℝ}
    (h_iid : iIndepFun X μ)
    (h_dist : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (h_pos : ∀ i ω, 0 ≤ X i ω)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : Integrable (X 0) μ)
    (h_safety : c > lam * (∫ ω, X 0 ω ∂μ))
    (R : ℝ) (hR_pos : 0 < R)
    (hR_def : lam * (∫ ω, exp (R * X 0 ω) - 1 ∂μ) = R * c) :
    let ψ : ℝ → ℝ := fun v =>
      (μ {ω | ∃ n : ℕ, (∑ i ∈ range n, (X i ω - c / lam)) ≥ v}).toReal
    ψ u ≤ exp (-R * u) ∧
    (∀ R' : ℝ, 0 < R' →
      lam * (∫ ω, exp (R' * X 0 ω) - 1 ∂μ) = R' * c → R' = R) := by
  intro ψ
  constructor
  · -- Part 1: Ruin bound ψ(u) ≤ exp(-R·u)
    exact ruin_prob_le_exp u hu c hc lam hlam h_iid h_dist h_pos h_meas h_int R hR_pos hR_def
  · -- Part 2: Uniqueness of R
    intro R' hR'_pos hR'_def
    have hR_int := integrable_exp_of_adjustment c hc lam hlam R hR_pos hR_def
    have hR'_int := integrable_exp_of_adjustment c hc lam hlam R' hR'_pos hR'_def
    exact adjustment_coeff_unique c hc lam hlam (h_pos 0)
      R hR_pos hR_def hR_int R' hR'_pos hR'_def hR'_int

end Pythia