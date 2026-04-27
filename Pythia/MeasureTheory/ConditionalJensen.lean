/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harmonic
-/
import Mathlib

/-!
# Conditional Jensen's Inequality

For a convex function `φ : ℝ → ℝ`, an integrable random variable `X`, and a
sub-σ-algebra `m ≤ m₀`, we prove the pointwise a.e. inequality

  `φ(𝔼[X | m]) ≤ 𝔼[φ(X) | m]`   a.s.

This is the *conditional* form of Jensen's inequality. The unconditional version
(`ConvexOn.map_integral_le`) is already in Mathlib; this file provides the
conditional upgrade, which is load-bearing for many martingale and concentration
results.

## Proof strategy

We use the **countable affine minorant** method:

1. At every rational point `q`, the supporting-line lemma gives an affine function
   `L_q(x) = φ(q) + c_q · (x − q)` that minorises `φ` everywhere.
2. Each `L_q ∘ X` is integrable (affine in the integrable `X`), so
   `condexp_mono` + linearity yield `L_q(𝔼[X|m]) ≤ 𝔼[φ∘X|m]` a.e.
3. A countable intersection over `q ∈ ℚ` gives the inequality for all rational
   affine minorants simultaneously a.e.
4. Continuity of `φ` implies `φ(y) = sup_q L_q(y)` for every `y`, finishing
   the proof.

## References

* Williams, *Probability with Martingales*, §9.7
-/

open MeasureTheory Filter Set

noncomputable section

namespace ConditionalJensen

/-! ### Supporting-line lemma -/

/-
**Supporting-line lemma** (subgradient existence). For a convex function on `ℝ` and
any point `x₀`, there exists a slope `c` such that the affine function
`x ↦ φ(x₀) + c * (x − x₀)` minorises `φ` everywhere.
-/
theorem ConvexOn.exists_affine_le {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ) (x₀ : ℝ) :
    ∃ c : ℝ, ∀ x : ℝ, φ x₀ + c * (x - x₀) ≤ φ x := by
  -- Let $c$ be the right derivative of $\phi$ at $x_{0}$.
  obtain ⟨c, hc⟩ : ∃ c, ∀ x, x > x₀ → (φ x - φ x₀) / (x - x₀) ≥ c ∧ ∀ x, x < x₀ → (φ x - φ x₀) / (x - x₀) ≤ c := by
    use sInf (Set.image (fun x => (φ x - φ x₀) / (x - x₀)) (Set.Ioi x₀));
    refine' fun x hx => ⟨ _, _ ⟩;
    · refine' csInf_le _ _;
      · refine' ⟨ ( φ x₀ - φ ( x₀ - 1 ) ) / ( x₀ - ( x₀ - 1 ) ), Set.forall_mem_image.2 fun y hy => _ ⟩;
        have := hφ.slope_mono_adjacent ( Set.mem_univ ( x₀ - 1 ) ) ( Set.mem_univ y ) ( by linarith [ hy.out ] : x₀ - 1 < x₀ ) hy.out; aesop;
      · grind;
    · intro x hx
      have h_slope : ∀ y > x₀, (φ y - φ x₀) / (y - x₀) ≥ (φ x₀ - φ x) / (x₀ - x) := by
        intro y hy; have := hφ.slope_mono_adjacent ( Set.mem_univ x ) ( Set.mem_univ y ) hx hy; aesop;
      exact le_csInf ⟨ _, Set.mem_image_of_mem _ ( show x₀ + 1 ∈ Set.Ioi x₀ by norm_num ) ⟩ ( Set.forall_mem_image.2 fun y hy => by rw [ ← neg_div_neg_eq ] ; simpa using h_slope y hy );
  refine' ⟨ c, fun x => _ ⟩;
  rcases lt_trichotomy x x₀ with ( h | rfl | h ) <;> norm_num;
  · have := hc ( x₀ + 1 ) ( by linarith ) ; have := this.2 x h; rw [ div_le_iff_of_neg ] at this <;> linarith;
  · have := hc x h; rw [ ge_iff_le, le_div_iff₀ ] at this <;> linarith

/-! ### Affine minorant approximation -/

/-
For a continuous convex function, for every `ε > 0` there exists a rational point
`q` whose supporting line at `q` evaluated at `y` is within `ε` of `φ(y)`.
-/
theorem ConvexOn.approx_by_rat_affine {φ : ℝ → ℝ} (_hφ : ConvexOn ℝ univ φ)
    (hφ_cont : Continuous φ)
    (c : ℚ → ℝ) (hc : ∀ q : ℚ, ∀ x : ℝ, φ (q : ℝ) + c q * (x - (q : ℝ)) ≤ φ x)
    (y : ℝ) :
    ∀ ε > (0 : ℝ), ∃ q : ℚ, φ y - ε < φ (q : ℝ) + c q * (y - (q : ℝ)) := by
  intro ε hε;
  -- Fix y and ε > 0. Take a sequence of rationals q_n → y (using density of ℚ in ℝ).
  obtain ⟨q_n, hq_n⟩ : ∃ q_n : ℕ → ℚ, Filter.Tendsto (fun n => q_n n : ℕ → ℝ) Filter.atTop (nhds y) := by
    have h_seq : ∀ ε > 0, ∃ q : ℚ, abs (q - y) < ε := by
      exact fun ε hε => by rcases exists_rat_btwn ( sub_lt_self y hε ) with ⟨ q, hq₁, hq₂ ⟩ ; exact ⟨ q, abs_lt.mpr ⟨ by linarith, by linarith ⟩ ⟩ ;
    exact ⟨ fun n => Classical.choose ( h_seq ( 1 / ( n + 1 ) ) ( by positivity ) ), tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero ( fun _ => by positivity ) ( fun n => Classical.choose_spec ( h_seq ( 1 / ( n + 1 ) ) ( by positivity ) ) |> le_of_lt ) <| tendsto_one_div_add_atTop_nhds_zero_nat ⟩;
  -- By the properties of the supporting lines, we have that $c_{q_n}$ is bounded.
  have h_c_bounded : ∃ M > 0, ∀ᶠ n in Filter.atTop, |c (q_n n)| ≤ M := by
    -- By the properties of the supporting lines, we have that $c_{q_n}$ is bounded by the slopes of the supporting lines at $y - 1$ and $y + 1$.
    have h_c_bounded : ∀ᶠ n in Filter.atTop, c (q_n n) ≤ (φ (y + 1) - φ (q_n n)) / (y + 1 - q_n n) ∧ c (q_n n) ≥ (φ (y - 1) - φ (q_n n)) / (y - 1 - q_n n) := by
      filter_upwards [ hq_n.eventually ( Metric.ball_mem_nhds _ zero_lt_one ) ] with n hn;
      exact ⟨ by rw [ le_div_iff₀ ] <;> linarith [ abs_lt.mp hn, hc ( q_n n ) ( y + 1 ) ], by rw [ ge_iff_le, div_le_iff_of_neg ] <;> linarith [ abs_lt.mp hn, hc ( q_n n ) ( y - 1 ) ] ⟩;
    -- Since $\phi$ is continuous, the slopes of the supporting lines at $y - 1$ and $y + 1$ are bounded.
    have h_slope_bounded : Filter.Tendsto (fun n => (φ (y + 1) - φ (q_n n)) / (y + 1 - q_n n)) Filter.atTop (nhds ((φ (y + 1) - φ y) / (y + 1 - y))) ∧ Filter.Tendsto (fun n => (φ (y - 1) - φ (q_n n)) / (y - 1 - q_n n)) Filter.atTop (nhds ((φ (y - 1) - φ y) / (y - 1 - y))) := by
      exact ⟨ Filter.Tendsto.div ( tendsto_const_nhds.sub ( hφ_cont.continuousAt.tendsto.comp hq_n ) ) ( tendsto_const_nhds.sub hq_n ) ( by linarith ), Filter.Tendsto.div ( tendsto_const_nhds.sub ( hφ_cont.continuousAt.tendsto.comp hq_n ) ) ( tendsto_const_nhds.sub hq_n ) ( by linarith ) ⟩;
    obtain ⟨M₁, hM₁⟩ : ∃ M₁ > 0, ∀ᶠ n in Filter.atTop, |(φ (y + 1) - φ (q_n n)) / (y + 1 - q_n n)| ≤ M₁ := by
      exact Filter.Tendsto.bddAbove_range ( h_slope_bounded.1.abs ) |> fun ⟨ M₁, hM₁ ⟩ => ⟨ Max.max M₁ 1, by positivity, Filter.Eventually.of_forall fun n => le_trans ( hM₁ <| Set.mem_range_self n ) <| le_max_left _ _ ⟩
    obtain ⟨M₂, hM₂⟩ : ∃ M₂ > 0, ∀ᶠ n in Filter.atTop, |(φ (y - 1) - φ (q_n n)) / (y - 1 - q_n n)| ≤ M₂ := by
      exact ⟨ |(φ (y - 1) - φ y) / (y - 1 - y)| + 1, by positivity, h_slope_bounded.2.abs.eventually ( ge_mem_nhds <| lt_add_one _ ) ⟩;
    exact ⟨ Max.max M₁ M₂, lt_max_of_lt_left hM₁.1, by filter_upwards [ h_c_bounded, hM₁.2, hM₂.2 ] with n hn₁ hn₂ hn₃ using abs_le.mpr ⟨ by linarith [ abs_le.mp hn₃, le_max_right M₁ M₂ ], by linarith [ abs_le.mp hn₂, le_max_left M₁ M₂ ] ⟩ ⟩;
  -- Since $c_{q_n}$ is bounded, we have that $c_{q_n} * (y - q_n) \to 0$ as $n \to \infty$.
  have h_c_q_n_zero : Filter.Tendsto (fun n => c (q_n n) * (y - q_n n)) Filter.atTop (nhds 0) := by
    exact squeeze_zero_norm' ( by filter_upwards [ h_c_bounded.choose_spec.2 ] with n hn; simpa [ abs_mul ] using mul_le_mul_of_nonneg_right hn ( abs_nonneg _ ) ) ( by simpa using hq_n.const_sub y |> Filter.Tendsto.abs |> Filter.Tendsto.const_mul ( h_c_bounded.choose : ℝ ) );
  have := h_c_q_n_zero.add ( hφ_cont.continuousAt.tendsto.comp hq_n );
  have := this.eventually ( lt_mem_nhds <| show 0 + φ y > φ y - ε by linarith ) ; obtain ⟨ n, hn ⟩ := this.exists; exact ⟨ q_n n, by norm_num at *; linarith ⟩ ;

/-! ### Conditional expectation lower bound by constant -/

/-
If an integrable function is a.e. bounded below by a constant `c`, then its
conditional expectation is also a.e. bounded below by `c`.
-/
theorem condExp_ge_const {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    {f : Ω → ℝ} (hf : Integrable f μ) {c : ℝ} (hfc : ∀ᵐ ω ∂μ, c ≤ f ω) :
    ∀ᵐ ω ∂μ, c ≤ μ[f | m] ω := by
  by_contra h;
  -- Let $A = \{ \omega \mid \mathbb{E}[f \mid m](\omega) < c \}$. Since $\mathbb{E}[f \mid m]$ is $m$-measurable, $A$ is $m$-measurable.
  set A := {ω | MeasureTheory.condExp m μ f ω < c} with hA_def
  have hA_meas : MeasurableSet[m] A := by
    exact measurableSet_lt ( MeasureTheory.stronglyMeasurable_condExp.measurable ) measurable_const;
  -- Since μ is σ-finite with respect to m, there exists a set B ⊆ A with 0 < μ(B) < ∞.
  obtain ⟨B, hB_sub, hB_meas, hB_pos⟩ : ∃ B ⊆ A, MeasurableSet[m] B ∧ 0 < μ B ∧ μ B < ⊤ := by
    have h_sigma_finite : ∀ {S : Set Ω}, MeasurableSet[m] S → μ S ≠ 0 → ∃ B ⊆ S, MeasurableSet[m] B ∧ 0 < μ B ∧ μ B < ⊤ := by
      intro S hS_meas hS_pos
      have h_sigma_finite : ∃ B ⊆ S, MeasurableSet[m] B ∧ 0 < μ B ∧ μ B < ⊤ := by
        have h_sigma_finite : ∃ B ⊆ S, MeasurableSet[m] B ∧ μ B < ⊤ ∧ μ B ≠ 0 := by
          have h_sigma_finite : ∀ {S : Set Ω}, MeasurableSet[m] S → μ S ≠ 0 → ∃ B ⊆ S, MeasurableSet[m] B ∧ μ B < ⊤ ∧ μ B ≠ 0 := by
            intro S hS_meas hS_pos
            have h_sigma_finite : ∃ n, μ (S ∩ (MeasureTheory.spanningSets (μ.trim hm) n)) ≠ 0 := by
              have h_sigma_finite : μ S = μ (⋃ n, S ∩ (MeasureTheory.spanningSets (μ.trim hm) n)) := by
                rw [ ← Set.inter_iUnion, iUnion_spanningSets ];
                rw [ Set.inter_univ ];
              exact not_forall.mp fun h => hS_pos <| h_sigma_finite.trans <| MeasureTheory.measure_iUnion_null h
            obtain ⟨ n, hn ⟩ := h_sigma_finite;
            refine' ⟨ S ∩ spanningSets ( μ.trim hm ) n, Set.inter_subset_left, _, _, hn ⟩;
            · exact hS_meas.inter ( MeasureTheory.measurableSet_spanningSets ( μ.trim hm ) n );
            · refine' lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) _;
              have := MeasureTheory.measure_spanningSets_lt_top ( μ.trim hm ) n;
              convert this using 1;
              rw [ MeasureTheory.trim_measurableSet_eq ];
              exact measurableSet_spanningSets (μ.trim hm) n;
          exact h_sigma_finite hS_meas hS_pos
        exact ⟨ h_sigma_finite.choose, h_sigma_finite.choose_spec.1, h_sigma_finite.choose_spec.2.1, lt_of_le_of_ne ( zero_le _ ) h_sigma_finite.choose_spec.2.2.2.symm, h_sigma_finite.choose_spec.2.2.1 ⟩;
      exact h_sigma_finite;
    apply h_sigma_finite hA_meas;
    exact fun h' => h <| MeasureTheory.measure_mono_null ( fun x hx => by aesop ) h';
  -- Since $B \subseteq A$, we have $\int_B \mathbb{E}[f \mid m] \, d\mu < c \cdot \mu(B)$.
  have hB_int : ∫ ω in B, MeasureTheory.condExp m μ f ω ∂μ < c * μ.real B := by
    have hB_int : ∀ᵐ ω ∂μ.restrict B, MeasureTheory.condExp m μ f ω < c := by
      exact ae_restrict_of_forall_mem (hm B hB_meas) hB_sub;
    have hB_int : ∫ ω in B, (c - MeasureTheory.condExp m μ f ω) ∂μ > 0 := by
      refine' ( lt_of_le_of_lt _ ( MeasureTheory.integral_pos_iff_support_of_nonneg_ae _ _ |>.2 _ ) );
      · norm_num;
      · filter_upwards [ hB_int ] with ω hω using sub_nonneg_of_le hω.le;
      · refine' MeasureTheory.Integrable.sub _ _;
        · simp +decide [ MeasureTheory.integrable_const_iff ];
          exact Or.inr ⟨ by aesop ⟩;
        · exact MeasureTheory.Integrable.integrableOn ( MeasureTheory.integrable_condExp );
      · simp_all +decide [ Function.support, sub_eq_zero ];
        exact lt_of_lt_of_le ( by aesop ) ( MeasureTheory.measure_mono ( show { x | ¬c = MeasureTheory.condExp m μ f x } ⊇ B from fun x hx => ne_of_gt ( hB_sub hx ) ) );
    rw [ MeasureTheory.integral_sub ] at hB_int <;> norm_num at *;
    · linarith;
    · apply_rules [ MeasureTheory.integrable_const ];
      constructor ; aesop;
    · exact MeasureTheory.Integrable.integrableOn ( MeasureTheory.integrable_condExp );
  -- Since $B \subseteq A$, we have $\int_B f \, d\mu \geq c \cdot \mu(B)$.
  have hB_int_f : ∫ ω in B, f ω ∂μ ≥ c * μ.real B := by
    have hB_int_f : ∫ ω in B, (f ω - c) ∂μ ≥ 0 := by
      exact MeasureTheory.integral_nonneg_of_ae ( MeasureTheory.ae_restrict_of_ae hfc |> fun h => h.mono fun x hx => sub_nonneg.2 hx );
    rw [ MeasureTheory.integral_sub ] at hB_int_f <;> norm_num at *;
    · lia;
    · exact hf.integrableOn;
    · apply_rules [ MeasureTheory.integrable_const ];
      constructor ; aesop;
  -- By the definition of conditional expectation, we have $\int_B \mathbb{E}[f \mid m] \, d\mu = \int_B f \, d\mu$.
  have hB_int_eq : ∫ ω in B, MeasureTheory.condExp m μ f ω ∂μ = ∫ ω in B, f ω ∂μ := by
    apply_rules [ MeasureTheory.setIntegral_condExp ];
  linarith

/-! ### Affine conditional expectation step -/

/-
For an affine minorant `d + a * x ≤ φ(x)`, the conditional expectation of
`φ ∘ X` dominates the affine function evaluated at the conditional expectation of `X`.
-/
theorem condExp_affine_minorant_le
    {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    {φ : ℝ → ℝ} {X : Ω → ℝ} (hX : Integrable X μ) (hφX : Integrable (φ ∘ X) μ)
    {a d : ℝ} (hle : ∀ x : ℝ, d + a * x ≤ φ x) :
    ∀ᵐ ω ∂μ, d + a * μ[X | m] ω ≤ μ[φ ∘ X | m] ω := by
  -- Let $g(ω) = φ(X(ω)) - a * X(ω)$. By assumption, $g$ is integrable and $g ≥ d$ pointwise.
  set g : Ω → ℝ := fun ω => (φ ∘ X) ω - a * X ω
  have hg_int : Integrable g μ := by
    exact hφX.sub ( hX.const_mul a )
  have hg_ge_d : ∀ ω, g ω ≥ d := by
    exact fun ω => le_tsub_of_add_le_right <| hle _;
  -- By the properties of conditional expectation, we have $\mathrm{E}[g | m] = \mathrm{E}[(φ \circ X) | m] - a \mathrm{E}[X | m]$.
  have h_condExp_g : ∀ᵐ ω ∂μ, μ[g | m] ω = μ[φ ∘ X | m] ω - a * μ[X | m] ω := by
    have h_condExp_g : ∀ᵐ ω ∂μ, μ[g | m] ω = μ[(φ ∘ X) | m] ω - μ[a • X | m] ω := by
      apply_rules [ MeasureTheory.condExp_sub ];
      exact hX.const_mul a;
    have h_condExp_smul : ∀ᵐ ω ∂μ, μ[a • X | m] ω = a * μ[X | m] ω := by
      apply_rules [ MeasureTheory.condExp_smul ];
    filter_upwards [ h_condExp_g, h_condExp_smul ] with ω hω₁ hω₂ using by rw [ hω₁, hω₂ ] ;
  -- By the properties of conditional expectation, we have $\mathrm{E}[g | m] \geq d$.
  have h_condExp_g_ge_d : ∀ᵐ ω ∂μ, μ[g | m] ω ≥ d := by
    apply_rules [ condExp_ge_const ];
    exact Filter.Eventually.of_forall hg_ge_d;
  filter_upwards [ h_condExp_g, h_condExp_g_ge_d ] with ω hω₁ hω₂ using by linarith;

/-! ### Main theorem -/

/-
**Conditional Jensen's Inequality.** If `φ : ℝ → ℝ` is convex and continuous,
`X` is integrable, `φ ∘ X` is integrable, and `m` is a sub-σ-algebra, then
`φ(𝔼[X | m]) ≤ 𝔼[φ(X) | m]` almost surely.
-/
theorem condExp_le_condExp_of_convexOn
    {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    (hm : m ≤ m₀) [hμm : SigmaFinite (μ.trim hm)]
    {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ) (hφ_cont : Continuous φ)
    {X : Ω → ℝ} (hX : Integrable X μ) (hφX : Integrable (φ ∘ X) μ) :
    (fun ω => φ (μ[X | m] ω)) ≤ᵐ[μ] μ[φ ∘ X | m] := by
  obtain ⟨c, hc⟩ : ∃ c : ℚ → ℝ, ∀ q : ℚ, ∀ x : ℝ, φ (q : ℝ) + c q * (x - (q : ℝ)) ≤ φ x := by
    exact ⟨ fun q => Classical.choose ( ConvexOn.exists_affine_le hφ q ), fun q x => Classical.choose_spec ( ConvexOn.exists_affine_le hφ q ) x ⟩;
  -- By the properties of the conditional expectation, we have that for each rational number $q$, $\phi(q) + c_q (E[X|m] - q) \leq E[\phi(X)|m]$ almost surely.
  have h_ae_affine : ∀ q : ℚ, ∀ᵐ ω ∂μ, φ (q : ℝ) + c q * ((μ[X | m]) ω - (q : ℝ)) ≤ (μ[φ ∘ X | m]) ω := by
    intro q;
    have := @condExp_affine_minorant_le;
    specialize this hm hX hφX ( show ∀ x : ℝ, φ ↑q - c q * ↑q + c q * x ≤ φ x from fun x => by linarith [ hc q x ] ) ; filter_upwards [ this ] with ω hω using by linarith;
  -- By the properties of the conditional expectation, we have that for almost every $\omega$, $\phi(E[X|m](\omega)) \leq E[\phi(X)|m](\omega)$.
  have h_ae_final : ∀ᵐ ω ∂μ, ∀ q : ℚ, φ (q : ℝ) + c q * ((μ[X | m]) ω - (q : ℝ)) ≤ (μ[φ ∘ X | m]) ω := by
    exact MeasureTheory.ae_all_iff.2 h_ae_affine;
  filter_upwards [ h_ae_final ] with ω hω;
  -- By the properties of the conditional expectation, we have that for almost every $\omega$, $\phi(E[X|m](\omega)) \leq E[\phi(X)|m](\omega)$ follows from the fact that $\phi$ is continuous and convex.
  have h_cont_convex : ∀ ε > 0, ∃ q : ℚ, φ (μ[X | m] ω) - ε < φ (q : ℝ) + c q * ((μ[X | m] ω) - (q : ℝ)) := by
    apply ConvexOn.approx_by_rat_affine hφ hφ_cont c hc;
  exact le_of_forall_pos_le_add fun ε εpos => by obtain ⟨ q, hq ⟩ := h_cont_convex ε εpos; linarith [ hω q ] ;

end ConditionalJensen