/-
Copyright (c) 2024 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Rockafellar–Uryasev CVaR Dual Representation

Formalises the variational (dual) characterisation of Conditional Value-at-Risk
from Rockafellar & Uryasev, *J. Risk* 2(3):21–41 (2000) and *J. Banking &
Finance* 26(7):1443–1471 (2002):

$$
  \operatorname{CVaR}_\alpha(X)
  = \inf_{z\in\mathbb R}\Bigl\{
      z + \frac{1}{1-\alpha}\,\mathbb E\bigl[\max(X-z,\,0)\bigr]
    \Bigr\},
$$

where the infimum is attained at $z^* = \operatorname{VaR}_\alpha(X)$.

## Main definitions

* `VaR μ X α` – Value-at-Risk (left-quantile) at level α.
* `cvarAux μ X α z` – the auxiliary function `F(z) = z + (1/(1-α)) · 𝔼[max(X-z,0)]`.
* `CVaR μ X α` – Conditional Value-at-Risk defined as `⨅ z, cvarAux μ X α z`.

## Main results

* `cvarAux_convexOn` – `F` is convex on `ℝ` in `z`.
* `cvarAux_bddBelow` – `F` is bounded below.
* `CVaR_eq_cvarAux_VaR` – the infimum is attained: `CVaR = F(VaR)`.
* `CVaR_dual_rep` – full dual-representation identity.

## References

* Rockafellar, R.T. & Uryasev, S. (2000). *Optimization of conditional
  value-at-risk.* J. Risk 2(3):21–41.
* Rockafellar, R.T. & Uryasev, S. (2002). *Conditional value-at-risk for
  general loss distributions.* J. Banking & Finance 26(7):1443–1471.

## Practical relevance

CVaR (also called Expected Shortfall, ES) is the regulatory risk metric
mandated by the Basel III/IV framework for market-risk capital calculations.
-/

import Mathlib

open MeasureTheory Measure Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Value-at-Risk (left quantile) -/

/-- Value-at-Risk at level `α`: the left-quantile
    `VaR_α(X) = inf { z ∈ ℝ | P(X ≤ z) ≥ α }` (for a probability measure).
    We use the *generalised inverse* (left-continuous) convention matching
    Rockafellar–Uryasev. -/
def VaR (μ : Measure Ω) (X : Ω → ℝ) (α : ℝ) : ℝ :=
  sInf { z : ℝ | α * (μ Set.univ).toReal ≤ (μ { ω | X ω ≤ z }).toReal }

/-! ### Auxiliary function F(z) -/

/-- The Rockafellar–Uryasev auxiliary function
    `F(z) = z + (1/(1-α)) · ∫ max(X(ω) - z, 0) dμ(ω)`. -/
def cvarAux (μ : Measure Ω) (X : Ω → ℝ) (α : ℝ) (z : ℝ) : ℝ :=
  z + (1 / (1 - α)) * ∫ ω, max (X ω - z) 0 ∂μ

/-! ### CVaR (Expected Shortfall) -/

/-- Conditional Value-at-Risk at level `α`, defined via the Rockafellar–Uryasev
    dual representation as `⨅ z, F(z)`. -/
def CVaR (μ : Measure Ω) (X : Ω → ℝ) (α : ℝ) : ℝ :=
  ⨅ z : ℝ, cvarAux μ X α z

/-! ### Basic properties of the positive-part integrand -/

/-- `ω ↦ max (X ω - z, 0)` is measurable when `X` is. -/
theorem measurable_posPart_sub {X : Ω → ℝ} (hX : Measurable X) (z : ℝ) :
    Measurable (fun ω => max (X ω - z) 0) :=
  Measurable.max (hX.sub measurable_const) measurable_const

/-- `ω ↦ max (X ω - z, 0)` is integrable when `X` is. -/
theorem integrable_posPart_sub {X : Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ]
    (hX : Integrable X μ) (z : ℝ) :
    Integrable (fun ω => max (X ω - z) 0) μ :=
  Integrable.sup (hX.sub (integrable_const z)) (integrable_const 0)

/-! ### Monotonicity and Lipschitz properties of the integral -/

/-- The positive-part integral `z ↦ ∫ max(X-z,0) dμ` is antitone. -/
theorem integral_posPart_antitone {X : Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ]
    (hX : Integrable X μ) :
    Antitone (fun z => ∫ ω, max (X ω - z) 0 ∂μ) := by
  intro z z' hzz'
  exact integral_mono (integrable_posPart_sub hX z') (integrable_posPart_sub hX z)
    (fun ω => max_le_max (sub_le_sub_left hzz' _) le_rfl)

/-- Pointwise upper bound for positive-part differences. -/
theorem posPart_diff_upper {x z₁ z₂ : ℝ} (_hz : z₁ ≤ z₂) :
    max (x - z₁) (0 : ℝ) - max (x - z₂) (0 : ℝ) ≤ z₂ - z₁ := by
  rcases max_cases (x - z₁) 0 with ⟨_, _⟩ | ⟨_, _⟩ <;>
  rcases max_cases (x - z₂) 0 with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith

/-
The positive-part integral decreases by at most `(z₂ - z₁) · μ(Ω)`.
-/
theorem integral_posPart_lipschitz_bound {X : Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ]
    (hX : Integrable X μ) {z₁ z₂ : ℝ} (hz : z₁ ≤ z₂) :
    ∫ ω, max (X ω - z₁) 0 ∂μ - ∫ ω, max (X ω - z₂) 0 ∂μ ≤
      (z₂ - z₁) * (μ Set.univ).toReal := by
        rw [ ← MeasureTheory.integral_sub ];
        · refine' le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _;
          refine' fun ω => z₂ - z₁;
          · exact Filter.Eventually.of_forall fun ω => sub_nonneg_of_le <| max_le_max ( by linarith ) le_rfl;
          · exact MeasureTheory.integrable_const _;
          · filter_upwards [ ] with ω using by cases max_cases ( X ω - z₁ ) 0 <;> cases max_cases ( X ω - z₂ ) 0 <;> linarith;
          · simp +decide [ mul_comm ];
            rfl;
        · exact integrable_posPart_sub hX z₁
        · exact integrable_posPart_sub hX z₂

/-
Lower bound: the integral difference is at least `(z₂-z₁) · μ({X > z₂})`.
-/
theorem integral_posPart_lower_bound {X : Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ]
    (hX : Measurable X) (hXi : Integrable X μ) {z₁ z₂ : ℝ} (hz : z₁ ≤ z₂) :
    (z₂ - z₁) * (μ { ω | z₂ < X ω }).toReal ≤
      ∫ ω, max (X ω - z₁) 0 ∂μ - ∫ ω, max (X ω - z₂) 0 ∂μ := by
        rw [ ← MeasureTheory.integral_sub ];
        · refine' le_trans _ ( MeasureTheory.integral_mono_of_nonneg _ _ _ );
          case refine'_2 => exact fun ω => ( z₂ - z₁ ) * ( if z₂ < X ω then 1 else 0 );
          · erw [ MeasureTheory.integral_const_mul, MeasureTheory.integral_indicator ( measurableSet_lt measurable_const hX ) ] ; aesop;
          · exact Filter.Eventually.of_forall fun ω => mul_nonneg ( sub_nonneg.2 hz ) ( by split_ifs <;> norm_num );
          · exact MeasureTheory.Integrable.sub ( MeasureTheory.Integrable.sup ( hXi.sub ( MeasureTheory.integrable_const _ ) ) ( MeasureTheory.integrable_const _ ) ) ( MeasureTheory.Integrable.sup ( hXi.sub ( MeasureTheory.integrable_const _ ) ) ( MeasureTheory.integrable_const _ ) );
          · filter_upwards [ ] with ω using by split_ifs <;> cases max_cases ( X ω - z₁ ) 0 <;> cases max_cases ( X ω - z₂ ) 0 <;> linarith;
        · exact integrable_posPart_sub hXi z₁
        · exact MeasureTheory.Integrable.pos_part ( hXi.sub ( MeasureTheory.integrable_const _ ) )

/-! ### Convexity of the auxiliary function -/

/-
`F` is convex on `ℝ` when `α ∈ (0,1)`.
-/
theorem cvarAux_convexOn {X : Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ]
    (_hX : Measurable X) (hXi : Integrable X μ)
    (_hα : 0 < α) (hα1 : α < 1) :
    ConvexOn ℝ Set.univ (cvarAux μ X α) := by
      have h_convex_int : ConvexOn ℝ Set.univ (fun z => ∫ ω, max (X ω - z) 0 ∂μ) := by
        refine' ⟨ convex_univ, fun x _ y _ a b ha hb hab => _ ⟩;
        simp +zetaDelta at *;
        rw [ ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_add ];
        · refine' MeasureTheory.integral_mono_of_nonneg _ _ _;
          · exact Filter.Eventually.of_forall fun ω => le_max_right _ _;
          · fun_prop;
          · filter_upwards [ ] with ω using by rw [ ← eq_sub_iff_add_eq' ] at hab; subst hab; cases max_cases ( X ω - ( a * x + ( 1 - a ) * y ) ) 0 <;> cases max_cases ( X ω - x ) 0 <;> cases max_cases ( X ω - y ) 0 <;> nlinarith;
        · exact MeasureTheory.Integrable.const_mul ( hXi.sub ( MeasureTheory.integrable_const x ) |> MeasureTheory.Integrable.pos_part ) _;
        · exact MeasureTheory.Integrable.const_mul ( hXi.sub ( MeasureTheory.integrable_const y ) |> MeasureTheory.Integrable.pos_part ) _;
      refine' ( convexOn_id ( convex_univ ) ).add ( h_convex_int.smul ( by exact div_nonneg zero_le_one ( sub_nonneg.mpr hα1.le ) ) )

/-- `F` is continuous (convex on an open set ⟹ continuous). -/
theorem cvarAux_continuous {X : Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ]
    (hX : Measurable X) (hXi : Integrable X μ)
    (hα : 0 < α) (hα1 : α < 1) :
    Continuous (cvarAux μ X α) := by
  have hc := cvarAux_convexOn hX hXi hα hα1
  have := hc.continuousOn isOpen_univ
  rwa [continuousOn_univ] at this

/-! ### Boundedness below -/

/-
On a probability space, `F(z) ≥ 𝔼[X]` for all `z` when `α ∈ (0,1)`.
-/
theorem cvarAux_ge_integral {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hXi : Integrable X μ) (hα : 0 < α) (hα1 : α < 1) (z : ℝ) :
    ∫ ω, X ω ∂μ ≤ cvarAux μ X α z := by
      -- Integrate the inequality `X ω ≤ max(X ω - z, 0) + z` over the probability space `μ`.
      have h_int_le : (∫ ω, X ω ∂μ : ℝ) ≤ (∫ ω, max ((X ω) - z) 0 ∂μ : ℝ) + z := by
        convert MeasureTheory.integral_mono _ _ fun ω => show X ω ≤ max ( X ω - z ) 0 + z by linarith [ le_max_left ( X ω - z ) 0, le_max_right ( X ω - z ) 0 ] using 1;
        · rw [ MeasureTheory.integral_add ] <;> norm_num;
          exact MeasureTheory.Integrable.pos_part ( hXi.sub ( MeasureTheory.integrable_const z ) );
        · exact hXi;
        · exact MeasureTheory.Integrable.add ( MeasureTheory.Integrable.sup ( hXi.sub ( MeasureTheory.integrable_const z ) ) ( MeasureTheory.integrable_const 0 ) ) ( MeasureTheory.integrable_const z );
      -- Since $1/(1 - α) ≥ 1$ (as $0 < α < 1$), we can multiply both sides of the inequality by $(1 / (1 - α))$ to obtain the desired result.
      have h_mul : (1 / (1 - α)) * (∫ ω, max ((X ω) - z) 0 ∂μ : ℝ) ≥ (∫ ω, max ((X ω) - z) 0 ∂μ : ℝ) := by
        exact le_mul_of_one_le_left ( MeasureTheory.integral_nonneg fun _ => le_max_right _ _ ) ( one_le_one_div ( by linarith ) ( by linarith ) );
      exact h_int_le.trans ( by unfold cvarAux; linarith )

/-- The range of `cvarAux` is bounded below on a probability space. -/
theorem cvarAux_bddBelow {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hXi : Integrable X μ) (hα : 0 < α) (hα1 : α < 1) :
    BddBelow (range (cvarAux μ X α)) :=
  ⟨∫ ω, X ω ∂μ, fun _ ⟨z, hz⟩ => hz ▸ cvarAux_ge_integral hXi hα hα1 z⟩

/-! ### Coercivity -/

/-- `F(z) → +∞` as `z → +∞`. -/
theorem cvarAux_tendsto_atTop {X : Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ]
    (_hXi : Integrable X μ) (hα1 : α < 1) :
    Tendsto (cvarAux μ X α) atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun b => ⟨b, fun z hz => le_add_of_le_of_nonneg hz ?_⟩
  exact mul_nonneg (one_div_nonneg.mpr (sub_nonneg.mpr hα1.le))
    (integral_nonneg fun _ => le_max_right _ _)

/-
`F(z) → +∞` as `z → -∞` on a probability space.
-/
theorem cvarAux_tendsto_atBot {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hXi : Integrable X μ) (hα : 0 < α) (hα1 : α < 1) :
    Tendsto (cvarAux μ X α) atBot atTop := by
      have h_lower_bound : ∀ z : ℝ, cvarAux μ X α z ≥ (∫ ω, X ω ∂μ - α * z) / (1 - α) := by
        intro z
        have h_lower_bound : ∫ ω, max (X ω - z) 0 ∂μ ≥ ∫ ω, (X ω - z) ∂μ := by
          refine' MeasureTheory.integral_mono _ _ fun ω => le_max_left _ _;
          · exact hXi.sub ( MeasureTheory.integrable_const _ );
          · exact MeasureTheory.Integrable.pos_part ( hXi.sub ( MeasureTheory.integrable_const z ) );
        rw [ MeasureTheory.integral_sub hXi ] at h_lower_bound <;> norm_num at *;
        unfold cvarAux;
        rw [ div_mul_eq_mul_div, add_div', div_le_div_iff_of_pos_right ] <;> nlinarith;
      refine' Filter.tendsto_atTop_mono h_lower_bound _;
      exact Filter.Tendsto.atTop_div_const ( by linarith ) ( Filter.tendsto_atTop_add_const_left _ _ <| Filter.tendsto_neg_atBot_atTop.comp <| Filter.tendsto_id.const_mul_atBot hα )

/-! ### Properties of VaR -/

/-
The quantile set `{z | α ≤ P(X ≤ z)}` is nonempty.
-/
theorem VaR_set_nonempty {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (_hX : Measurable X) (hα1 : α < 1) :
    { z : ℝ | α * (μ Set.univ).toReal ≤ (μ { ω | X ω ≤ z }).toReal }.Nonempty := by
      have h_tendsto : Filter.Tendsto (fun z => (μ {ω | X ω ≤ z}).toReal) Filter.atTop (nhds 1) := by
        have h_cdf : Filter.Tendsto (fun z => (μ {ω | X ω ≤ z})) Filter.atTop (nhds (μ Set.univ)) := by
          convert MeasureTheory.tendsto_measure_iUnion_atTop _;
          · ext ω; simp [Set.mem_iUnion];
            exact ⟨ X ω, le_rfl ⟩;
          · infer_instance;
          · exact fun x y hxy => Set.setOf_subset_setOf.2 fun ω hω => le_trans hω hxy;
        simpa using ENNReal.tendsto_toReal ( MeasureTheory.measure_ne_top _ _ ) |> Filter.Tendsto.comp <| h_cdf;
      exact Filter.Eventually.exists ( h_tendsto.eventually ( le_mem_nhds ( by norm_num; linarith ) ) )

/-
The quantile set is bounded below.
-/
theorem VaR_set_bddBelow {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : Measurable X) (hα : 0 < α) :
    BddBelow { z : ℝ | α * (μ Set.univ).toReal ≤ (μ { ω | X ω ≤ z }).toReal } := by
      -- The CDF P(X ≤ z) → 0 as z → -∞. Use tendsto_measure_iInter_atBot to show μ({X ≤ z}) → 0 as z → -∞.
      have h_cdf_zero : Filter.Tendsto (fun z => (μ {ω | X ω ≤ z}).toReal) Filter.atBot (nhds 0) := by
        convert ENNReal.tendsto_toReal ( show ( 0 : ENNReal ) ≠ ⊤ from by simp +decide ) |> Filter.Tendsto.comp <| ?_ using 2;
        convert MeasureTheory.tendsto_measure_iInter_atBot _ _ _;
        · rw [ show ⋂ n : ℝ, { ω | X ω ≤ n } = ∅ by rw [ Set.eq_empty_iff_forall_notMem ] ; intro ω hω; exact absurd ( Set.mem_iInter.mp hω ( X ω - 1 ) ) ( by norm_num ) ] ; simp +decide;
        · infer_instance;
        · exact fun i => measurableSet_le hX measurable_const |> MeasurableSet.nullMeasurableSet;
        · exact fun x y hxy => Set.setOf_subset_setOf.2 fun ω hω => le_trans hω hxy;
        · exact ⟨ 0, ne_of_lt ( MeasureTheory.measure_lt_top _ _ ) ⟩;
      have := h_cdf_zero.eventually ( gt_mem_nhds <| show 0 < α * ( μ Set.univ |> ENNReal.toReal ) by simp +decide [ hα ] );
      rw [ Filter.eventually_atBot ] at this; rcases this with ⟨ M, hM ⟩ ; exact ⟨ M, fun z hz => not_lt.1 fun contra => not_le_of_gt ( hM z contra.le ) hz ⟩ ;

/-
For `z < VaR`, `P(X ≤ z) < α` (on a probability space).
-/
theorem measure_lt_alpha_of_lt_VaR {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : Measurable X) (hα : 0 < α) (_hα1 : α < 1) {z : ℝ} (hz : z < VaR μ X α) :
    (μ { ω | X ω ≤ z }).toReal < α := by
      contrapose! hz;
      exact csInf_le ( VaR_set_bddBelow hX hα ) ( by simpa using hz )

/-
`P(X ≤ VaR) ≥ α` (right-continuity of CDF at VaR).
-/
theorem measure_le_VaR_ge_alpha {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : Measurable X) (hα : 0 < α) (hα1 : α < 1) :
    α ≤ (μ { ω | X ω ≤ VaR μ X α }).toReal := by
      -- By definition of $VaR$, we know that for any $\epsilon > 0$, $P(X \leq VaR + \epsilon) \geq \alpha$.
      have hVaR_eps : ∀ ε > 0, (μ {ω | X ω ≤ VaR μ X α + ε}).toReal ≥ α := by
        intro ε εpos
        have h_exists : ∃ z ∈ {z : ℝ | α * (μ Set.univ).toReal ≤ (μ {ω | X ω ≤ z}).toReal}, z < VaR μ X α + ε := by
          exact exists_lt_of_csInf_lt ( VaR_set_nonempty hX hα1 ) ( lt_add_of_pos_right _ εpos );
        obtain ⟨ z, hz₁, hz₂ ⟩ := h_exists; exact le_trans ( by simpa using hz₁ ) ( ENNReal.toReal_mono ( MeasureTheory.measure_ne_top _ _ ) ( MeasureTheory.measure_mono ( show { ω | X ω ≤ z } ⊆ { ω | X ω ≤ VaR μ X α + ε } from fun ω hω => le_trans hω.out hz₂.le ) ) ) ;
      -- By the right-continuity of the measure, we have that $\lim_{n \to \infty} \mu {ω | (X ω) ≤ VaR μ X α + \frac{1}{n}} = \mu {ω | (X ω) ≤ VaR μ X α}$.
      have h_lim : Filter.Tendsto (fun n : ℕ => μ {ω | (X ω) ≤ VaR μ X α + (1 / (n + 1 : ℝ))}) Filter.atTop (nhds (μ {ω | (X ω) ≤ VaR μ X α})) := by
        -- Using the continuity of the measure from above, we have:
        have h_cont : Filter.Tendsto (fun n : ℕ => μ (⋂ k ≤ n, {ω | (X ω) ≤ VaR μ X α + (1 / (k + 1 : ℝ))})) Filter.atTop (nhds (μ {ω | (X ω) ≤ VaR μ X α})) := by
          convert MeasureTheory.tendsto_measure_iInter_atTop _ _ _;
          · ext ω; simp [Set.mem_iInter];
            exact ⟨ fun h i j hij => le_add_of_le_of_nonneg h <| by positivity, fun h => le_of_forall_pos_le_add fun ε εpos => by have := h ⌈ε⁻¹⌉₊ ⌈ε⁻¹⌉₊ le_rfl; nlinarith [ Nat.le_ceil ( ε⁻¹ ), mul_inv_cancel₀ ( ne_of_gt εpos ), inv_mul_cancel₀ ( show ( ⌈ε⁻¹⌉₊ : ℝ ) + 1 ≠ 0 by positivity ) ] ⟩;
          · infer_instance;
          · exact fun n => MeasurableSet.nullMeasurableSet ( MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => measurableSet_le hX measurable_const );
          · exact fun n m hnm => Set.biInter_subset_biInter_left fun k hk => le_trans hk hnm;
          · exact ⟨ 0, ne_of_lt ( MeasureTheory.measure_lt_top _ _ ) ⟩;
        refine' h_cont.congr' _;
        filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn;
        congr with ω ; simp +decide [ Set.mem_iInter ];
        exact ⟨ fun h => h n le_rfl, fun h i hi => le_trans h ( by gcongr ) ⟩;
      exact le_of_tendsto_of_tendsto' tendsto_const_nhds ( ENNReal.tendsto_toReal ( MeasureTheory.measure_ne_top _ _ ) |> Filter.Tendsto.comp <| h_lim ) fun n => hVaR_eps _ <| by positivity;

/-! ### F is nondecreasing above VaR -/

/-
For `z ≥ VaR`, `F(z) ≥ F(VaR)`.
-/
theorem cvarAux_nondecreasing_above_VaR {X : Ω → ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (hX : Measurable X) (hXi : Integrable X μ)
    (hα : 0 < α) (hα1 : α < 1) {z : ℝ} (hz : VaR μ X α ≤ z) :
    cvarAux μ X α (VaR μ X α) ≤ cvarAux μ X α z := by
      unfold cvarAux;
      -- Using the upper bound from integral_posPart_upper_bound with z₁ = VaR, z₂ = z:
      have h_upper_bound : ∫ ω, max (X ω - VaR μ X α) 0 ∂μ - ∫ ω, max (X ω - z) 0 ∂μ ≤ (z - VaR μ X α) * (μ { ω | VaR μ X α < X ω }).toReal := by
        have h_upper_bound : ∀ ω, max (X ω - VaR μ X α) 0 - max (X ω - z) 0 ≤ (z - VaR μ X α) * (if VaR μ X α < X ω then 1 else 0) := by
          intro ω; split_ifs <;> cases max_cases ( X ω - VaR μ X α ) 0 <;> cases max_cases ( X ω - z ) 0 <;> linarith;
        rw [ ← MeasureTheory.integral_sub ];
        · convert MeasureTheory.integral_mono _ _ h_upper_bound;
          · erw [ MeasureTheory.integral_const_mul, MeasureTheory.integral_indicator ( measurableSet_lt measurable_const hX ) ] ; aesop;
          · exact MeasureTheory.Integrable.sub ( MeasureTheory.Integrable.pos_part ( hXi.sub ( MeasureTheory.integrable_const _ ) ) ) ( MeasureTheory.Integrable.pos_part ( hXi.sub ( MeasureTheory.integrable_const _ ) ) );
          · refine' MeasureTheory.Integrable.const_mul _ _;
            refine' MeasureTheory.Integrable.indicator _ _;
            · norm_num;
            · exact measurableSet_lt measurable_const hX;
        · exact MeasureTheory.Integrable.pos_part ( hXi.sub ( MeasureTheory.integrable_const _ ) );
        · exact MeasureTheory.Integrable.pos_part ( hXi.sub ( MeasureTheory.integrable_const z ) );
      -- Using the fact that $\mu(\{X > VaR\}) \leq 1 - \alpha$, we get:
      have h_measure_bound : (μ { ω | VaR μ X α < X ω }).toReal ≤ 1 - α := by
        have h_measure_bound : (μ { ω | VaR μ X α < X ω }) = μ Set.univ - μ { ω | X ω ≤ VaR μ X α } := by
          rw [ ← MeasureTheory.measure_diff ] <;> norm_num [ Set.compl_setOf ];
          · exact congr_arg _ ( by ext; simp +decide [ not_le ] );
          · exact measurableSet_le hX measurable_const |> MeasurableSet.nullMeasurableSet;
        rw [ h_measure_bound, ENNReal.toReal_sub_of_le ] <;> norm_num;
        · linarith [ show ( μ { ω | X ω ≤ VaR μ X α } |> ENNReal.toReal ) ≥ α by simpa using measure_le_VaR_ge_alpha hX hα hα1 ];
        · exact le_trans ( MeasureTheory.measure_mono ( Set.subset_univ _ ) ) ( by norm_num );
      field_simp;
      rw [ add_div', add_div', div_le_div_iff_of_pos_right ] <;> nlinarith

/-! ### F is nonincreasing below VaR -/

/-
For `z₁ ≤ z₂ < VaR`, `F(z₂) ≤ F(z₁)`.
-/
theorem cvarAux_nonincreasing_below_VaR {X : Ω → ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (hX : Measurable X) (hXi : Integrable X μ)
    (hα : 0 < α) (hα1 : α < 1) {z₁ z₂ : ℝ} (hz12 : z₁ ≤ z₂) (hz2 : z₂ < VaR μ X α) :
    cvarAux μ X α z₂ ≤ cvarAux μ X α z₁ := by
      -- Hence: F(z₂) - F(z₁) ≤ (z₂ - z₁) + 1/(1-α) · (-(z₂ - z₁) · μ({X > z₂}).toReal)
      have h_diff : cvarAux μ X α z₂ - cvarAux μ X α z₁ ≤ (z₂ - z₁) + 1 / (1 - α) * (-(z₂ - z₁) * (μ { ω | z₂ < X ω }).toReal) := by
        unfold cvarAux;
        have := integral_posPart_lower_bound hX hXi hz12;
        nlinarith [ one_div_mul_cancel ( by linarith : ( 1 - α ) ≠ 0 ) ];
      -- Apply the lemma measure_lt_alpha_of_lt_VaR.
      have h_measure_lt_alpha : (μ { ω | z₂ < X ω }).toReal > 1 - α := by
        have := measure_lt_alpha_of_lt_VaR hX hα hα1 hz2;
        rw [ show { ω | z₂ < X ω } = ( Set.univ \ { ω | X ω ≤ z₂ } ) by ext; simp +decide, MeasureTheory.measure_diff ] <;> norm_num;
        · rw [ ENNReal.toReal_sub_of_le ] <;> norm_num;
          · exact this;
          · exact le_trans ( MeasureTheory.measure_mono ( Set.subset_univ _ ) ) ( by norm_num );
        · exact measurableSet_le hX measurable_const |> MeasurableSet.nullMeasurableSet;
      norm_num +zetaDelta at *;
      nlinarith [ inv_mul_cancel_left₀ ( by linarith : ( 1 - α ) ≠ 0 ) ( z₁ - z₂ ), mul_le_mul_of_nonneg_left h_measure_lt_alpha.le ( sub_nonneg.mpr hz12 ) ]

/-! ### The infimum is attained at VaR -/

/-
`F(z) ≥ F(VaR)` for all `z ≤ VaR`. Combines nonincreasing on `(-∞, VaR)`
    with continuity of `F` at `VaR`.
-/
theorem cvarAux_ge_VaR_left {X : Ω → ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (hX : Measurable X) (hXi : Integrable X μ)
    (hα : 0 < α) (hα1 : α < 1) {z : ℝ} (hz : z ≤ VaR μ X α) :
    cvarAux μ X α (VaR μ X α) ≤ cvarAux μ X α z := by
      by_contra h_contra;
      -- Choose a sequence $z_n$ such that $z_n \to VaR$ and $z_n < VaR$ for all $n$.
      obtain ⟨z_n, hz_n⟩ : ∃ z_n : ℕ → ℝ, (∀ n, z_n n < VaR μ X α) ∧ Filter.Tendsto z_n Filter.atTop (nhds (VaR μ X α)) ∧ ∀ n, z_n n ≥ z := by
        refine' ⟨ fun n => VaR μ X α - 1 / ( n + 1 ) * ( VaR μ X α - z ), _, _, _ ⟩ <;> norm_num;
        · exact fun n => mul_pos ( inv_pos.mpr ( Nat.cast_add_one_pos n ) ) ( sub_pos.mpr ( lt_of_le_of_ne hz ( by rintro rfl; exact h_contra le_rfl ) ) );
        · exact le_trans ( tendsto_const_nhds.sub ( Filter.Tendsto.mul ( tendsto_inv_atTop_zero.comp ( Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) tendsto_const_nhds ) ) ( by norm_num );
        · exact fun n => by nlinarith [ inv_mul_cancel_left₀ ( by linarith : ( n : ℝ ) + 1 ≠ 0 ) ( VaR μ X α - z ) ] ;
      -- By the properties of the auxiliary function, we have $F(z_n) \leq F(z)$ for all $n$.
      have hF_le : ∀ n, cvarAux μ X α (z_n n) ≤ cvarAux μ X α z := by
        exact fun n => cvarAux_nonincreasing_below_VaR hX hXi hα hα1 ( hz_n.2.2 n ) ( hz_n.1 n );
      exact h_contra <| le_of_tendsto_of_tendsto' ( cvarAux_continuous hX hXi hα hα1 |> Continuous.continuousAt |> fun h => h.tendsto.comp hz_n.2.1 ) tendsto_const_nhds hF_le

/-- The auxiliary function `F` attains its infimum at `z = VaR_α(X)`. -/
theorem CVaR_eq_cvarAux_VaR {X : Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ]
    [IsProbabilityMeasure μ]
    (hX : Measurable X) (hXi : Integrable X μ)
    (hα : 0 < α) (hα1 : α < 1) :
    CVaR μ X α = cvarAux μ X α (VaR μ X α) := by
  apply le_antisymm
  · exact ciInf_le (cvarAux_bddBelow hXi hα hα1) (VaR μ X α)
  · apply le_ciInf; intro z
    by_cases hz : z ≤ VaR μ X α
    · exact cvarAux_ge_VaR_left hX hXi hα hα1 hz
    · exact cvarAux_nondecreasing_above_VaR hX hXi hα hα1 (not_le.mp hz |>.le)

/-! ### Full dual representation -/

/-- **Rockafellar–Uryasev dual representation.**
    `CVaR_α(X) = inf_z { z + (1/(1-α)) ∫ max(X-z, 0) dμ }`.
    Definitional by our choice of `CVaR`. -/
theorem CVaR_dual_rep {X : Ω → ℝ} {μ : Measure Ω}
    (_hα : 0 < α) (_hα1 : α < 1) :
    CVaR μ X α = ⨅ z : ℝ, (z + (1 / (1 - α)) * ∫ ω, max (X ω - z) 0 ∂μ) := by
  rfl

end