/-
Pythia.HowardRamdasCS — formalised self-normalized CS
construction (Howard et al. 2021).

## Refactoring notes (monotone_once_fired / Option b)

The original `StoppingRule` structure required a
`monotone_once_fired` field: once `decide m t = true`, the rule
must stay fired at `t+1` on the **same** trajectory.  For the
Howard-Ramdas rule with a strictly increasing boundary, this is
FALSE for arbitrary trajectories (a trajectory can cross the
boundary at `t` and fall below at `t+1`).  This is the
*Specification Incompatibility Theorem*.

Following option (b) from the design note, we **drop** the
`StoppingRule` structure entirely and define stopping as the
first-hitting event directly.

## Boundary choice

The boundary `σ √(2 t log(t(t+1)/α))` gives per-time Chernoff
bounds `α/(t(t+1))` whose telescoping sum equals `α`, enabling
an infinite-horizon coverage guarantee via union bound.
-/

import Mathlib
import Pythia.Basic
import Pythia.SubGaussianMG

namespace Pythia

open MeasureTheory ProbabilityTheory

/-- Howard-Ramdas boundary at step `t` with sub-Gaussian parameter
`sigma` and one-sided coverage `alpha`.  For `t ≥ 1`, equals
`sigma * √(2 t log(t(t+1)/α))`.  At `t = 0` set to `sigma`. -/
noncomputable def hrBoundary (sigma alpha : ℝ) (t : ℕ) : ℝ :=
  if t = 0 then sigma
  else sigma * Real.sqrt (2 * t * Real.log (t * (t + 1) / alpha))

/-! ### Helper lemmas -/

/-- `hrBoundary 1 alpha 0 = 1`. -/
lemma hrBoundary_zero (alpha : ℝ) : hrBoundary 1 alpha 0 = 1 := by
  simp [hrBoundary]

/-
For `t ≥ 1` and `0 < alpha < 1`, the boundary is positive.
-/
lemma hrBoundary_pos (alpha : ℝ) (halpha : 0 < alpha ∧ alpha < 1)
    (t : ℕ) (ht : 1 ≤ t) : 0 < hrBoundary 1 alpha t := by
  unfold hrBoundary;
  exact if_neg ( by linarith ) |> fun h => h.symm ▸ mul_pos zero_lt_one ( Real.sqrt_pos.mpr ( mul_pos ( by positivity ) ( Real.log_pos ( by rw [ lt_div_iff₀ halpha.1 ] ; nlinarith [ show ( t : ℝ ) ≥ 1 by norm_cast ] ) ) ) )

/-
Key computation: for `t ≥ 1`,
`exp(−(hrBoundary 1 α t)² / (2t)) = α / (t(t+1))`.
-/
lemma hrBoundary_exp_eq (alpha : ℝ) (halpha : 0 < alpha ∧ alpha < 1)
    (t : ℕ) (ht : 1 ≤ t) :
    Real.exp (-(hrBoundary 1 alpha t) ^ 2 / (2 * 1 ^ 2 * (t : ℝ))) =
      alpha / ((t : ℝ) * ((t : ℝ) + 1)) := by
  unfold hrBoundary;
  rw [ if_neg ( by positivity ), one_mul, Real.sq_sqrt ( mul_nonneg ( by positivity ) ( Real.log_nonneg ( by rw [ le_div_iff₀ halpha.1 ] ; nlinarith [ show ( t : ℝ ) ≥ 1 by norm_cast ] ) ) ) ] ; ring;
  rw [ mul_right_comm, mul_inv_cancel₀ ( by positivity ), one_mul, Real.exp_neg, Real.exp_log ( by nlinarith [ show ( t : ℝ ) ≥ 1 by norm_cast, inv_pos.mpr halpha.1 ] ) ] ; ring;
  rw [ inv_eq_iff_eq_inv ] ; norm_num ; ring

/-
Finite partial sum of the telescoping series.
-/
lemma telescope_partial_sum (n : ℕ) :
    ∑ k ∈ Finset.range n, (1 : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) =
      1 - 1 / ((n : ℝ) + 1) := by
  induction n <;> push_cast [ Finset.sum_range_succ ] <;> norm_num ; ring;
  grind

/-- The telescoping partial sum is at most 1. -/
lemma telescope_partial_sum_le_one (n : ℕ) :
    ∑ k ∈ Finset.range n, (1 : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) ≤ 1 := by
  have := telescope_partial_sum n
  linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) from by positivity]

/-
Per-time bound: `μ{M_t ≥ b(t)} ≤ α/(t(t+1))` for `t ≥ 1`.
Uses `ville_ineq` with `τ = b(t)` and `N = t`.
-/
lemma hr_per_time_bound
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : SubGaussianMG 1 𝓕 μ)
    (hM0 : ∀ᵐ ω ∂μ, M.process 0 ω = 0)
    (alpha : ℝ) (halpha : 0 < alpha ∧ alpha < 1)
    (t : ℕ) (ht : 1 ≤ t) :
    μ {ω | M.process t ω ≥ hrBoundary 1 alpha t} ≤
      ENNReal.ofReal (alpha / ((t : ℝ) * ((t : ℝ) + 1))) := by
  refine' le_trans _ ( ville_ineq M ( hrBoundary 1 alpha t ) ( hrBoundary_pos alpha halpha t ht ) t ht hM0 |> le_trans <| _ );
  · exact MeasureTheory.measure_mono fun ω hω => ⟨ t, le_rfl, hω ⟩;
  · rw [ hrBoundary_exp_eq alpha halpha t ht ]

/-
The event `{M_0 ≥ hrBoundary 1 α 0}` has measure 0 since
`M_0 = 0` a.s. and `hrBoundary 1 α 0 = 1 > 0`.
-/
lemma hr_time_zero_null
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : SubGaussianMG 1 𝓕 μ)
    (hM0 : ∀ᵐ ω ∂μ, M.process 0 ω = 0)
    (alpha : ℝ) (_halpha : 0 < alpha ∧ alpha < 1) :
    μ {ω | M.process 0 ω ≥ hrBoundary 1 alpha 0} = 0 := by
  unfold hrBoundary;
  rw [ MeasureTheory.measure_eq_zero_iff_ae_notMem ];
  filter_upwards [ hM0 ] with ω hω using by norm_num [ hω ]

/-
**Admissibility of the Howard-Ramdas rule** (main theorem).

For every sub-Gaussian martingale `M` with parameter `σ = 1`
starting at 0 a.s., and any `α ∈ (0,1)`, the probability that
the process ever crosses the Howard-Ramdas boundary is at most `α`:

    `μ {ω | ∃ t, M_t ω ≥ hrBoundary 1 α t} ≤ α`

Proof: countable union bound + per-time Chernoff bounds + telescoping
series `∑ α/(t(t+1)) = α`.
-/
theorem hrStoppingRule_admissible
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : SubGaussianMG 1 𝓕 μ)
    (hM0 : ∀ᵐ ω ∂μ, M.process 0 ω = 0)
    (alpha : ℝ) (halpha : 0 < alpha ∧ alpha < 1) :
    μ {ω | ∃ t, M.process t ω ≥ hrBoundary 1 alpha t} ≤
      ENNReal.ofReal alpha := by
  -- Apply the measure of the union bound to bound the probability.
  have h_union_bound : μ {ω | ∃ t, M.process t ω ≥ hrBoundary 1 alpha t} ≤ ∑' t : ℕ, μ {ω | M.process t ω ≥ hrBoundary 1 alpha t} := by
    rw [ show { ω | ∃ t, M.process t ω ≥ hrBoundary 1 alpha t } = ⋃ t, { ω | M.process t ω ≥ hrBoundary 1 alpha t } by ext; aesop ];
    exact measure_iUnion_le fun i => {ω | M.process i ω ≥ hrBoundary 1 alpha i};
  refine' le_trans h_union_bound ( le_trans ( ENNReal.tsum_le_tsum fun t => _ ) _ );
  use fun t => if t = 0 then 0 else ENNReal.ofReal ( alpha / ( t * ( t + 1 ) ) );
  · by_cases ht : t = 0;
    · simp +decide [ ht, hr_time_zero_null M hM0 alpha halpha ];
    · simpa [ ht ] using hr_per_time_bound M hM0 alpha halpha t ( Nat.pos_of_ne_zero ht );
  · -- The series $\sum_{t=1}^{\infty} \frac{\alpha}{t(t+1)}$ is a telescoping series.
    have h_telescoping : ∑' t : ℕ, (if t = 0 then 0 else alpha / ((t : ℝ) * ((t : ℝ) + 1))) = alpha := by
      have h_telescoping : ∀ n : ℕ, ∑ t ∈ Finset.range (n + 1), (if t = 0 then 0 else alpha / ((t : ℝ) * ((t : ℝ) + 1))) = alpha * (1 - 1 / (n + 1)) := by
        intro n; induction n <;> simp_all +decide [ Finset.sum_range_succ ] ; ring;
        -- Combine and simplify the terms on the left-hand side.
        field_simp
        ring;
      refine' HasSum.tsum_eq _;
      rw [ hasSum_iff_tendsto_nat_of_nonneg ];
      · rw [ ← Filter.tendsto_add_atTop_iff_nat 1 ];
        simpa only [ h_telescoping ] using le_trans ( tendsto_const_nhds.mul ( tendsto_const_nhds.sub ( tendsto_one_div_add_atTop_nhds_zero_nat ) ) ) ( by norm_num );
      · exact fun n => by split_ifs <;> first | positivity | exact div_nonneg halpha.1.le ( by positivity ) ;
    rw [ ← h_telescoping, ENNReal.ofReal_tsum_of_nonneg ];
    · exact ENNReal.tsum_le_tsum fun n => by aesop;
    · exact fun n => by split_ifs <;> first | positivity | exact div_nonneg halpha.1.le ( by positivity ) ;
    · exact ( by contrapose! h_telescoping; erw [ tsum_eq_zero_of_not_summable h_telescoping ] ; linarith )

end Pythia