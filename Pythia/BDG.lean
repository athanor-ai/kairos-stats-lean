/-
Pythia.BDG — Burkholder-Davis-Gundy inequality at p = 2 for discrete-time martingales.

The main result `bdg_discrete_l2` establishes that for a square-integrable martingale M
with M_0 = 0 and quadratic variation [M]_N = ∑_{k<N} (ΔM_k)², we have

  E[(sup_{k≤N} |M_k|)²] ≤ 4 · E[[M]_N]   and   E[[M]_N] ≤ E[(sup_{k≤N} |M_k|)²]

The proof combines:
  • Orthogonality of martingale increments: E[ΔM_j · ΔM_k] = 0 for j ≠ k
  • The identity E[M_N²] = E[[M]_N]
  • Doob's L² maximal inequality: E[sup M_k²] ≤ 4 E[M_N²]
-/
import Mathlib

namespace Pythia

open MeasureTheory Filter Finset
open scoped BigOperators NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
variable {𝓕 : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}

/-! ### Running maximum and its properties -/

/-
|M_k ω| ≤ sSup of the range for any k in Fin (N+1).
-/
lemma abs_le_sSup_range (M : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) (k : Fin (N + 1)) :
    |M k.val ω| ≤ sSup (Set.range (fun i : Fin (N + 1) => |M i.val ω|)) := by
  exact le_csSup ( Set.finite_range _ |> Set.Finite.bddAbove ) ( Set.mem_range_self _ )

/-
The sSup of absolute values is non-negative.
-/
lemma sSup_range_nonneg (M : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) :
    0 ≤ sSup (Set.range (fun k : Fin (N + 1) => |M k.val ω|)) := by
  -- The set of absolute values is non-negative, so its supremum is also non-negative.
  apply Real.sSup_nonneg;
  grind +qlia

/-
The sSup of absolute values as a function of ω is measurable.
-/
lemma measurable_sSup_abs (hM : Martingale M 𝓕 μ) (N : ℕ) :
    Measurable (fun ω => sSup (Set.range (fun k : Fin (N + 1) => |M k.val ω|))) := by
  -- The supremum of a finite set of measurable functions is measurable.
  have h_sup_measurable : ∀ (f : Fin (N + 1) → Ω → ℝ), (∀ k, Measurable (f k)) → Measurable (fun ω => sSup (Set.range (fun k : Fin (N + 1) => f k ω))) := by
    exact?;
  convert h_sup_measurable _ _;
  have h_adapted : ∀ k, MeasureTheory.StronglyMeasurable (M k) := by
    have := hM.stronglyMeasurable;
    exact?;
  exact fun k => ( h_adapted k |> StronglyMeasurable.measurable |> Measurable.norm )

/-
The square of the running max is integrable.
-/
lemma integrable_sSup_sq (hM : Martingale M 𝓕 μ)
    (hint : ∀ n, Integrable (fun ω => (M n ω) ^ 2) μ) (N : ℕ) :
    Integrable (fun ω => (sSup (Set.range (fun k : Fin (N + 1) => |M k.val ω|))) ^ 2) μ := by
  -- By definition of integrability, we need to show that the function is bounded by an integrable function.
  have h_bound : ∀ ω, (sSup (Set.range (fun k : Fin (N + 1) => |M k ω|))) ^ 2 ≤ (∑ k : Fin (N + 1), (M k.val ω) ^ 2) * (N + 1) := by
    intro ω
    have h_bound : ∀ k : Fin (N + 1), |M k ω| ≤ Real.sqrt (∑ k : Fin (N + 1), M k.val ω ^ 2) := by
      exact fun k => Real.abs_le_sqrt ( Finset.single_le_sum ( fun i _ => sq_nonneg ( M ( i : Fin ( N + 1 ) ) ω ) ) ( Finset.mem_univ k ) );
    refine' le_trans ( pow_le_pow_left₀ ( by apply_rules [ Real.sSup_nonneg ] ; rintro x ⟨ k, rfl ⟩ ; positivity ) ( csSup_le ( Set.range_nonempty _ ) ( Set.forall_mem_range.2 h_bound ) ) 2 ) _;
    rw [ Real.sq_sqrt ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ] ; exact le_mul_of_one_le_right ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ( by linarith );
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun ω => ( ∑ k : Fin ( N + 1 ), M k.val ω ^ 2 ) * ( N + 1 );
  · fun_prop;
  · -- The square of the running max is measurable.
    have h_meas : Measurable (fun ω => sSup (Set.range (fun k : Fin (N + 1) => |M k.val ω|))) := by
      exact?;
    exact h_meas.pow_const 2 |> Measurable.aestronglyMeasurable;
  · filter_upwards [ ] using fun ω => by rw [ Real.norm_of_nonneg ( sq_nonneg _ ) ] ; exact h_bound ω

/-! ### Orthogonality of martingale increments -/

/-
For a martingale M and j + 1 ≤ k, the increments ΔM_j and ΔM_k are orthogonal in L².
-/
lemma martingale_increment_orthogonal (hM : Martingale M 𝓕 μ)
    (hint : ∀ n, Integrable (fun ω => (M n ω) ^ 2) μ)
    {j k : ℕ} (hjk : j + 1 ≤ k) :
    ∫ ω, (M (j + 1) ω - M j ω) * (M (k + 1) ω - M k ω) ∂μ = 0 := by
  -- Apply the tower property to rewrite the integrand.
  have h_tower : ∫ ω, (M (j + 1) ω - M j ω) * (M (k + 1) ω - M k ω) ∂μ = ∫ ω, (M (j + 1) ω - M j ω) * (MeasureTheory.condExp (𝓕 k) μ (fun ω => M (k + 1) ω - M k ω) ω) ∂μ := by
    have h_tower : ∫ ω, (M (j + 1) ω - M j ω) * (M (k + 1) ω - M k ω) ∂μ = ∫ ω, MeasureTheory.condExp (𝓕 k) μ (fun ω => (M (j + 1) ω - M j ω) * (M (k + 1) ω - M k ω)) ω ∂μ := by
      rw [ MeasureTheory.integral_condExp ];
    rw [ h_tower, MeasureTheory.integral_congr_ae ];
    apply_rules [ MeasureTheory.condExp_mul_of_stronglyMeasurable_left ];
    · have := hM.stronglyMeasurable;
      exact StronglyMeasurable.sub ( this _ |> StronglyMeasurable.mono <| 𝓕.mono <| by linarith ) ( this _ |> StronglyMeasurable.mono <| 𝓕.mono <| by linarith );
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun ω => 2 * ( M ( j + 1 ) ω ^ 2 + M j ω ^ 2 + M ( k + 1 ) ω ^ 2 + M k ω ^ 2 );
      · exact MeasureTheory.Integrable.const_mul ( MeasureTheory.Integrable.add ( MeasureTheory.Integrable.add ( MeasureTheory.Integrable.add ( ‹∀ n, Integrable ( fun ω => M n ω ^ 2 ) μ› _ ) ( ‹∀ n, Integrable ( fun ω => M n ω ^ 2 ) μ› _ ) ) ( ‹∀ n, Integrable ( fun ω => M n ω ^ 2 ) μ› _ ) ) ( ‹∀ n, Integrable ( fun ω => M n ω ^ 2 ) μ› _ ) ) _;
      · have h_aestronglyMeasurable : ∀ n, AEStronglyMeasurable (fun ω => M n ω) μ := by
          exact fun n => hM.stronglyMeasurable n |> fun h => h.aestronglyMeasurable.mono ( 𝓕.le n );
        exact AEStronglyMeasurable.mul ( AEStronglyMeasurable.sub ( h_aestronglyMeasurable _ ) ( h_aestronglyMeasurable _ ) ) ( AEStronglyMeasurable.sub ( h_aestronglyMeasurable _ ) ( h_aestronglyMeasurable _ ) );
      · filter_upwards [ ] with ω using abs_le.mpr ⟨ by norm_num; nlinarith only [ sq_nonneg ( M ( j + 1 ) ω - M j ω ), sq_nonneg ( M ( k + 1 ) ω - M k ω ), sq_nonneg ( M ( j + 1 ) ω + M j ω ), sq_nonneg ( M ( k + 1 ) ω + M k ω ) ], by norm_num; nlinarith only [ sq_nonneg ( M ( j + 1 ) ω - M j ω ), sq_nonneg ( M ( k + 1 ) ω - M k ω ), sq_nonneg ( M ( j + 1 ) ω + M j ω ), sq_nonneg ( M ( k + 1 ) ω + M k ω ) ] ⟩;
    · exact MeasureTheory.Integrable.sub ( hM.integrable _ ) ( hM.integrable _ );
  -- By the properties of conditional expectation, we know that $\mathbb{E}[M_{k+1} - M_k \mid \mathcal{F}_k] = 0$.
  have h_cond_exp : ∀ᵐ ω ∂μ, MeasureTheory.condExp (𝓕 k) μ (fun ω => M (k + 1) ω - M k ω) ω = 0 := by
    have h_cond_exp : ∀ᵐ ω ∂μ, MeasureTheory.condExp (𝓕 k) μ (fun ω => M (k + 1) ω - M k ω) ω = MeasureTheory.condExp (𝓕 k) μ (fun ω => M (k + 1) ω) ω - MeasureTheory.condExp (𝓕 k) μ (fun ω => M k ω) ω := by
      apply_rules [ MeasureTheory.condExp_sub ];
      · exact hM.integrable _;
      · exact hM.integrable _;
    have := hM.2;
    filter_upwards [ h_cond_exp, this k ( k + 1 ) ( Nat.le_succ _ ), this k k le_rfl ] with ω hω₁ hω₂ hω₃ using by aesop;
  exact h_tower.trans ( MeasureTheory.integral_eq_zero_of_ae ( h_cond_exp.mono fun ω hω => by simp +decide [ hω ] ) )

/-! ### Quadratic variation identity -/

/-
E[M_N²] = E[[M]_N]: the second moment of a martingale starting at 0
equals the expected quadratic variation.
-/
set_option maxHeartbeats 800000 in
lemma integral_sq_eq_integral_qv (hM : Martingale M 𝓕 μ)
    (hint : ∀ n, Integrable (fun ω => (M n ω) ^ 2) μ)
    (hM0 : ∀ᵐ ω ∂μ, M 0 ω = 0) (N : ℕ) :
    ∫ ω, (M N ω) ^ 2 ∂μ =
      ∫ ω, ∑ k ∈ Finset.range N, (M (k + 1) ω - M k ω) ^ 2 ∂μ := by
  -- Use the fact that $|M_N(M_{k+1} - M_k)|$ is bounded by $M_N^2 + (M_{k+1} - M_k)^2 / 2$.
  have h_bound : ∀ n, Integrable (fun ω => M n ω * (M (n + 1) ω - M n ω)) μ := by
    intro n;
    refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun ω => 2 * ( M n ω ^ 2 + M ( n + 1 ) ω ^ 2 );
    · fun_prop;
    · have := hM.integrable n;
      exact this.1.mul ( hM.integrable ( n + 1 ) |> MeasureTheory.Integrable.aestronglyMeasurable |> fun h => h.sub this.1 );
    · filter_upwards [ ] with ω using abs_le.mpr ⟨ by nlinarith only [ sq_nonneg ( M n ω - M ( n + 1 ) ω ), sq_nonneg ( M n ω + M ( n + 1 ) ω ) ], by nlinarith only [ sq_nonneg ( M n ω - M ( n + 1 ) ω ), sq_nonneg ( M n ω + M ( n + 1 ) ω ) ] ⟩;
  -- Use the fact that $M_n$ is a martingale to show that the cross-terms vanish.
  have h_cross : ∀ n, ∫ ω, M n ω * (M (n + 1) ω - M n ω) ∂μ = 0 := by
    intro n
    have h_cond_exp : ∫ ω, M n ω * (M (n + 1) ω - M n ω) ∂μ = ∫ ω, M n ω * (condExp (𝓕 n) μ (fun ω => M (n + 1) ω - M n ω) ω) ∂μ := by
      have h_cond_exp : ∫ ω, M n ω * (M (n + 1) ω - M n ω) ∂μ = ∫ ω, condExp (𝓕 n) μ (fun ω => M n ω * (M (n + 1) ω - M n ω)) ω ∂μ := by
        rw [ MeasureTheory.integral_condExp ];
      rw [ h_cond_exp ];
      rw [ MeasureTheory.integral_congr_ae ];
      apply_rules [ MeasureTheory.condExp_mul_of_stronglyMeasurable_left ];
      · exact hM.stronglyMeasurable n;
      · exact MeasureTheory.Integrable.sub ( hM.integrable _ ) ( hM.integrable _ );
    have h_cond_exp_zero : ∀ᵐ ω ∂μ, condExp (𝓕 n) μ (fun ω => M (n + 1) ω - M n ω) ω = 0 := by
      have := hM.2 n;
      have h_cond_exp_zero : ∀ᵐ ω ∂μ, condExp (𝓕 n) μ (fun ω => M (n + 1) ω - M n ω) ω = condExp (𝓕 n) μ (fun ω => M (n + 1) ω) ω - condExp (𝓕 n) μ (fun ω => M n ω) ω := by
        apply_rules [ MeasureTheory.condExp_sub ];
        · exact hM.integrable _;
        · exact hM.integrable _;
      filter_upwards [ h_cond_exp_zero, this ( n + 1 ) ( Nat.le_succ _ ), this n le_rfl ] with ω hω₁ hω₂ hω₃ using by aesop;
    exact h_cond_exp.trans ( MeasureTheory.integral_eq_zero_of_ae ( h_cond_exp_zero.mono fun ω hω => by simp +decide [ hω ] ) );
  induction' N with N ih <;> simp_all +decide [ Finset.sum_range_succ ];
  · exact MeasureTheory.integral_eq_zero_of_ae ( hM0.mono fun ω hω => by simp +decide [ hω ] );
  · rw [ MeasureTheory.integral_add ];
    · rw [ ← ih, ← MeasureTheory.integral_add ];
      · rw [ show ( fun ω => M ( N + 1 ) ω ^ 2 ) = fun ω => M N ω ^ 2 + ( M ( N + 1 ) ω - M N ω ) ^ 2 + 2 * ( M N ω * ( M ( N + 1 ) ω - M N ω ) ) by ext; ring, MeasureTheory.integral_add, MeasureTheory.integral_add ];
        · rw [ MeasureTheory.integral_const_mul, h_cross, MulZeroClass.mul_zero, add_zero ];
        · exact?;
        · simp_rw +decide [ sub_sq ];
          apply_rules [ MeasureTheory.Integrable.add, MeasureTheory.Integrable.neg, MeasureTheory.Integrable.const_mul ];
          have h_integrable : Integrable (fun ω => M (N + 1) ω ^ 2 + M N ω ^ 2) μ := by
            exact MeasureTheory.Integrable.add ( ‹∀ n, MeasureTheory.Integrable ( fun ω => M n ω ^ 2 ) μ› _ ) ( ‹∀ n, MeasureTheory.Integrable ( fun ω => M n ω ^ 2 ) μ› _ );
          refine' h_integrable.mono' _ _;
          · have h_integrable : AEStronglyMeasurable (fun ω => M (N + 1) ω) μ ∧ AEStronglyMeasurable (fun ω => M N ω) μ := by
              exact ⟨ hM.integrable _ |> Integrable.aestronglyMeasurable, hM.integrable _ |> Integrable.aestronglyMeasurable ⟩;
            exact MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.aestronglyMeasurable_const ) h_integrable.1 ) h_integrable.2;
          · filter_upwards [ ] with ω using abs_le.mpr ⟨ by nlinarith only [ sq_nonneg ( M ( N + 1 ) ω - M N ω ), sq_nonneg ( M ( N + 1 ) ω + M N ω ) ], by nlinarith only [ sq_nonneg ( M ( N + 1 ) ω - M N ω ), sq_nonneg ( M ( N + 1 ) ω + M N ω ) ] ⟩;
        · simp_rw +decide [ sub_sq ];
          apply_rules [ MeasureTheory.Integrable.add, MeasureTheory.Integrable.neg, MeasureTheory.Integrable.mul_const, MeasureTheory.Integrable.const_mul ];
          have h_integrable : Integrable (fun ω => M (N + 1) ω ^ 2 + M N ω ^ 2) μ := by
            exact MeasureTheory.Integrable.add ( ‹∀ n, MeasureTheory.Integrable ( fun ω => M n ω ^ 2 ) μ› _ ) ( ‹∀ n, MeasureTheory.Integrable ( fun ω => M n ω ^ 2 ) μ› _ );
          refine' h_integrable.mono' _ _;
          · have h_integrable : AEStronglyMeasurable (fun ω => M (N + 1) ω) μ ∧ AEStronglyMeasurable (fun ω => M N ω) μ := by
              exact ⟨ hM.integrable _ |> Integrable.aestronglyMeasurable, hM.integrable _ |> Integrable.aestronglyMeasurable ⟩;
            exact MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.aestronglyMeasurable_const ) h_integrable.1 ) h_integrable.2;
          · filter_upwards [ ] with ω using abs_le.mpr ⟨ by nlinarith only [ sq_nonneg ( M ( N + 1 ) ω - M N ω ), sq_nonneg ( M ( N + 1 ) ω + M N ω ) ], by nlinarith only [ sq_nonneg ( M ( N + 1 ) ω - M N ω ), sq_nonneg ( M ( N + 1 ) ω + M N ω ) ] ⟩;
        · exact MeasureTheory.Integrable.const_mul ( h_bound N ) _;
      · exact?;
      · simp_rw +decide [ sub_sq ];
        apply_rules [ MeasureTheory.Integrable.add, MeasureTheory.Integrable.neg, MeasureTheory.Integrable.const_mul ];
        have h_integrable : Integrable (fun ω => M (N + 1) ω ^ 2 + M N ω ^ 2) μ := by
          exact MeasureTheory.Integrable.add ( ‹∀ n, MeasureTheory.Integrable ( fun ω => M n ω ^ 2 ) μ› _ ) ( ‹∀ n, MeasureTheory.Integrable ( fun ω => M n ω ^ 2 ) μ› _ );
        refine' h_integrable.mono' _ _;
        · have h_integrable : AEStronglyMeasurable (fun ω => M (N + 1) ω) μ ∧ AEStronglyMeasurable (fun ω => M N ω) μ := by
            exact ⟨ hM.integrable _ |> Integrable.aestronglyMeasurable, hM.integrable _ |> Integrable.aestronglyMeasurable ⟩;
          exact MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.aestronglyMeasurable_const ) h_integrable.1 ) h_integrable.2;
        · filter_upwards [ ] with ω using abs_le.mpr ⟨ by nlinarith only [ sq_nonneg ( M ( N + 1 ) ω - M N ω ), sq_nonneg ( M ( N + 1 ) ω + M N ω ) ], by nlinarith only [ sq_nonneg ( M ( N + 1 ) ω - M N ω ), sq_nonneg ( M ( N + 1 ) ω + M N ω ) ] ⟩;
    · refine' MeasureTheory.integrable_finset_sum _ fun i hi => _;
      simp_rw +decide [ sub_sq ];
      apply_rules [ MeasureTheory.Integrable.add, MeasureTheory.Integrable.neg, MeasureTheory.Integrable.const_mul ];
      have h_integrable : Integrable (fun ω => M (i + 1) ω ^ 2 + M i ω ^ 2) μ := by
        fun_prop;
      refine' h_integrable.mono' _ _;
      · have h_integrable : AEStronglyMeasurable (fun ω => M (i + 1) ω) μ ∧ AEStronglyMeasurable (fun ω => M i ω) μ := by
          exact ⟨ hM.integrable _ |> MeasureTheory.Integrable.aestronglyMeasurable, hM.integrable _ |> MeasureTheory.Integrable.aestronglyMeasurable ⟩;
        exact MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.aestronglyMeasurable_const ) h_integrable.1 ) h_integrable.2;
      · filter_upwards [ ] with ω using abs_le.mpr ⟨ by linarith [ sq_nonneg ( M ( i + 1 ) ω - M i ω ), sq_nonneg ( M ( i + 1 ) ω + M i ω ) ], by linarith [ sq_nonneg ( M ( i + 1 ) ω - M i ω ), sq_nonneg ( M ( i + 1 ) ω + M i ω ) ] ⟩;
    · simp_rw +decide [ sub_sq ];
      apply_rules [ MeasureTheory.Integrable.add, MeasureTheory.Integrable.neg, MeasureTheory.Integrable.mul_const, MeasureTheory.Integrable.const_mul ];
      have h_integrable : Integrable (fun ω => M (N + 1) ω ^ 2 + M N ω ^ 2) μ := by
        exact MeasureTheory.Integrable.add ( ‹∀ n, MeasureTheory.Integrable ( fun ω => M n ω ^ 2 ) μ› _ ) ( ‹∀ n, MeasureTheory.Integrable ( fun ω => M n ω ^ 2 ) μ› _ );
      refine' h_integrable.mono' _ _;
      · have h_integrable : AEStronglyMeasurable (fun ω => M (N + 1) ω) μ ∧ AEStronglyMeasurable (fun ω => M N ω) μ := by
          exact ⟨ hM.integrable _ |> Integrable.aestronglyMeasurable, hM.integrable _ |> Integrable.aestronglyMeasurable ⟩;
        exact MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.aestronglyMeasurable_const ) h_integrable.1 ) h_integrable.2;
      · filter_upwards [ ] with ω using abs_le.mpr ⟨ by nlinarith only [ sq_nonneg ( M ( N + 1 ) ω - M N ω ), sq_nonneg ( M ( N + 1 ) ω + M N ω ) ], by nlinarith only [ sq_nonneg ( M ( N + 1 ) ω - M N ω ), sq_nonneg ( M ( N + 1 ) ω + M N ω ) ] ⟩

/-! ### Doob's L² maximal inequality -/

/-
Doob's L² maximal inequality: E[(sup_{k≤N} |M_k|)²] ≤ 4 E[M_N²].
This follows from the layer-cake formula, Doob's weak (L¹) maximal inequality,
Fubini-Tonelli, and Cauchy-Schwarz.
-/
set_option maxHeartbeats 1600000 in
lemma doob_l2_maximal (hM : Martingale M 𝓕 μ)
    (hint : ∀ n, Integrable (fun ω => (M n ω) ^ 2) μ) (N : ℕ) :
    ∫ ω, (sSup (Set.range (fun k : Fin (N + 1) => |M k.val ω|))) ^ 2 ∂μ ≤
      4 * ∫ ω, (M N ω) ^ 2 ∂μ := by
  revert N;
  intro N
  have h_abs_martingale : Submartingale (fun n ω => |M n ω|) 𝓕 μ := by
    refine' ⟨ _, _ ⟩;
    · have := hM.1;
      exact fun n => this n |> fun h => h.norm;
    · refine' ⟨ _, _ ⟩;
      · intro i j hij
        have h_abs : ∀ᵐ ω ∂μ, |M i ω| ≤ μ[|M j| | 𝓕 i] ω := by
          have h_abs : ∀ᵐ ω ∂μ, |μ[M j | 𝓕 i] ω| ≤ μ[|M j| | 𝓕 i] ω := by
            have h_abs : ∀ᵐ ω ∂μ, |μ[M j | 𝓕 i] ω| ≤ μ[|M j| | 𝓕 i] ω := by
              have h_abs : ∀ᵐ ω ∂μ, μ[M j | 𝓕 i] ω ≤ μ[|M j| | 𝓕 i] ω := by
                apply_rules [ MeasureTheory.condExp_mono ];
                · exact hM.integrable _;
                · refine' MeasureTheory.Integrable.abs _;
                  exact hM.integrable _;
                · exact Filter.Eventually.of_forall fun ω => le_abs_self _
              have h_abs_neg : ∀ᵐ ω ∂μ, -μ[M j | 𝓕 i] ω ≤ μ[|M j| | 𝓕 i] ω := by
                have h_abs_neg : ∀ᵐ ω ∂μ, μ[-M j | 𝓕 i] ω ≤ μ[|M j| | 𝓕 i] ω := by
                  apply_rules [ MeasureTheory.condExp_mono ];
                  · exact hM.integrable j |> fun h => h.neg;
                  · refine' MeasureTheory.Integrable.abs _;
                    exact hM.integrable _;
                  · filter_upwards [ ] with ω using neg_le_abs _;
                have h_abs_neg : ∀ᵐ ω ∂μ, μ[-M j | 𝓕 i] ω = -μ[M j | 𝓕 i] ω := by
                  apply_rules [ MeasureTheory.condExp_neg ];
                filter_upwards [ ‹∀ᵐ ω ∂μ, μ[-M j | 𝓕 i] ω ≤ μ[|M j| | 𝓕 i] ω›, h_abs_neg ] with ω hω₁ hω₂ using by linarith;
              filter_upwards [ h_abs, h_abs_neg ] with ω hω₁ hω₂ using abs_le.mpr ⟨ by linarith, by linarith ⟩;
            exact h_abs;
          have := hM.2 i j hij;
          filter_upwards [ this, h_abs ] with ω hω₁ hω₂ using by simpa only [ hω₁ ] using hω₂;
        exact h_abs.mono fun ω hω => hω;
      · exact fun n => hM.integrable n |> fun h => h.norm;
  -- Let $f_n = |M_n|$ and $f^* = \sup_{k \leq N} |M_k|$.
  set f : ℕ → Ω → ℝ := fun n ω => |M n ω|
  set f_star : Ω → ℝ := fun ω => sSup (Set.range (fun k : Fin (N + 1) => |M k.val ω|));
  -- By Doob's weak L¹ inequality, we have $\mathbb{P}(f^* \geq t) \leq \frac{1}{t} \mathbb{E}[f_N \mathbf{1}_{\{f^* \geq t\}}]$.
  have h_doob_weak : ∀ t > 0, μ {ω | f_star ω ≥ t} ≤ ENNReal.ofReal ((1 / t) * ∫ ω in {ω | f_star ω ≥ t}, f N ω ∂μ) := by
    intro t ht_pos
    have h_doob_weak : μ {ω | f_star ω ≥ t} ≤ ENNReal.ofReal ((1 / t) * ∫ ω in {ω | f_star ω ≥ t}, f N ω ∂μ) := by
      have h_doob_weak_aux : ∀ t > 0, μ {ω | (Finset.range (N + 1)).sup' (by simp) (fun k => f k ω) ≥ t} ≤ ENNReal.ofReal ((1 / t) * ∫ ω in {ω | (Finset.range (N + 1)).sup' (by simp) (fun k => f k ω) ≥ t}, f N ω ∂μ) := by
        intro t ht_pos
        have := @MeasureTheory.maximal_ineq Ω mΩ μ;
        specialize this h_abs_martingale (fun n ω => abs_nonneg (M n ω)) N;
        exact ⟨ t, ht_pos.le ⟩;
        simp_all +decide [ ENNReal.ofReal_mul ( inv_nonneg.mpr ht_pos.le ) ];
        rw [ ← ENNReal.div_eq_inv_mul ];
        rw [ ENNReal.le_div_iff_mul_le ] <;> norm_num [ ENNReal.ofReal_pos, ‹0 < t› ];
        convert this using 1 ; ring!;
        exact congr_arg _ ( ENNReal.ofReal_eq_coe_nnreal <| by positivity )
      convert h_doob_weak_aux t ht_pos using 4;
      · constructor <;> intro h <;> contrapose! h;
        · refine' lt_of_le_of_lt _ h;
          refine' csSup_le _ _ <;> norm_num;
          · exact ⟨ _, ⟨ ⟨ 0, Nat.zero_lt_succ _ ⟩, rfl ⟩ ⟩;
          · exact fun a => ⟨ a, Fin.is_le a, le_rfl ⟩;
        · refine' lt_of_le_of_lt _ h;
          simp +zetaDelta at *;
          exact fun n hn => le_csSup ( Set.finite_range _ |> Set.Finite.bddAbove ) ⟨ ⟨ n, by linarith ⟩, rfl ⟩;
      · congr! 2;
        ext ω; simp [f_star];
        constructor;
        · intro ht;
          contrapose! ht;
          have h_sup_lt_t : ∃ k : Fin (N + 1), ∀ j : Fin (N + 1), |M j.val ω| ≤ |M k.val ω| := by
            simpa using Finset.exists_max_image Finset.univ ( fun j : Fin ( N + 1 ) => |M j ω| ) ⟨ 0, Finset.mem_univ 0 ⟩;
          obtain ⟨ k, hk ⟩ := h_sup_lt_t;
          exact lt_of_le_of_lt ( csSup_le ( Set.nonempty_of_mem ( Set.mem_range_self k ) ) ( Set.forall_mem_range.mpr fun j => hk j ) ) ( ht k ( Fin.is_le k ) );
        · rintro ⟨ k, hk₁, hk₂ ⟩;
          exact le_trans hk₂ ( le_csSup ( Set.finite_range _ |> Set.Finite.bddAbove ) ⟨ ⟨ k, by linarith ⟩, rfl ⟩ );
    exact h_doob_weak;
  -- Using the layer cake formula, we have $\mathbb{E}[(f^*)^2] = 2 \int_0^\infty t \mathbb{P}(f^* \geq t) \, dt$.
  have h_layer_cake : ∫⁻ ω, ENNReal.ofReal (f_star ω ^ 2) ∂μ = 2 * ∫⁻ t in Set.Ioi 0, ENNReal.ofReal t * μ {ω | f_star ω ≥ t} := by
    have h_layer_cake : ∀ {g : Ω → ℝ}, (0 ≤ᵐ[μ] g) → (Measurable g) → ∫⁻ ω, ENNReal.ofReal (g ω ^ 2) ∂μ = 2 * ∫⁻ t in Set.Ioi 0, ENNReal.ofReal t * μ {ω | g ω ≥ t} := by
      intro g hg hg';
      have := @MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul;
      convert @this Ω mΩ μ g hg ( hg'.aemeasurable ) 2 ( by norm_num ) using 1 ; norm_num [ mul_comm ];
      norm_num [ mul_comm ];
    apply h_layer_cake;
    · exact Filter.Eventually.of_forall fun ω => by apply_rules [ Real.sSup_nonneg ] ; rintro x ⟨ k, rfl ⟩ ; exact abs_nonneg _;
    · convert measurable_sSup_abs hM N using 1;
  -- Using the weak inequality, we have $\mathbb{E}[(f^*)^2] \leq 2 \int_0^\infty \mathbb{E}[f_N \mathbf{1}_{\{f^* \geq t\}}] \, dt$.
  have h_integral_bound : ∫⁻ ω, ENNReal.ofReal (f_star ω ^ 2) ∂μ ≤ 2 * ∫⁻ t in Set.Ioi 0, ∫⁻ ω in {ω | f_star ω ≥ t}, ENNReal.ofReal (f N ω) ∂μ := by
    rw [h_layer_cake];
    refine' mul_le_mul_left' ( MeasureTheory.setLIntegral_mono' measurableSet_Ioi fun t ht => _ ) _;
    refine' le_trans ( mul_le_mul_left' ( h_doob_weak t ht ) _ ) _;
    rw [ ← ENNReal.ofReal_mul ht.out.le ];
    rw [ ← mul_assoc, mul_one_div_cancel ht.out.ne', one_mul, MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun ω => M N ω ^ 2 + 1;
      · exact MeasureTheory.Integrable.add ( MeasureTheory.Integrable.mono_measure ( ‹∀ n, Integrable ( fun ω => M n ω ^ 2 ) μ› N ) ( Measure.restrict_le_self ) ) ( MeasureTheory.integrable_const _ );
      · have := hM.integrable N;
        exact this.abs.aestronglyMeasurable.restrict;
      · filter_upwards [ ] with ω using by rw [ Real.norm_eq_abs, abs_abs ] ; nlinarith only [ sq_nonneg ( |M N ω| - 1 ), abs_mul_abs_self ( M N ω ) ] ;
    · exact Filter.Eventually.of_forall fun ω => abs_nonneg _;
  -- Using Fubini's theorem, we can interchange the order of integration.
  have h_fubini : ∫⁻ t in Set.Ioi 0, ∫⁻ ω in {ω | f_star ω ≥ t}, ENNReal.ofReal (f N ω) ∂μ = ∫⁻ ω, ∫⁻ t in Set.Ioc 0 (f_star ω), ENNReal.ofReal (f N ω) ∂MeasureTheory.MeasureSpace.volume ∂μ := by
    have h_fubini : ∫⁻ t in Set.Ioi 0, ∫⁻ ω in {ω | f_star ω ≥ t}, ENNReal.ofReal (f N ω) ∂μ = ∫⁻ ω, ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (f N ω) * (if t ≤ f_star ω then 1 else 0) ∂MeasureTheory.MeasureSpace.volume ∂μ := by
      rw [ ← MeasureTheory.lintegral_lintegral_swap ];
      · refine' MeasureTheory.lintegral_congr_ae _;
        filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with t ht;
        rw [ ← MeasureTheory.lintegral_indicator ] <;> norm_num [ Set.indicator ];
        have h_measurable : Measurable (fun ω => sSup (Set.range (fun k : Fin (N + 1) => |M k.val ω|))) := by
          exact?;
        exact measurableSet_le measurable_const h_measurable |> MeasurableSet.mem;
      · refine' AEMeasurable.mul _ _;
        · refine' AEMeasurable.ennreal_ofReal _;
          have h_aemeasurable : AEMeasurable (fun ω => f N ω) μ := by
            have := h_abs_martingale.integrable N;
            exact this.1.aemeasurable;
          exact?;
        · refine' AEMeasurable.indicator _ _;
          · exact aemeasurable_const;
          · have h_measurable : Measurable (fun ω => sSup (Set.range (fun k : Fin (N + 1) => |M k.val ω|))) := by
              exact?;
            exact measurableSet_le measurable_fst ( h_measurable.comp measurable_snd );
    rw [ h_fubini ];
    congr! 2;
    rw [ ← MeasureTheory.lintegral_indicator, ← MeasureTheory.lintegral_indicator ] <;> norm_num [ Set.indicator ];
    simpa only [ ← ite_and ];
  -- Using the fact that $\int_0^{f^*} f_N \, dt \leq \int_0^{f^*} f^* \, dt = \frac{1}{2} (f^*)^2$, we get $\mathbb{E}[(f^*)^2] \leq 2 \int_0^\infty \mathbb{E}[f_N \mathbf{1}_{\{f^* \geq t\}}] \, dt \leq 2 \mathbb{E}[f_N f^*]$.
  have h_integral_bound_final : ∫⁻ ω, ENNReal.ofReal (f_star ω ^ 2) ∂μ ≤ 2 * ∫⁻ ω, ENNReal.ofReal (f N ω * f_star ω) ∂μ := by
    refine' le_trans h_integral_bound ( mul_le_mul_left' ( h_fubini.le.trans _ ) _ );
    refine' MeasureTheory.lintegral_mono fun ω => _;
    simp +decide [ mul_comm, ENNReal.ofReal_mul ( abs_nonneg _ ) ];
    rw [ ENNReal.ofReal_mul ( abs_nonneg _ ) ];
  -- Using the Cauchy-Schwarz inequality, we have $\mathbb{E}[f_N f^*] \leq \sqrt{\mathbb{E}[f_N^2]} \sqrt{\mathbb{E}[(f^*)^2]}$.
  have h_cauchy_schwarz : ∫⁻ ω, ENNReal.ofReal (f N ω * f_star ω) ∂μ ≤ ENNReal.ofReal (Real.sqrt (∫ ω, f N ω ^ 2 ∂μ) * Real.sqrt (∫ ω, f_star ω ^ 2 ∂μ)) := by
    have h_cauchy_schwarz : (∫ ω, f N ω * f_star ω ∂μ) ^ 2 ≤ (∫ ω, f N ω ^ 2 ∂μ) * (∫ ω, f_star ω ^ 2 ∂μ) := by
      have h_cauchy_schwarz : ∀ (f g : Ω → ℝ), MeasureTheory.Integrable (fun ω => f ω ^ 2) μ → MeasureTheory.Integrable (fun ω => g ω ^ 2) μ → MeasureTheory.Integrable (fun ω => f ω * g ω) μ → (∫ ω, f ω * g ω ∂μ) ^ 2 ≤ (∫ ω, f ω ^ 2 ∂μ) * (∫ ω, g ω ^ 2 ∂μ) := by
        intros f g hf hg hfg
        have h_cauchy_schwarz : (∫ ω, (f ω - (∫ ω, f ω * g ω ∂μ) / (∫ ω, g ω ^ 2 ∂μ) * g ω) ^ 2 ∂μ) ≥ 0 := by
          exact MeasureTheory.integral_nonneg fun ω => sq_nonneg _;
        by_cases h : ∫ ω, g ω ^ 2 ∂μ = 0 <;> simp_all +decide [ sub_sq, mul_pow ];
        · rw [ MeasureTheory.integral_eq_zero_iff_of_nonneg ( fun _ => sq_nonneg _ ) ] at h;
          · exact MeasureTheory.integral_eq_zero_of_ae ( h.mono fun x hx => by aesop );
          · exact hg;
        · rw [ MeasureTheory.integral_add, MeasureTheory.integral_sub ] at h_cauchy_schwarz;
          · simp_all +decide [ div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm, MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const ];
            simp_all +decide [ ← mul_assoc, MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul ];
            nlinarith [ inv_mul_cancel_left₀ h ( ∫ ω, f ω * g ω ∂μ ), inv_mul_cancel₀ h, show 0 ≤ ∫ ω, f ω ^ 2 ∂μ from MeasureTheory.integral_nonneg fun _ => sq_nonneg _, show 0 ≤ ∫ ω, g ω ^ 2 ∂μ from MeasureTheory.integral_nonneg fun _ => sq_nonneg _ ];
          · exact hf;
          · convert hfg.mul_const ( 2 * ( ( ∫ ω, f ω * g ω ∂μ ) / ∫ ω, g ω ^ 2 ∂μ ) ) using 2 ; ring;
          · refine' MeasureTheory.Integrable.sub hf _;
            convert hfg.mul_const ( 2 * ( ( ∫ ω, f ω * g ω ∂μ ) / ∫ ω, g ω ^ 2 ∂μ ) ) using 2 ; ring;
          · exact hg.const_mul _;
      apply h_cauchy_schwarz;
      · aesop;
      · exact?;
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun ω => ( M N ω ) ^ 2 + ( f_star ω ) ^ 2;
        · refine' MeasureTheory.Integrable.add ( ‹∀ n, MeasureTheory.Integrable ( fun ω => M n ω ^ 2 ) μ› N ) _;
          convert integrable_sSup_sq hM ‹_› N using 1;
        · refine' AEStronglyMeasurable.mul _ _;
          · have := hM.integrable N;
            exact this.1.norm;
          · have h_measurable : Measurable (fun ω => sSup (Set.range (fun k : Fin (N + 1) => |M k.val ω|))) := by
              convert measurable_sSup_abs hM N using 1;
            exact h_measurable.aestronglyMeasurable;
        · filter_upwards [ ] with ω using abs_le.mpr ⟨ by nlinarith only [ abs_mul_abs_self ( M N ω ), abs_nonneg ( M N ω ), abs_nonneg ( f_star ω ) ], by nlinarith only [ abs_mul_abs_self ( M N ω ), abs_nonneg ( M N ω ), abs_nonneg ( f_star ω ) ] ⟩;
    rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
    · rw [ ← Real.sqrt_mul ( MeasureTheory.integral_nonneg fun _ => sq_nonneg _ ) ];
      refine' Real.le_sqrt_of_sq_le _;
      convert h_cauchy_schwarz using 1;
      rw [ MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
      · exact Filter.Eventually.of_forall fun ω => mul_nonneg ( abs_nonneg _ ) ( by apply_rules [ Real.sSup_nonneg ] ; rintro x ⟨ k, rfl ⟩ ; exact abs_nonneg _ );
      · refine' AEStronglyMeasurable.mul _ _;
        · exact h_abs_martingale.integrable N |> fun h => h.1;
        · have h_measurable : Measurable (fun ω => sSup (Set.range (fun k : Fin (N + 1) => |M k.val ω|))) := by
            exact?;
          exact h_measurable.aestronglyMeasurable;
    · refine' ne_of_lt ( MeasureTheory.Integrable.lintegral_lt_top _ );
      refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun ω => ( M N ω ) ^ 2 + ( f_star ω ) ^ 2;
      · refine' MeasureTheory.Integrable.add ( ‹∀ n, Integrable ( fun ω => M n ω ^ 2 ) μ› N ) _;
        convert integrable_sSup_sq hM ‹_› N using 1;
      · refine' AEStronglyMeasurable.mul _ _;
        · have := hM.integrable N;
          exact this.abs.aestronglyMeasurable;
        · have h_measurable : Measurable (fun ω => sSup (Set.range (fun k : Fin (N + 1) => |M k.val ω|))) := by
            exact?;
          exact h_measurable.aestronglyMeasurable;
      · filter_upwards [ ] with ω using abs_le.mpr ⟨ by nlinarith only [ abs_mul_abs_self ( M N ω ), abs_nonneg ( M N ω ), show 0 ≤ f_star ω from by apply_rules [ Real.sSup_nonneg ] ; rintro x ⟨ k, rfl ⟩ ; exact abs_nonneg _ ], by nlinarith only [ abs_mul_abs_self ( M N ω ), abs_nonneg ( M N ω ), show 0 ≤ f_star ω from by apply_rules [ Real.sSup_nonneg ] ; rintro x ⟨ k, rfl ⟩ ; exact abs_nonneg _ ] ⟩;
    · exact ENNReal.mul_ne_top ( ENNReal.ofReal_ne_top ) ( ENNReal.ofReal_ne_top );
  -- Combining the inequalities, we get $\mathbb{E}[(f^*)^2] \leq 2 \sqrt{\mathbb{E}[f_N^2]} \sqrt{\mathbb{E}[(f^*)^2]}$.
  have h_combined : ∫⁻ ω, ENNReal.ofReal (f_star ω ^ 2) ∂μ ≤ 2 * ENNReal.ofReal (Real.sqrt (∫ ω, f N ω ^ 2 ∂μ) * Real.sqrt (∫ ω, f_star ω ^ 2 ∂μ)) := by
    exact h_integral_bound_final.trans ( mul_le_mul_left' h_cauchy_schwarz _ );
  -- Dividing both sides by $\sqrt{\mathbb{E}[(f^*)^2]}$, we get $\sqrt{\mathbb{E}[(f^*)^2]} \leq 2 \sqrt{\mathbb{E}[f_N^2]}$.
  have h_divided : Real.sqrt (∫ ω, f_star ω ^ 2 ∂μ) ≤ 2 * Real.sqrt (∫ ω, f N ω ^ 2 ∂μ) := by
    contrapose! h_combined;
    rw [ ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
    · rw [ ENNReal.lt_ofReal_iff_toReal_lt ] <;> norm_num;
      · nlinarith [ Real.sqrt_nonneg ( ∫ ω, f N ω ^ 2 ∂μ ), Real.sqrt_nonneg ( ∫ ω, f_star ω ^ 2 ∂μ ), Real.mul_self_sqrt ( show 0 ≤ ∫ ω, f N ω ^ 2 ∂μ by exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _ ), Real.mul_self_sqrt ( show 0 ≤ ∫ ω, f_star ω ^ 2 ∂μ by exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _ ) ];
      · exact ENNReal.mul_ne_top ENNReal.coe_ne_top ( ENNReal.mul_ne_top ( ENNReal.ofReal_ne_top ) ( ENNReal.ofReal_ne_top ) );
    · exact ( by by_contra h; rw [ MeasureTheory.integral_undef h ] at h_combined; norm_num at h_combined; linarith [ Real.sqrt_nonneg ( ∫ ω, f N ω ^ 2 ∂μ ) ] );
    · exact Filter.Eventually.of_forall fun ω => sq_nonneg _;
  rw [ Real.sqrt_le_iff ] at h_divided;
  convert h_divided.2 using 1 ; ring ; norm_num [ Real.sq_sqrt ( MeasureTheory.integral_nonneg fun _ => sq_nonneg _ ) ] ;
  simp +zetaDelta at *

/-! ### Main BDG theorem -/

/-- **Burkholder-Davis-Gundy inequality at p = 2** for discrete-time martingales.

For a square-integrable martingale M with M_0 = 0 a.s., the L² norm of the
running maximum is comparable to the L² norm of the square root of the
quadratic variation, with constants 1 and 4. -/
theorem bdg_discrete_l2
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝓕 : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (hM : Martingale M 𝓕 μ)
    (hM_int : ∀ n, Integrable (fun ω => (M n ω) ^ 2) μ)
    (hM0 : ∀ᵐ ω ∂μ, M 0 ω = 0)
    (N : ℕ) :
    let qv : Ω → ℝ := fun ω =>
      ∑ k ∈ Finset.range N, (M (k + 1) ω - M k ω) ^ 2
    (∫ ω, (sSup (Set.range (fun k : Fin (N + 1) => |M k.val ω|))) ^ 2 ∂μ) ≤
      4 * ∫ ω, qv ω ∂μ ∧
    ∫ ω, qv ω ∂μ ≤
      ∫ ω, (sSup (Set.range (fun k : Fin (N + 1) => |M k.val ω|))) ^ 2 ∂μ := by
  intro qv
  have h_id := integral_sq_eq_integral_qv hM hM_int hM0 N
  have h_doob := doob_l2_maximal hM hM_int N
  refine ⟨?_, ?_⟩
  · -- Upper bound: E[(sup|M|)²] ≤ 4 * E[qv]
    -- By Doob: E[(sup|M|)²] ≤ 4 * E[M_N²] and E[M_N²] = E[qv]
    linarith
  · -- Lower bound: E[qv] ≤ E[(sup|M|)²]
    -- E[qv] = E[M_N²] and M_N² ≤ (sup|M|)² pointwise
    rw [← h_id]
    apply integral_mono (hM_int N) (integrable_sSup_sq hM hM_int N)
    intro ω
    have h1 : |M N ω| ≤ sSup (Set.range (fun k : Fin (N + 1) => |M k.val ω|)) :=
      abs_le_sSup_range M N ω ⟨N, Nat.lt_succ_iff.mpr le_rfl⟩
    calc (M N ω) ^ 2 = |M N ω| ^ 2 := (sq_abs _).symm
      _ ≤ (sSup (Set.range (fun k : Fin (N + 1) => |M k.val ω|))) ^ 2 :=
          sq_le_sq' (by linarith [sSup_range_nonneg M N ω, abs_nonneg (M N ω)]) h1

end Pythia