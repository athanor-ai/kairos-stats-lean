/-
Copyright (c) 2024 Pythia Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pythia Contributors
-/
import Mathlib

/-! # Dvoretzky Stochastic Approximation Convergence Theorem

This module formalizes the **Dvoretzky (1956)** stochastic approximation convergence
theorem, building on the **Robbins–Siegmund** almost-supermartingale convergence lemma.

## Main results

### Deterministic core

* `tailSum` – tail sum `∑_{i≥n} bᵢ` of a sequence.
* `contraction_telescope` – telescoping bound under a contraction recurrence.
* `contraction_y_antitone` – the modified sequence `yₙ = xₙ + tailSum(b, n)` is antitone.
* `contraction_tendsto` – a contraction sequence with summable perturbations converges.
* `contraction_frequently_lt` – with divergent step sizes, the sequence frequently
  drops below any ε > 0.
* `det_contraction_convergence` – **Main deterministic result**: xₙ → 0.

### Robbins–Siegmund

* `robbins_siegmund_det` – Deterministic Robbins–Siegmund: non-negative sequences
  satisfying an almost-supermartingale inequality converge, and the
  "contraction" increments are summable.

### Almost-sure (stochastic) versions

* `dvoretzky_ae` – Almost-sure version of the contraction convergence.
* `robbins_siegmund_ae` – Almost-sure Robbins–Siegmund.

### Robbins–Monro

* `RobbinsMonroStepSize` – standard step-size conditions: `∑ aₙ = ∞`, `∑ aₙ² < ∞`.
* `robbins_monro_convergence` – deterministic Robbins–Monro convergence.
* `sgd_convergence` – SGD convergence backbone for ML/RL applications.

## References

* A. Dvoretzky, *On stochastic approximation*, Proc. 3rd Berkeley Symp.
  Math. Statist. Probab. **1** (1956), 39–55.
* H. Robbins and D. Siegmund, *A convergence theorem for non-negative almost
  supermartingales and some applications*, in Optimizing Methods in Statistics,
  Academic Press, 1971, 233–257.
* H. Robbins and S. Monro, *A stochastic approximation method*,
  Ann. Math. Statist. **22** (1951), 400–407.
-/

open Filter Topology BigOperators MeasureTheory
open scoped NNReal ENNReal

namespace Pythia.StochasticApproximation.Dvoretzky

-- ================================================================
-- § 1  Tail-sum infrastructure
-- ================================================================

/-- Tail sum of a real-valued sequence starting at index `n`:
    `tailSum b n = ∑_{i≥n} b i = ∑' i, b (n + i)`. -/
noncomputable def tailSum (b : ℕ → ℝ) (n : ℕ) : ℝ := ∑' i, b (n + i)

/-- Tail sums of a non-negative sequence are non-negative. -/
theorem tailSum_nonneg {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) (n : ℕ) :
    0 ≤ tailSum b n :=
  tsum_nonneg fun i => hb _

/-
Tail sum telescoping: `tailSum b n = b n + tailSum b (n + 1)`.
-/
theorem tailSum_succ {b : ℕ → ℝ} (hb : Summable b) (n : ℕ) :
    tailSum b n = b n + tailSum b (n + 1) := by
  unfold tailSum;
  rw [ Summable.tsum_eq_zero_add ];
  · ac_rfl;
  · exact hb.comp_injective ( add_right_injective n )

/-
Tail sums of a summable non-negative sequence tend to zero.
-/
theorem tendsto_tailSum {b : ℕ → ℝ} (hb_nn : ∀ n, 0 ≤ b n) (hb : Summable b) :
    Tendsto (tailSum b) atTop (𝓝 0) := by
  convert tendsto_sum_nat_add fun n => b n using 1;
  exact funext fun n => tsum_congr fun k => by rw [ add_comm ] ;

/-
================================================================
§ 2  Deterministic contraction convergence (Dvoretzky core)
================================================================

**Telescoping bound**: under the contraction recurrence `x(n+1) ≤ (1-aₙ)xₙ + bₙ`
and a uniform lower bound `x n ≥ ε` for `n ≥ N`, we obtain
`x(N+k) ≤ x(N) − ε · ∑ a(N+i) + ∑ b(N+i)`.
-/
theorem contraction_telescope (x a b : ℕ → ℝ)
    (hx_nn : ∀ n, 0 ≤ x n)
    (ha_nn : ∀ n, 0 ≤ a n)
    (hrec : ∀ n, x (n + 1) ≤ (1 - a n) * x n + b n)
    (N : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hxε : ∀ n, N ≤ n → ε ≤ x n)
    (k : ℕ) :
    x (N + k) ≤ x N - ε * ∑ i ∈ Finset.range k, a (N + i) +
      ∑ i ∈ Finset.range k, b (N + i) := by
  induction' k with k ih;
  · norm_num;
  · rw [ Finset.sum_range_succ, Finset.sum_range_succ ];
    nlinarith! [ hrec ( N + k ), hxε ( N + k ) ( by linarith ), ha_nn ( N + k ) ]

/-
The modified sequence `yₙ = xₙ + tailSum b n` is step-wise non-increasing.
-/
theorem contraction_y_step (x a b : ℕ → ℝ)
    (hx_nn : ∀ n, 0 ≤ x n)
    (ha_nn : ∀ n, 0 ≤ a n) (ha_le : ∀ n, a n ≤ 1)
    (hrec : ∀ n, x (n + 1) ≤ (1 - a n) * x n + b n)
    (hb_sum : Summable b) (n : ℕ) :
    x (n + 1) + tailSum b (n + 1) ≤ x n + tailSum b n := by
  -- By the properties of the tail sum, we have `tailSum b n = b n + tailSum b (n + 1)`.
  have h_tailSum_succ : tailSum b n = b n + tailSum b (n + 1) := by
    exact tailSum_succ hb_sum n
  nlinarith [hx_nn n, ha_nn n, ha_le n, hrec n]

/-
The modified sequence `yₙ = xₙ + tailSum b n` is antitone.
-/
theorem contraction_y_antitone (x a b : ℕ → ℝ)
    (hx_nn : ∀ n, 0 ≤ x n)
    (ha_nn : ∀ n, 0 ≤ a n) (ha_le : ∀ n, a n ≤ 1)
    (hrec : ∀ n, x (n + 1) ≤ (1 - a n) * x n + b n)
    (hb_sum : Summable b) :
    Antitone (fun n => x n + tailSum b n) := by
  exact antitone_nat_of_succ_le fun n => contraction_y_step x a b hx_nn ha_nn ha_le hrec hb_sum n

/-
The contraction sequence converges to some limit `L ≥ 0`.
-/
theorem contraction_tendsto (x a b : ℕ → ℝ)
    (hx_nn : ∀ n, 0 ≤ x n)
    (ha_nn : ∀ n, 0 ≤ a n) (ha_le : ∀ n, a n ≤ 1)
    (hb_nn : ∀ n, 0 ≤ b n)
    (hrec : ∀ n, x (n + 1) ≤ (1 - a n) * x n + b n)
    (hb_sum : Summable b) :
    ∃ L ≥ 0, Tendsto x atTop (𝓝 L) := by
  -- Define y n = x n + tailSum b n. By contraction_y_antitone, y is antitone.
  set y : ℕ → ℝ := fun n => x n + tailSum b n;
  -- Since $y$ is antitone and bounded below, it converges.
  obtain ⟨L_y, hL_y⟩ : ∃ L_y, Filter.Tendsto y Filter.atTop (nhds L_y) := by
    exact ⟨ _, tendsto_atTop_ciInf ( contraction_y_antitone x a b hx_nn ha_nn ha_le hrec hb_sum ) ⟨ 0, Set.forall_mem_range.mpr fun n => add_nonneg ( hx_nn n ) ( tailSum_nonneg hb_nn n ) ⟩ ⟩;
  -- Since $tailSum b \to 0$, we have $x n = y n - tailSum b n \to L_y - 0 = L_y$.
  have hL : Filter.Tendsto x Filter.atTop (nhds (L_y - 0)) := by
    convert hL_y.sub ( tendsto_tailSum hb_nn hb_sum ) using 2 ; ring;
  exact ⟨ L_y - 0, le_of_tendsto_of_tendsto' tendsto_const_nhds hL fun n => by aesop, hL ⟩

/-
Under divergent step sizes, the contraction sequence frequently drops below
any positive threshold.
-/
theorem contraction_frequently_lt (x a b : ℕ → ℝ)
    (hx_nn : ∀ n, 0 ≤ x n)
    (ha_nn : ∀ n, 0 ≤ a n) (ha_le : ∀ n, a n ≤ 1)
    (hb_nn : ∀ n, 0 ≤ b n)
    (hrec : ∀ n, x (n + 1) ≤ (1 - a n) * x n + b n)
    (ha_div : ¬Summable a) (hb_sum : Summable b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ n in atTop, x n < ε := by
  by_contra h_contra;
  -- Then there exists $N$ such that for all $n \geq N$, $x_n \geq \varepsilon$.
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, x n ≥ ε := by
    aesop;
  -- Apply contraction_telescope to get $x(N+k) \leq x N - \varepsilon \sum_{i<N} a(i) + \sum_{i<N} b(i)$.
  have h_telescope : ∀ k, x (N + k) ≤ x N - ε * ∑ i ∈ Finset.range k, a (N + i) + ∑ i ∈ Finset.range k, b (N + i) :=
    fun k => contraction_telescope x a b hx_nn ha_nn hrec N ε hε hN k
  -- The sum $\sum_{i<N} a(i)$ diverges since $\sum a$ diverges.
  have h_sum_a_diverges : Filter.Tendsto (fun k => ∑ i ∈ Finset.range k, a (N + i)) Filter.atTop Filter.atTop := by
    exact not_summable_iff_tendsto_nat_atTop_of_nonneg ( fun _ => ha_nn _ ) |>.1 ( by exact fun h => ha_div <| summable_nat_add_iff N |>.1 <| by simpa only [ add_comm ] using h );
  -- The sum $\sum_{i<N} b(i)$ is bounded since $\sum b$ converges.
  have h_sum_b_bounded : ∃ C, ∀ k, ∑ i ∈ Finset.range k, b (N + i) ≤ C := by
    exact ⟨ _, fun k => Summable.sum_le_tsum ( Finset.range k ) ( fun _ _ => hb_nn _ ) ( hb_sum.comp_injective ( add_right_injective N ) ) ⟩;
  -- Choose $k$ large enough such that $\varepsilon \sum_{i<N} a(i) > x N + C$.
  obtain ⟨k, hk⟩ : ∃ k, ε * ∑ i ∈ Finset.range k, a (N + i) > x N + h_sum_b_bounded.choose := by
    exact ( h_sum_a_diverges.const_mul_atTop hε ) |> fun h => h.eventually_gt_atTop ( x N + h_sum_b_bounded.choose ) |> fun h => h.exists;
  linarith [ h_telescope k, h_sum_b_bounded.choose_spec k, hx_nn ( N + k ) ]

/-
**Deterministic Dvoretzky contraction convergence**: if a non-negative sequence
satisfies `xₙ₊₁ ≤ (1 − aₙ) xₙ + bₙ` with `0 ≤ aₙ ≤ 1`, `bₙ ≥ 0`,
`∑ aₙ = ∞` (step sizes diverge), and `∑ bₙ < ∞` (perturbations summable),
then `xₙ → 0`.
-/
theorem det_contraction_convergence (x a b : ℕ → ℝ)
    (hx_nn : ∀ n, 0 ≤ x n)
    (ha_nn : ∀ n, 0 ≤ a n) (ha_le : ∀ n, a n ≤ 1)
    (hb_nn : ∀ n, 0 ≤ b n)
    (hrec : ∀ n, x (n + 1) ≤ (1 - a n) * x n + b n)
    (ha_div : ¬Summable a) (hb_sum : Summable b) :
    Tendsto x atTop (𝓝 0) := by
  obtain ⟨ L, hL_nonneg, hL_tendsto ⟩ := contraction_tendsto x a b hx_nn ha_nn ha_le hb_nn hrec hb_sum;
  by_cases hL_pos : L > 0;
  · exact absurd ( contraction_frequently_lt x a b hx_nn ha_nn ha_le hb_nn hrec ha_div hb_sum ( half_pos hL_pos ) ) ( by exact fun h => h <| by filter_upwards [ hL_tendsto.eventually ( lt_mem_nhds <| half_lt_self hL_pos ) ] with n hn using by linarith );
  · rwa [ le_antisymm ( le_of_not_gt hL_pos ) hL_nonneg ] at hL_tendsto

/-
================================================================
§ 3  Robbins–Siegmund deterministic convergence
================================================================

**Robbins–Siegmund (deterministic)**: if a non-negative sequence satisfies
`xₙ₊₁ ≤ (1 + αₙ) xₙ − βₙ + γₙ` with `αₙ, βₙ, γₙ ≥ 0`, `∑ αₙ < ∞`,
`∑ γₙ < ∞`, then `xₙ` converges and `∑ βₙ < ∞`.

This is the key "almost supermartingale" convergence lemma from Robbins–Siegmund
(1971) that underlies most modern stochastic approximation proofs.
-/
theorem robbins_siegmund_det (x α β γ : ℕ → ℝ)
    (hx_nn : ∀ n, 0 ≤ x n)
    (hα_nn : ∀ n, 0 ≤ α n) (hβ_nn : ∀ n, 0 ≤ β n) (hγ_nn : ∀ n, 0 ≤ γ n)
    (hrec : ∀ n, x (n + 1) ≤ (1 + α n) * x n - β n + γ n)
    (hα_sum : Summable α) (hγ_sum : Summable γ) :
    (∃ L, Tendsto x atTop (𝓝 L)) ∧ Summable β := by
  -- By induction, we can show that $x_n \leq M$ for some $M$.
  obtain ⟨M, hM⟩ : ∃ M, ∀ n, x n ≤ M := by
    have hx_bound : ∀ n, x (n + 1) ≤ x n + α n * x n + γ n := by
      exact fun n => by linarith [ hrec n, hβ_nn n ] ;
    -- By induction, we can show that $x_n \leq x_0 \exp(\sum_{i=0}^{n-1} \alpha_i) + \sum_{i=0}^{n-1} \gamma_i \exp(\sum_{j=i+1}^{n-1} \alpha_j)$.
    have hx_induction : ∀ n, x n ≤ x 0 * Real.exp (∑ i ∈ Finset.range n, α i) + ∑ i ∈ Finset.range n, γ i * Real.exp (∑ j ∈ Finset.Ico (i + 1) n, α j) := by
      intro n;
      induction' n with n ih;
      · norm_num;
      · simp_all +decide [Finset.sum_range_succ];
        rw [ Real.exp_add ];
        refine le_trans ( hx_bound n ) ?_;
        rw [ show ( ∑ i ∈ Finset.range n, γ i * Real.exp ( ∑ j ∈ Finset.Ico ( i + 1 ) ( n + 1 ), α j ) ) = ( ∑ i ∈ Finset.range n, γ i * Real.exp ( ∑ j ∈ Finset.Ico ( i + 1 ) n, α j ) ) * Real.exp ( α n ) from ?_ ];
        · nlinarith [ hx_nn n, hα_nn n, hβ_nn n, hγ_nn n, Real.add_one_le_exp ( α n ), Real.add_one_le_exp ( ∑ i ∈ Finset.range n, α i ), mul_le_mul_of_nonneg_left ( Real.add_one_le_exp ( α n ) ) ( hx_nn n ), mul_le_mul_of_nonneg_left ( Real.add_one_le_exp ( ∑ i ∈ Finset.range n, α i ) ) ( hx_nn n ) ];
        · rw [ Finset.sum_mul _ _ _ ] ; refine' Finset.sum_congr rfl fun i hi => _ ; rw [ Finset.sum_Ico_succ_top ( by linarith [ Finset.mem_range.mp hi ] ) ] ; rw [ Real.exp_add ] ; ring;
    -- Since $\sum \alpha_i$ and $\sum \gamma_i$ are summable, their exponential sums are also bounded.
    have h_exp_bound : ∃ C, ∀ n, Real.exp (∑ i ∈ Finset.range n, α i) ≤ C := by
      exact ⟨ Real.exp ( ∑' i, α i ), fun n => Real.exp_le_exp.mpr ( Summable.sum_le_tsum ( Finset.range n ) ( fun _ _ => hα_nn _ ) hα_sum ) ⟩;
    have h_gamma_exp_bound : ∃ C, ∀ n, ∑ i ∈ Finset.range n, γ i * Real.exp (∑ j ∈ Finset.Ico (i + 1) n, α j) ≤ C := by
      have h_gamma_exp_bound_step : ∀ n, ∑ i ∈ Finset.range n, γ i * Real.exp (∑ j ∈ Finset.Ico (i + 1) n, α j) ≤ ∑ i ∈ Finset.range n, γ i * Real.exp (∑ j ∈ Finset.range n, α j) := by
        exact fun n => Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_iff.mpr fun j hj => Finset.mem_range.mpr <| by linarith [ Finset.mem_Ico.mp hj ] ) fun _ _ _ => hα_nn _ ) <| hγ_nn _
      simp_all +decide [ ← Finset.sum_mul _ _ _ ];
      exact ⟨ ( ∑' i, γ i ) * h_exp_bound.choose, fun n => le_trans ( h_gamma_exp_bound_step n ) ( mul_le_mul ( Summable.sum_le_tsum ( Finset.range n ) ( fun _ _ => hγ_nn _ ) hγ_sum ) ( h_exp_bound.choose_spec n ) ( by positivity ) ( by exact tsum_nonneg fun _ => hγ_nn _ ) ) ⟩;
    exact ⟨ x 0 * h_exp_bound.choose + h_gamma_exp_bound.choose, fun n => le_trans ( hx_induction n ) ( add_le_add ( mul_le_mul_of_nonneg_left ( h_exp_bound.choose_spec n ) ( hx_nn 0 ) ) ( h_gamma_exp_bound.choose_spec n ) ) ⟩;
  -- Define $y_n = x_n + M \sum_{i=n}^{\infty} \alpha_i + \sum_{i=n}^{\infty} \gamma_i$.
  set y : ℕ → ℝ := fun n => x n + M * tailSum α n + tailSum γ n;
  -- Show that $y_n$ is non-increasing.
  have hy_noninc : ∀ n, y (n + 1) ≤ y n - β n := by
    intro n;
    have := hrec n;
    nlinarith [ hx_nn n, hx_nn ( n + 1 ), hα_nn n, hβ_nn n, hγ_nn n, hM n, hM ( n + 1 ), tailSum_succ hα_sum n, tailSum_succ hγ_sum n, mul_nonneg ( hα_nn n ) ( hx_nn n ), mul_nonneg ( hα_nn n ) ( hx_nn ( n + 1 ) ), mul_nonneg ( hα_nn n ) ( hM n |> le_trans ( hx_nn n ) ), mul_nonneg ( hα_nn n ) ( hM ( n + 1 ) |> le_trans ( hx_nn ( n + 1 ) ) ) ];
  -- Since $y_n$ is non-increasing and bounded below by $0$, it converges.
  have hy_conv : ∃ L, Filter.Tendsto y Filter.atTop (nhds L) := by
    have hy_noninc : Antitone y := by
      exact antitone_nat_of_succ_le fun n => by linarith [ hy_noninc n, hβ_nn n ] ;
    exact ⟨ _, tendsto_atTop_ciInf hy_noninc ⟨ 0, Set.forall_mem_range.mpr fun n => add_nonneg ( add_nonneg ( hx_nn n ) ( mul_nonneg ( show 0 ≤ M by linarith [ hx_nn 0, hM 0 ] ) ( tailSum_nonneg hα_nn n ) ) ) ( tailSum_nonneg hγ_nn n ) ⟩ ⟩;
  -- Since $y_n$ converges and $M \sum_{i=n}^{\infty} \alpha_i$ and $\sum_{i=n}^{\infty} \gamma_i$ tend to $0$, it follows that $x_n$ converges.
  obtain ⟨L, hL⟩ := hy_conv;
  have hx_conv : Filter.Tendsto x Filter.atTop (nhds L) := by
    have h_tail_zero : Filter.Tendsto (fun n => M * tailSum α n) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun n => tailSum γ n) Filter.atTop (nhds 0) := by
      exact ⟨ by simpa using tendsto_const_nhds.mul ( tendsto_tailSum hα_nn hα_sum ), by simpa using tendsto_tailSum hγ_nn hγ_sum ⟩;
    convert hL.sub ( h_tail_zero.1.add h_tail_zero.2 ) using 2 <;> ring;
  -- Since $y_n$ is non-increasing and bounded below by $0$, it follows that $\sum_{n=0}^{\infty} \beta_n$ converges.
  have hβ_sum : Summable β := by
    have h_telescope : ∀ N, ∑ n ∈ Finset.range N, β n ≤ y 0 - y N := by
      exact fun N => Nat.recOn N ( by norm_num ) fun n ihn => by rw [ Finset.sum_range_succ ] ; linarith [ hy_noninc n ] ;
    rw [ summable_iff_not_tendsto_nat_atTop_of_nonneg hβ_nn ];
    exact fun h => not_tendsto_atTop_of_tendsto_nhds ( tendsto_const_nhds.sub hL ) ( Filter.tendsto_atTop_mono h_telescope h );
  exact ⟨ ⟨ L, hx_conv ⟩, hβ_sum ⟩

/-
================================================================
§ 4  Almost-sure (stochastic) versions
================================================================

**Dvoretzky a.s. convergence**: pointwise a.e. lifting of
`det_contraction_convergence`. If random variables `X n ω` satisfy the
contraction recurrence for a.e. `ω`, then `X n → 0` a.s.
-/
theorem dvoretzky_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (a b : ℕ → ℝ)
    (hX_nn : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ X n ω)
    (ha_nn : ∀ n, 0 ≤ a n) (ha_le : ∀ n, a n ≤ 1)
    (hb_nn : ∀ n, 0 ≤ b n)
    (hrec : ∀ n, ∀ᵐ ω ∂μ, X (n + 1) ω ≤ (1 - a n) * X n ω + b n)
    (ha_div : ¬Summable a) (hb_sum : Summable b) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 0) := by
  filter_upwards [ MeasureTheory.ae_all_iff.2 hX_nn, MeasureTheory.ae_all_iff.2 hrec ] with ω hω₁ hω₂;
  exact det_contraction_convergence _ _ _ hω₁ ha_nn ha_le hb_nn hω₂ ha_div hb_sum

/-
**Robbins–Siegmund a.s. convergence**: almost-sure version of the
Robbins–Siegmund convergence theorem with random coefficient sequences.
-/
theorem robbins_siegmund_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X α β γ : ℕ → Ω → ℝ)
    (hX_nn : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ X n ω)
    (hα_nn : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ α n ω)
    (hβ_nn : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ β n ω)
    (hγ_nn : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ γ n ω)
    (hrec : ∀ n, ∀ᵐ ω ∂μ,
      X (n + 1) ω ≤ (1 + α n ω) * X n ω - β n ω + γ n ω)
    (hα_sum : ∀ᵐ ω ∂μ, Summable (fun n => α n ω))
    (hγ_sum : ∀ᵐ ω ∂μ, Summable (fun n => γ n ω)) :
    ∀ᵐ ω ∂μ, (∃ L, Tendsto (fun n => X n ω) atTop (𝓝 L)) ∧
              Summable (fun n => β n ω) := by
  filter_upwards [hα_sum, hγ_sum, ae_all_iff.2 hX_nn, ae_all_iff.2 hα_nn,
    ae_all_iff.2 hβ_nn, ae_all_iff.2 hγ_nn, ae_all_iff.2 hrec]
    with ω hωαs hωγs hωX hωα hωβ hωγ hωrec
  exact robbins_siegmund_det _ _ _ _ hωX hωα hωβ hωγ hωrec hωαs hωγs

-- ================================================================
-- § 5  Robbins–Monro step-size conditions and convergence
-- ================================================================

/-- **Robbins–Monro step-size conditions**: a non-negative sequence `a` with
`aₙ ≤ 1` for all `n`, `∑ aₙ = ∞` (ensures exploration), and
`∑ aₙ² < ∞` (controls noise variance).

These are the classical conditions for stochastic gradient descent (SGD)
and Q-learning convergence. The canonical example is `aₙ = 1/(n+1)`. -/
structure RobbinsMonroStepSize (a : ℕ → ℝ) : Prop where
  nonneg : ∀ n, 0 ≤ a n
  le_one : ∀ n, a n ≤ 1
  sum_diverges : ¬Summable a
  sum_sq_summable : Summable (fun n => a n ^ 2)

/-
**Robbins–Monro convergence**: under standard step-size conditions, if a
non-negative sequence satisfies `xₙ₊₁ ≤ (1 − aₙ) xₙ + C aₙ²` for some
constant `C ≥ 0`, then `xₙ → 0`.

This captures the convergence backbone of SGD: the `C aₙ²` term represents
bounded-variance noise scaled by the squared step size.
-/
theorem robbins_monro_convergence (x a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hx_nn : ∀ n, 0 ≤ x n)
    (hrec : ∀ n, x (n + 1) ≤ (1 - a n) * x n + C * a n ^ 2)
    (hRM : RobbinsMonroStepSize a) :
    Tendsto x atTop (𝓝 0) := by
  refine' det_contraction_convergence x a ( fun n => C * a n ^ 2 ) hx_nn hRM.nonneg hRM.le_one _ hrec _ _;
  · exact fun n => mul_nonneg hC ( sq_nonneg _ );
  · exact hRM.sum_diverges;
  · exact Summable.mul_left _ hRM.sum_sq_summable

/-
**SGD convergence (a.s.)**: stochastic version of Robbins–Monro convergence.
This is the foundational result for convergence of stochastic gradient descent
in machine learning and Q-learning in reinforcement learning.
-/
theorem sgd_convergence {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hX_nn : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ X n ω)
    (hrec : ∀ n, ∀ᵐ ω ∂μ, X (n + 1) ω ≤ (1 - a n) * X n ω + C * a n ^ 2)
    (hRM : RobbinsMonroStepSize a) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 0) := by
  apply_rules [ dvoretzky_ae ];
  · exact hRM.nonneg;
  · exact hRM.le_one;
  · exact fun n => mul_nonneg hC ( sq_nonneg _ );
  · exact hRM.sum_diverges;
  · exact Summable.mul_left _ hRM.sum_sq_summable

end Pythia.StochasticApproximation.Dvoretzky