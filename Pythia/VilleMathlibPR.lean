/-
Copyright (c) 2026 Athanor AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Athanor AI
-/
module

public import Mathlib.Probability.Notation
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Martingale.OptionalStopping

/-! # Ville's inequality for non-negative supermartingales

Ville's inequality is the supermartingale analogue of Doob's maximal inequality. For a
non-negative supermartingale `f` on a filtration `𝒢` with integrable initial value and
any `ε : ℝ≥0`:

$$\varepsilon \cdot \mu\{\omega \mid \exists t,\ \varepsilon \le f_t(\omega)\}
  \;\le\; \mu[f_0].$$

Doob's inequality (`maximal_ineq`) bounds a non-negative submartingale's running maximum
over `[0, n]` by the expectation at the end time `μ[f n]`. Ville's inequality strengthens
the bound on the supermartingale side: the running maximum is bounded by the expectation
at the *initial* time `μ[f 0]`, and the bound extends to all of `ℕ`. The proof passes
through the first-crossing stopping time and the supermartingale form of optional stopping.

### Main results

* `MeasureTheory.ville_ineq`: the finite-horizon form, over `Finset.range (n + 1)`.
* `MeasureTheory.ville_ineq_countable`: the countable-time form, over all `t : ℕ`.

-/

public section

open Finset
open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {f : ℕ → Ω → ℝ} {𝒢 : Filtration ℕ m0}

/-- The expected stopped value of a supermartingale at a bounded stopping time `τ` is at
most the expectation of the initial term. This is the supermartingale counterpart of
`Submartingale.expected_stoppedValue_mono`, obtained by applying the submartingale
version to `-f` with the constant zero stopping time. -/
theorem Supermartingale.expected_stoppedValue_le
    (hsup : Supermartingale f 𝒢 μ) {τ : Ω → ℕ∞} (hτ : IsStoppingTime 𝒢 τ)
    {N : ℕ} (hτN : ∀ ω, τ ω ≤ ↑N) :
    μ[stoppedValue f τ] ≤ μ[f 0] := by
  have h_sub :
      μ[stoppedValue (-f) (fun _ => (0 : ℕ∞))] ≤ μ[stoppedValue (-f) τ] :=
    Submartingale.expected_stoppedValue_mono hsup.neg
      (isStoppingTime_const 𝒢 0) hτ (fun _ => zero_le _) hτN
  simp_all [integral_neg, stoppedValue]

private theorem ville_aux_stoppedValue_ge
    (hnonneg : 0 ≤ f) {ε : ℝ≥0} (n : ℕ) (ω : Ω)
    (hω : ∃ t ∈ range (n + 1), (ε : ℝ) ≤ f t ω) :
    (ε : ℝ) ≤ stoppedValue f
      (fun ω' => ↑(hittingBtwn f {y | (ε : ℝ) ≤ y} 0 n ω')) ω := by
  apply hittingBtwn_mem_set
  aesop

/-- **Ville's inequality, finite-horizon form.** For a non-negative supermartingale `f`
on a finite measure space, any `ε : ℝ≥0`, and any horizon `n : ℕ`:
$$\varepsilon \cdot \mu\{\omega \mid \exists t \in [0, n],\ \varepsilon \le f_t(\omega)\}
  \;\le\; \mu[f_0].$$

This is the supermartingale analogue of `maximal_ineq`; the bound is on the initial
expectation rather than `μ[f n]`. -/
theorem ville_ineq (hsup : Supermartingale f 𝒢 μ) (hnonneg : 0 ≤ f)
    (hint : Integrable (f 0) μ) {ε : ℝ≥0} (n : ℕ) :
    (ε : ℝ≥0∞) * μ {ω | ∃ t ∈ range (n + 1), (ε : ℝ) ≤ f t ω}
      ≤ ENNReal.ofReal (μ[f 0]) := by
  set τ : Ω → ℕ∞ :=
    fun ω => ↑(hittingBtwn f {y : ℝ | (ε : ℝ) ≤ y} 0 n ω) with hτ_def
  have hτ_stop : IsStoppingTime 𝒢 τ :=
    hsup.adapted.isStoppingTime_hittingBtwn (by grind) measurableSet_Ici
  have hτ_bdd : ∀ ω, τ ω ≤ (n : ℕ∞) := by
    intro ω; simp [τ, hittingBtwn_le]
  set g : Ω → ℝ := stoppedValue f τ with hg_def
  have h_integrable : Integrable g μ := by
    exact integrable_stoppedValue ℕ hτ_stop hsup.integrable hτ_bdd
  have h_markov : (ε : ℝ≥0∞) * μ {ω | (ε : ℝ) ≤ g ω}
      ≤ ENNReal.ofReal (μ[g]) := by
    have h_nonneg : ∀ᵐ ω ∂μ, 0 ≤ g ω := by
      filter_upwards with ω
      simp only [g, stoppedValue]
      exact hnonneg _ _
    have := mul_meas_ge_le_integral_of_nonneg h_nonneg (ε : ℝ) h_integrable
    calc (ε : ℝ≥0∞) * μ {ω | (ε : ℝ) ≤ g ω}
        = ENNReal.ofReal ((ε : ℝ) * μ.real {ω | (ε : ℝ) ≤ g ω}) := by
          rw [ENNReal.ofReal_mul ε.coe_nonneg]
          rw [ENNReal.ofReal_coe_nnreal]
          rw [Measure.real]
          rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ ≤ ENNReal.ofReal (μ[g]) := ENNReal.ofReal_le_ofReal this
  have h_subset :
      {ω | ∃ t ∈ range (n + 1), (ε : ℝ) ≤ f t ω} ⊆ {ω | (ε : ℝ) ≤ g ω} :=
    fun ω hω => ville_aux_stoppedValue_ge hnonneg n ω hω
  have h_mono : (ε : ℝ≥0∞) * μ {ω | ∃ t ∈ range (n + 1), (ε : ℝ) ≤ f t ω}
      ≤ (ε : ℝ≥0∞) * μ {ω | (ε : ℝ) ≤ g ω} :=
    mul_le_mul_left' (measure_mono h_subset) _
  have h_stop_le : μ[g] ≤ μ[f 0] :=
    Supermartingale.expected_stoppedValue_le hsup hτ_stop hτ_bdd
  calc (ε : ℝ≥0∞) * μ {ω | ∃ t ∈ range (n + 1), (ε : ℝ) ≤ f t ω}
      ≤ (ε : ℝ≥0∞) * μ {ω | (ε : ℝ) ≤ g ω} := h_mono
    _ ≤ ENNReal.ofReal (μ[g]) := h_markov
    _ ≤ ENNReal.ofReal (μ[f 0]) := ENNReal.ofReal_le_ofReal h_stop_le

/-- **Ville's inequality, countable-time form.** For a non-negative supermartingale `f`
on a finite measure space and any `ε : ℝ≥0`:
$$\varepsilon \cdot \mu\{\omega \mid \exists t : \mathbb{N},\ \varepsilon \le f_t(\omega)\}
  \;\le\; \mu[f_0].$$

This is the countable-time limit of `ville_ineq` via monotone convergence. It is the
measure-theoretic substrate for anytime-valid confidence sequences: taking `ε = 1/α`
and `μ[f_0] = 1` recovers the standard `1/α` coverage bound. -/
theorem ville_ineq_countable (hsup : Supermartingale f 𝒢 μ) (hnonneg : 0 ≤ f)
    (hint : Integrable (f 0) μ) {ε : ℝ≥0} :
    (ε : ℝ≥0∞) * μ {ω | ∃ t : ℕ, (ε : ℝ) ≤ f t ω} ≤ ENNReal.ofReal (μ[f 0]) := by
  have h_eq : {ω : Ω | ∃ t : ℕ, (ε : ℝ) ≤ f t ω}
      = ⋃ n : ℕ, {ω | ∃ t ∈ range (n + 1), (ε : ℝ) ≤ f t ω} := by
    ext ω; aesop
  have h_mono : Monotone
      (fun n => {ω : Ω | ∃ t ∈ range (n + 1), (ε : ℝ) ≤ f t ω}) := by
    intro n m hnm ω ⟨t, ht_mem, ht_val⟩
    exact ⟨t, mem_range.mpr (by linarith [mem_range.mp ht_mem]), ht_val⟩
  rw [h_eq, measure_iUnion_eq_iSup h_mono.directed_le, ENNReal.mul_iSup]
  exact iSup_le fun n => ville_ineq hsup hnonneg hint n

end MeasureTheory
