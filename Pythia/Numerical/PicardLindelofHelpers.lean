/-
Helper lemmas for the Picard-Lindelöf theorem.

These are standalone results that support the main theorems in
`PicardLindelof.lean`. They are proved independently of that file.
-/
import Mathlib

namespace Pythia.Numerical.PicardLindelof

open MeasureTheory Set Metric

/-- Uniqueness of global ODE solutions. -/
lemma global_ode_unique (f : ℝ → ℝ → ℝ) (K : NNReal)
    (hK_lip : ∀ t : ℝ, LipschitzWith K (fun y => f t y))
    (y z : ℝ → ℝ)
    (hy : ∀ t : ℝ, HasDerivAt y (f t (y t)) t)
    (hz : ∀ t : ℝ, HasDerivAt z (f t (z t)) t)
    (heq : y 0 = z 0) : y = z :=
  ODE_solution_unique_univ (v := fun t y => f t y) (s := fun _ => Set.univ)
    (fun t => (hK_lip t).lipschitzOnWith)
    (fun t => ⟨hy t, Set.mem_univ _⟩)
    (fun t => ⟨hz t, Set.mem_univ _⟩)
    heq

/-- f is jointly continuous when it is uniformly Lipschitz in y and
continuous in t for each y. -/
lemma f_continuous (f : ℝ → ℝ → ℝ) (K : NNReal)
    (hK_lip : ∀ t : ℝ, LipschitzWith K (fun y => f t y))
    (hf_cont : ∀ y : ℝ, Continuous (fun t => f t y)) :
    Continuous (fun p : ℝ × ℝ => f p.1 p.2) := by
  rw [Metric.continuous_iff]
  intro ⟨t₀, y₀⟩ ε hε
  have hcont : ContinuousAt (fun t => f t y₀) t₀ := (hf_cont y₀).continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ₁, hδ₁, hδ₁_bound⟩ := hcont (ε / 2) (half_pos hε)
  refine ⟨min δ₁ (ε / (2 * (↑K + 1))), lt_min hδ₁ (div_pos hε (by positivity)), ?_⟩
  intro ⟨t, y⟩ hty
  simp only [Prod.dist_eq, max_lt_iff] at hty
  have ht : dist t t₀ < δ₁ := lt_of_lt_of_le hty.1 (min_le_left _ _)
  have hy : dist y y₀ < ε / (2 * (↑K + 1)) := lt_of_lt_of_le hty.2 (min_le_right _ _)
  have hK_nn := K.coe_nonneg
  calc dist (f t y) (f t₀ y₀)
      ≤ dist (f t y) (f t y₀) + dist (f t y₀) (f t₀ y₀) := dist_triangle _ _ _
    _ ≤ ↑K * dist y y₀ + dist (f t y₀) (f t₀ y₀) := by
        gcongr; exact (hK_lip t).dist_le_mul y y₀
    _ < ↑K * (ε / (2 * (↑K + 1))) + ε / 2 := by
        apply add_lt_add_of_le_of_lt
        · exact mul_le_mul_of_nonneg_left hy.le hK_nn
        · exact hδ₁_bound ht
    _ ≤ ε / 2 + ε / 2 := by
        gcongr
        calc ↑K * (ε / (2 * (↑K + 1)))
            = ε * ↑K / (2 * (↑K + 1)) := by ring
          _ ≤ ε * (↑K + 1) / (2 * (↑K + 1)) := by gcongr; linarith
          _ = ε / 2 := by field_simp
    _ = ε := add_halves ε

/-- Local existence at any initial condition, given globally Lipschitz
and continuous in t. -/
lemma ode_local_exists (f : ℝ → ℝ → ℝ) (K : NNReal)
    (hK_lip : ∀ t : ℝ, LipschitzWith K (fun y => f t y))
    (hf_cont : ∀ y : ℝ, Continuous (fun t => f t y))
    (t₀ y₁ : ℝ) :
    ∃ (δ : ℝ) (_ : 0 < δ) (y : ℝ → ℝ),
      y t₀ = y₁ ∧ ∀ t ∈ Icc (t₀ - δ) (t₀ + δ), HasDerivAt y (f t (y t)) t := by
  set hfc := f_continuous f K hK_lip hf_cont
  obtain ⟨M, hM_bound⟩ : ∃ M : ℝ, ∀ t ∈ Icc (t₀ - 1) (t₀ + 1),
      ∀ y ∈ Icc (y₁ - 1) (y₁ + 1), |f t y| ≤ M := by
    obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn
      (CompactIccSpace.isCompact_Icc.prod CompactIccSpace.isCompact_Icc)
      (show ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
        (Icc (t₀ - 1) (t₀ + 1) ×ˢ Icc (y₁ - 1) (y₁ + 1)) from hfc.continuousOn)
    exact ⟨M, fun t ht y hy => hM (t, y) ⟨ht, hy⟩⟩
  set δ := 1 / (max M 1 + 1) with hδ_def
  have hδ_pos : 0 < δ := by positivity
  have hδ_le_one : δ ≤ 1 :=
    div_le_self zero_le_one (by linarith [le_max_right M 1])
  have hδ_mul_M_le_one : δ * M ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_iff₀] <;> nlinarith [le_max_left M 1, le_max_right M 1]
  have h_picard_lindelof : IsPicardLindelof f
      (⟨t₀, by constructor <;> linarith⟩ : ↑(Icc (t₀ - δ) (t₀ + δ)))
      y₁ 1 0 (⟨M.toNNReal, by positivity⟩ : NNReal) K := by
    constructor
    · exact fun t _ => (hK_lip t).lipschitzOnWith
    · exact fun x _ => (hf_cont x).continuousOn
    · simp +zetaDelta at *
      exact fun t ht₁ ht₂ x hx =>
        Or.inl <| hM_bound t (by linarith) (by linarith) x
          (by linarith [abs_le.mp hx]) (by linarith [abs_le.mp hx])
    · norm_num +zetaDelta at *
      cases max_cases M 0 <;> cases max_cases M 1 <;>
        nlinarith [inv_mul_cancel₀ hδ_pos.ne']
  obtain ⟨α, hα₁, hα₂⟩ := h_picard_lindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨δ / 2, half_pos hδ_pos, α, hα₁, fun t ht =>
    (hα₂ t ⟨by linarith [ht.1], by linarith [ht.2]⟩).hasDerivAt
      (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))⟩

end Pythia.Numerical.PicardLindelof
