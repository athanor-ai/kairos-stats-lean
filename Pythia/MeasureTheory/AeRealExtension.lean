/-
Pythia.MeasureTheory.AeRealExtension -- bridge from rationals to reals
for almost-everywhere continuous identities.

A common pattern in conditional MGF / characteristic-function proofs is

  step 1: prove an identity f s a = g s a for s ∈ ℚ (almost surely);
  step 2: extend to s ∈ ℝ using continuity in s.

Step 2 traditionally needs care: the order of quantifiers (∀ s, ae a)
versus (ae a, ∀ s) does not commute over uncountable ℝ. The standard
fix: use ae_all_iff over the countable ℚ to get (ae a, ∀ q ∈ ℚ),
then upgrade to (ae a, ∀ s ∈ ℝ) via density of ℚ in ℝ + ae continuity
of both sides in s, then swap back to (∀ s, ae a).

This file provides that bridge as a reusable lemma.
-/
import Mathlib

namespace Pythia.MeasureTheory

open Filter Topology
open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}

/-- Bridge: an almost-sure equality on rationals extends to an
almost-sure equality on reals when both sides are almost-surely
continuous in the parameter.

Concretely, if `f, g : ℝ → α → ℝ` are such that `s ↦ f s a` and
`s ↦ g s a` are continuous for almost every `a`, and `f q =ᵐ[μ] g q`
for every rational `q`, then `f s =ᵐ[μ] g s` for every real `s`.

This is the fundamental tool for promoting a conditional-MGF identity
proved on rationals (via independence + Mathlib's gaussianReal MGF) to
the full real line. -/
theorem aeEq_of_aeEq_rat_of_aeContinuous
    {f g : ℝ → α → ℝ}
    (hf_cont : ∀ᵐ a ∂μ, Continuous (fun s : ℝ => f s a))
    (hg_cont : ∀ᵐ a ∂μ, Continuous (fun s : ℝ => g s a))
    (h_rat : ∀ q : ℚ, f (q : ℝ) =ᵐ[μ] g (q : ℝ)) :
    ∀ s : ℝ, f s =ᵐ[μ] g s := by
  -- Combine the countable family of ae equalities at each rational
  -- into a single ae statement quantified over all rationals.
  have h_ae_all_rat : ∀ᵐ a ∂μ, ∀ q : ℚ, f (q : ℝ) a = g (q : ℝ) a := by
    rw [MeasureTheory.ae_all_iff]
    exact h_rat
  -- Combine with the ae continuity hypotheses.
  have h_combined : ∀ᵐ a ∂μ,
      (Continuous (fun s : ℝ => f s a)) ∧
      (Continuous (fun s : ℝ => g s a)) ∧
      (∀ q : ℚ, f (q : ℝ) a = g (q : ℝ) a) := by
    filter_upwards [hf_cont, hg_cont, h_ae_all_rat] with a hfc hgc hrat
    exact ⟨hfc, hgc, hrat⟩
  -- For ae a, two continuous functions agreeing on the dense subset
  -- ℚ ⊆ ℝ must agree everywhere.
  have h_ae_all_real : ∀ᵐ a ∂μ, ∀ s : ℝ, f s a = g s a := by
    filter_upwards [h_combined] with a ⟨hfc, hgc, hrat⟩
    intro s
    -- Use density of ℚ in ℝ via rational approximation.
    have h_dense : Dense (Set.range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast
    -- The set where f and g agree contains ℚ and is closed
    -- (preimage of {0} under the continuous map s ↦ f s a - g s a).
    have h_eq_set_closed : IsClosed {s : ℝ | f s a = g s a} := by
      have h_eq : {s : ℝ | f s a = g s a} = (fun s => f s a - g s a) ⁻¹' {0} := by
        ext s; simp [sub_eq_zero]
      rw [h_eq]
      exact IsClosed.preimage (hfc.sub hgc) isClosed_singleton
    -- ℚ ⊆ {s | f s a = g s a}, and the latter is closed, so its
    -- closure (= ℝ) is also contained.
    have h_rat_subset : Set.range ((↑) : ℚ → ℝ) ⊆ {s : ℝ | f s a = g s a} := by
      rintro _ ⟨q, rfl⟩
      exact hrat q
    have h_closure : closure (Set.range ((↑) : ℚ → ℝ)) ⊆ {s : ℝ | f s a = g s a} :=
      h_eq_set_closed.closure_subset_iff.mpr h_rat_subset
    have h_all : Set.univ ⊆ {s : ℝ | f s a = g s a} := by
      rw [← h_dense.closure_eq]
      exact h_closure
    exact h_all (Set.mem_univ s)
  -- Swap the quantifier order back: (ae a, ∀ s) ⟹ (∀ s, ae a).
  intro s
  filter_upwards [h_ae_all_real] with a h
  exact h s

end Pythia.MeasureTheory
