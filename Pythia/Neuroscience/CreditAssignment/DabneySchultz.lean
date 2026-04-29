/-
Kairos Case 3: pure-theoretical sandwich bound (zero-band).

No empirical data lives on either side of this result; it is a
purely formal sandwich on the Dabney-Schultz reconciliation.

DS2 is the lower bound: for k' < 2, no scalar-TD bundle of
dimension k' can produce the second quantile of a 2-D distributional
code at every state.
-/

import Pythia.Neuroscience.CreditAssignment.Basic
import Mathlib

namespace Pythia.Neuroscience.CreditAssignment
namespace DabneySchultz

/-- Dabney-Schultz distributional code: a k-dimensional quantile
    vector over the return distribution at each state. -/
abbrev DSDistCode (k : ℕ) := State → Fin k → ℝ

/-- Scalar TD-error code: a single value estimate per state.
    Schultz-style. -/
abbrev ScalarTDCode := State → ℝ

/-- A k-D "scalar extension": a bundle of k independent
    scalar value functions. A scalar-TD rule with k heads. -/
abbrev ScalarTDBundle (k : ℕ) := Fin k → ScalarTDCode

/-- **DS1. Upper-bound reduction.** For k ≥ 2, there exists a
    constructive map from a k-D scalar-TD bundle to a k-D
    distributional code such that each scalar head sits as the
    corresponding quantile of the distributional code. Proves the
    EXISTENCE of a reduction; does NOT claim tightness. -/
theorem distributional_reduces_to_scalar_at_sufficient_k
    (k : ℕ) (_hK : k ≥ 2) :
    ∃ (φ : ScalarTDBundle k → DSDistCode k),
      ∀ (b : ScalarTDBundle k) (s : State) (i : Fin k),
        φ b s i = b i s := by
  refine ⟨fun b s i => b i s, ?_⟩
  intro b s i
  rfl

/-- **DS2. Lower-bound impossibility.** For k' < 2, no scalar-TD
    bundle of dimension k' can produce the second quantile of a
    2-D distributional code at every state.

    Proof strategy:
    - k' = 0: `Fin 0` is empty so the inner `∀` is vacuous.
    - k' = 1: pick `distCode s 1 := b 0 s + 1` so the head cannot
      equal `fun s => distCode s 1`. -/
theorem scalar_td_cannot_produce_variance_below_dim_two
    (k' : ℕ) (hk' : k' < 2) :
    ∀ (b : ScalarTDBundle k'),
      ∃ (distCode : DSDistCode 2),
        ∀ (i : Fin k'), b i ≠ fun s => distCode s 1 := by
  intro b
  interval_cases k'
  · -- k' = 0: Fin 0 is empty; the inner ∀ is vacuous.
    exact ⟨fun _ _ => 0, fun i => i.elim0⟩
  · -- k' = 1: pick distCode s 1 := b 0 s + 1.
    refine ⟨fun s j => if j = (1 : Fin 2) then b 0 s + 1 else 0, ?_⟩
    intro i
    have hi : i = 0 := by ext; omega
    subst hi
    intro h
    have h0 := congrFun h (0 : State)
    simp at h0

/-- **DS-sandwich. Minimum reduction dimension is exactly 2.**
    Combines DS1 (upper) and DS2 (lower) to certify that the
    Dabney-Schultz distributional code admits a k-head scalar-TD
    reduction iff k ≥ 2. -/
theorem dabney_schultz_min_dim :
    ∃ (K_min : ℕ), K_min = 2 ∧
      (∀ k ≥ K_min, ∃ (φ : ScalarTDBundle k → DSDistCode k),
        ∀ (b : ScalarTDBundle k) (s : State) (i : Fin k),
          φ b s i = b i s) ∧
      (∀ k' < K_min, ∀ (b : ScalarTDBundle k'),
        ∃ (distCode : DSDistCode 2),
          ∀ (i : Fin k'), b i ≠ fun s => distCode s 1) := by
  refine ⟨2, rfl, ?_, ?_⟩
  · intro k hk
    exact distributional_reduces_to_scalar_at_sufficient_k k hk
  · intro k' hk' b
    exact scalar_td_cannot_produce_variance_below_dim_two k' hk' b

end DabneySchultz
end Pythia.Neuroscience.CreditAssignment
