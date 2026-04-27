/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Two-state von Neumann entropy non-negativity

For a qubit density matrix `ρ` diagonal in some basis with
eigenvalues `(p, 1-p)`, the von Neumann entropy
`S(ρ) = -tr(ρ log ρ)` reduces to the Shannon binary entropy
`H(p) = -p log p - (1-p) log(1-p)`. This module proves the
non-negativity of `H(p)` for `p ∈ [0, 1]` (interpreting
`0 · log 0 = 0` via `Real.negMulLog`).

The result extends in a straightforward way to general qubit states
by spectral decomposition of `ρ`; the diagonal-basis case is the
content-bearing inequality.

## Main results

* `von_neumann_entropy_nonneg_two_state` — `0 ≤ -p log p - (1-p) log(1-p)`
  for any `p ∈ [0, 1]`.

## Why this lemma

Mathlib has `Real.negMulLog_nonneg` over `[0, 1]`; pythia exposes
the two-summand form under its quantum-information label so the
`pythia` cascade can close qubit-entropy non-negativity goals
directly without unfolding to the `Real.negMulLog` primitive.

## References

* von Neumann, J. "Mathematische Grundlagen der Quantenmechanik."
  Springer (1932); English translation 1955.
* Shannon, C.E. "A Mathematical Theory of Communication."
  Bell System Technical Journal 27(3): 379-423 (1948).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Quantum

/-- **Two-state von Neumann entropy non-negativity.** For any
`p ∈ [0, 1]`, `0 ≤ -p · log p - (1 - p) · log(1 - p)`. Each term is
`Real.negMulLog` evaluated on `[0, 1]`, hence non-negative by
`Real.negMulLog_nonneg`; the sum inherits the bound by `linarith`.
The boundary convention `0 · log 0 = 0` is inherited from
`Real.negMulLog`. -/
@[stat_lemma]
theorem von_neumann_entropy_nonneg_two_state {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    0 ≤ -p * Real.log p - (1 - p) * Real.log (1 - p) := by
  have hpos1 : 0 ≤ Real.negMulLog p := Real.negMulLog_nonneg h0 h1
  have h1p_lo : (0 : ℝ) ≤ 1 - p := by linarith
  have h1p_hi : (1 - p : ℝ) ≤ 1 := by linarith
  have hpos2 : 0 ≤ Real.negMulLog (1 - p) := Real.negMulLog_nonneg h1p_lo h1p_hi
  -- `Real.negMulLog x = -x * Real.log x`; rewrite both summands.
  have e1 : Real.negMulLog p = -p * Real.log p := by
    unfold Real.negMulLog; ring
  have e2 : Real.negMulLog (1 - p) = -(1 - p) * Real.log (1 - p) := by
    unfold Real.negMulLog; ring
  rw [e1] at hpos1
  rw [e2] at hpos2
  linarith

end Pythia.Quantum
