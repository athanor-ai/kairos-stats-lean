/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Itô isometry — finite-dimensional discrete analogue

The Itô isometry says that for a square-integrable predictable
process `f`, the L² norm of the Itô integral `∫ f dW` equals the L²
norm of `f` against the underlying Lebesgue-times-Brownian quadratic
variation. The discrete simplification used here is the
Cauchy-Schwarz form: for any `f : Fin n → ℝ`,
`(∑ i, f i)^2 ≤ n · ∑ i, (f i)^2`. This is the discrete analogue of
the L² isometric embedding (the equality case is when `f` is
constant; the strict inequality bounds the worst-case mass
concentration).

## Main results

* `ito_isometry_finite_dim` — `(∑ i, f i)^2 ≤ (n : ℝ) · ∑ i, (f i)^2`
  for any `f : Fin n → ℝ`.

## Why this lemma

Mathlib has `sq_sum_le_card_mul_sum_sq` over arbitrary linearly-
ordered semirings; pythia exposes the `Fin n` specialization with
the discrete-Itô framing so the `pythia` cascade can close
finite-dim stochastic-integral goals without hunting through
the Chebyshev family by name.

## References

* Itô, K. "On stochastic differential equations." Memoirs of the
  American Mathematical Society 4: 1-51 (1951).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Stochastic

/-- **Itô isometry, discrete finite-dimensional form.** For any
real-valued `f : Fin n → ℝ`, `(∑ i, f i)^2 ≤ (n : ℝ) · ∑ i, (f i)^2`.
This is the Cauchy-Schwarz / power-mean form of the Itô isometry
in finite dimension. Closes via Mathlib's
`sq_sum_le_card_mul_sum_sq` after rewriting `Finset.univ.card`
as `n`. -/
@[stat_lemma]
theorem ito_isometry_finite_dim {n : ℕ} (f : Fin n → ℝ) :
    (∑ i, f i)^2 ≤ (n : ℝ) * ∑ i, (f i)^2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := f)
  simpa using h

end Pythia.Stochastic
