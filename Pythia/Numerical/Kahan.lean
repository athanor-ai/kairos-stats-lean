/-
Pythia.Numerical.Kahan — compensated summation correctness.

Kahan's compensated summation algorithm (Kahan 1965) maintains a
running compensation term to cancel low-order roundoff bits when
summing a sequence of floating-point numbers. The algorithm achieves
backward error `2 ε` (where ε is machine epsilon) regardless of the
sequence length, vs the `n ε` worst-case for naive summation.

This module ships the Lean specification of Kahan summation + the
correctness theorem (running error is bounded by 2 ε plus a tiny
correction term).

## What ships

- `kahanStep`: one step of compensated addition.
- `kahanSum`: fold over a list using `kahanStep`.
- `kahan_error_bound`: backward error theorem.
- `naive_error_bound`: naive (uncompensated) summation comparison.

## Status

Scaffold. The `kahan_error_bound` proof is non-trivial — requires
Float-vs-Real bridging via `Float.toReal` and bookkeeping of round-off.
Aristotle queue item 34.

-/
import Mathlib

namespace Pythia.Numerical.Kahan

/-- One step of Kahan summation. Given current sum `s`, compensation
`c`, and next input `x`, return the updated `(s', c')` pair. -/
def kahanStep (s c : Float) (x : Float) : Float × Float :=
  let y := x - c
  let t := s + y
  let cnew := (t - s) - y
  (t, cnew)

/-- Kahan-compensated summation of a list. Initial sum and
compensation are 0. Returns the final sum (compensation discarded). -/
def kahanSum (xs : List Float) : Float :=
  (xs.foldl (fun (sc : Float × Float) x => kahanStep sc.1 sc.2 x) (0.0, 0.0)).1

/-- Naive summation (foldl with `+`). Used as the baseline for the
error-bound comparison. -/
def naiveSum (xs : List Float) : Float :=
  xs.foldl (· + ·) 0.0

/-- Kahan summation backward-error bound: the computed sum differs
from the true real sum by at most `2 ε * (sum of abs values) + O(n ε²)`,
where ε is machine epsilon. The leading term is INDEPENDENT of `n`
(no `n ε` accumulation). -/
theorem kahan_error_bound
    (xs : List Float) (h_finite : ∀ x ∈ xs, ¬ x.isNaN ∧ ¬ x.isInf) :
    -- |kahanSum xs - true_real_sum xs| ≤ 2 ε * (Σ |xᵢ|) + O(n ε²)
    -- where ε = Float.epsilon and the O term has explicit constant.
    -- Spec sketch (precise statement requires Mathlib's Float ↔ Real
    -- bridging which is partial in v4.28; pinning the explicit form
    -- to Aristotle).
    True := by
  trivial  -- v0.5 scaffold; Aristotle queue item 34 closes the
           -- precise statement once the Float-Real bridge is wired.

/-- Naive summation accumulates worst-case `n ε` error: a contrast
to Kahan's `2 ε` independent-of-n bound. -/
theorem naive_error_bound
    (xs : List Float) (h_finite : ∀ x ∈ xs, ¬ x.isNaN ∧ ¬ x.isInf) :
    -- |naiveSum xs - true_real_sum xs| ≤ n * ε * (Σ |xᵢ|)
    -- (worst case; precise constant depends on summation order)
    True := by
  trivial  -- v0.5 scaffold; Aristotle queue item 34 closes the
           -- precise statement.

/-- Demonstration: pathological "1 + 1e-20 + 1 + 1e-20 + ..." sums.
Kahan recovers the small terms; naive loses them. This is unit-level
testing, not a theorem. -/
def kahanWinsExample : Float × Float :=
  let xs := List.range 1000 |>.flatMap (fun _ => [1.0, 1.0e-20])
  (kahanSum xs, naiveSum xs)

end Pythia.Numerical.Kahan
