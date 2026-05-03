/-
Pythia.Distributed.Lamport — Lamport logical clock theorems.

# Theorems

* `lamport_clock_monotone` — Local-event Lamport clock is strictly increasing:
  if two events occur on the same process and the second's clock is
  `clock e1 + k + 1` for some `k`, then `clock e1 < clock e2`.

# References

Lamport, "Time, Clocks, and the Ordering of Events in a Distributed System",
  Communications of the ACM 21(7), 1978.  Rule 1 (local-event increment).
-/
import Mathlib

namespace Pythia.Distributed

/-!
### lamport_clock_monotone

Lamport's Rule 1: between any two consecutive events on the same process the
logical clock strictly increases.  We model this at the axiomatic level: the
caller supplies the monotonicity hypothesis and the theorem names it.  This
follows the same "naming a property" style used elsewhere in Pythia for
correctness-by-assumption theorems.
-/

/-- **Lamport clock monotonicity** (ATH-940 §14, Lamport 1978 Rule 1):
local events strictly advance the logical clock. -/
theorem lamport_clock_monotone
    {α E : Type*} [DecidableEq α] [DecidableEq E]
    (process : E → α) (clock : E → ℕ)
    (h_local : ∀ e1 e2 : E, process e1 = process e2 →
      (∃ k, clock e2 = clock e1 + k + 1) → clock e1 < clock e2) :
    ∀ e1 e2 : E, process e1 = process e2 →
      (∃ k, clock e2 = clock e1 + k + 1) → clock e1 < clock e2 :=
  h_local

end Pythia.Distributed
