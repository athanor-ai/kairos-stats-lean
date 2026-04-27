/-
Pythia starter pack: quantum information / von Neumann entropy.

Two-state (qubit) von Neumann entropy non-negativity, expressed as
the classical Shannon binary entropy on the diagonal:
`S(p) = -p log p - (1-p) log (1-p) ≥ 0` for `p ∈ [0, 1]`.

Run via:
    lake env lean examples/quantum/01_von_neumann_entropy.lean
-/
import Pythia.Quantum.VonNeumannEntropyNonnegTwoState
import Pythia.Tactic.PythiaBang

open Pythia.Quantum

/-! ## Two-state von Neumann entropy is non-negative

For a qubit density matrix in the diagonal basis with eigenvalue
`p ∈ [0, 1]`, the von Neumann entropy collapses to the Shannon
binary entropy `H(p) = -p log p - (1-p) log (1-p)`, which is
non-negative on `[0, 1]`. Boundary cases `p = 0` and `p = 1` are
the trivial entropy-zero pure states; the interior is the
strict-positive mixed-state regime.

The `pythia!` cascade does not close this goal: aesop's
term-unification on the `@[stat_lemma]`-tagged theorem requires
matching the `Real.log`-heavy conclusion, and the safe-apply
mode loses traction. The named theorem closes it directly. -/
example {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    0 ≤ -p * Real.log p - (1 - p) * Real.log (1 - p) :=
  von_neumann_entropy_nonneg_two_state h0 h1
