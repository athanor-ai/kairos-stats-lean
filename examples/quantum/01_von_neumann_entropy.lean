/-
Pythia starter pack — quantum information / von Neumann entropy.

Two-state (qubit) von Neumann entropy non-negativity, expressed as
the classical Shannon binary entropy on the diagonal:
`S(p) = -p log p - (1-p) log (1-p) ≥ 0` for `p ∈ [0, 1]`.

Run via:
    lake env lean examples/quantum/01_von_neumann_entropy.lean
-/
import Pythia.Quantum.VonNeumannEntropyNonnegTwoState
import Pythia.Tactic.PythiaBang

open Pythia

/-! ## Two-state von Neumann entropy is non-negative

For a qubit density matrix in the diagonal basis with eigenvalue
`p ∈ [0, 1]`, the von Neumann entropy collapses to the Shannon
binary entropy `H(p) = -p log p - (1-p) log (1-p)`, which is
non-negative on `[0, 1]`. The boundary cases `p = 0` and `p = 1`
are the trivial entropy-zero pure states; the interior is the
strict-positive mixed-state regime. -/
example (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    0 ≤ -p * Real.log p - (1 - p) * Real.log (1 - p) :=
  von_neumann_entropy_nonneg_two_state p h0 h1
