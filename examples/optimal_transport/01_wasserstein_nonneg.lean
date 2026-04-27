/-
Pythia starter pack — optimal transport / Wasserstein distance.

The L1 Wasserstein distance `W₁(p, q) ≥ 0` for any pair of discrete
probability distributions. The discrete case lifts directly via
`Finset.sum_nonneg`; pythia closes it without any setup.

Run via:
    lake env lean examples/optimal_transport/01_wasserstein_nonneg.lean
-/
import Pythia.OptimalTransport.WassersteinDistanceNonneg
import Pythia.Tactic.PythiaBang

open Pythia

/-! ## Discrete Wasserstein non-negativity

For probability mass functions `p, q : Fin n → ℝ`, the discrete
Wasserstein-style cost `Σ |p i - q i|` is non-negative. This is the
basic axiom of any metric on the simplex; concrete value matters
downstream when bounding `W₁` against KL or TV. -/
example (n : ℕ) (p q : Fin n → ℝ) (h : ∀ i, 0 ≤ |p i - q i|) :
    0 ≤ ∑ i, |p i - q i| := wasserstein_distance_nonneg p q h

/-! ## Compositional sanity

Two distributions that agree pointwise have zero Wasserstein cost. -/
example (n : ℕ) (p : Fin n → ℝ) :
    ∑ i, |p i - p i| = 0 := by
  simp
