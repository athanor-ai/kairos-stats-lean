/-
Pythia starter pack: optimal transport / Wasserstein distance.

The L1 Wasserstein-style cost between two discrete probability mass
functions `p, q : Fin n → ℝ` is non-negative. The discrete case
lifts directly via `Finset.sum_nonneg`; the named theorem
`wasserstein_distance_nonneg` is tagged `@[stat_lemma]` so the
headline `pythia!` tactic closes it via the cascade.

Run via:
    lake env lean examples/optimal_transport/01_wasserstein_nonneg.lean
-/
import Pythia.OptimalTransport.WassersteinDistanceNonneg
import Pythia.Tactic.PythiaBang

open Pythia.OptimalTransport

/-! ## Discrete Wasserstein non-negativity

For probability mass functions `p, q : Fin n → ℝ`, the discrete
Wasserstein-style cost `Σᵢ |pᵢ - qᵢ|` is non-negative. The basic
axiom of any metric on the simplex; concrete value matters
downstream when bounding `W₁` against KL or TV. -/
example {n : ℕ} (p q : Fin n → ℝ) :
    0 ≤ ∑ i, |p i - q i| := by
  pythia!

-- Equivalently, the named theorem applies directly without the
-- cascade:
example {n : ℕ} (p q : Fin n → ℝ) :
    0 ≤ ∑ i, |p i - q i| :=
  wasserstein_distance_nonneg p q

/-! ## Compositional sanity

Two distributions that agree pointwise have zero Wasserstein cost. -/
example {n : ℕ} (p : Fin n → ℝ) :
    ∑ i, |p i - p i| = 0 := by
  simp
