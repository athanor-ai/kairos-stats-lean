/-
examples/05_tight_tail_calculator.lean — the tail-bound calculator.

`Pythia.TightTail.report` evaluates every registered concentration
inequality at concrete parameters and reports which one is sharpest.
This is something Lean+Mathlib does not do: their tactics close
proofs of bounds, they don't help you *pick* which bound to use.

See `Pythia.Tactic.TightTail` for the formula table and the
roadmap to v2 (user-extensible registry via a `@[tail_bound]`
attribute) and v3 (sharpness-at-parameters ranking).
-/
import Pythia.Tactic.TightTail

open Pythia

/-! ### Standard regime: bounded support, sub-Gaussian σ. -/

/-- For n = 1000 samples bounded in [0, 1] with σ = 0.3, what's the
sharpest tail bound on `P(X̄ - μ > 0.05)`? -/
#eval TightTail.report (σ := 0.3) (b := 1.0) (n := 1000) (ε := 0.05)

/-- Same regime, smaller deviation: at ε = 0.01 the picture changes
because Hoeffding's b² penalty becomes more significant. -/
#eval TightTail.report (σ := 0.3) (b := 1.0) (n := 1000) (ε := 0.01)

/-! ### Sub-gamma regime: heavier tails. -/

/-- Sub-gamma with V = 2.0 and scale c = 1.0: at small ε the
sub-gamma bound is the tightest, at large ε Hoeffding wins. -/
#eval TightTail.report (b := 1.0) (V := 2.0) (c := 1.0) (n := 500) (ε := 0.1)

/-! ### Markov / Chebyshev regime: only first or second moment. -/

/-- When only μ is known, only Markov applies. -/
#eval TightTail.report (μ := 0.5) (ε := 1.0)

/-- When σ is known but the support is unbounded, Chebyshev applies
but the Hoeffding / Bernstein bounds drop out. -/
#eval TightTail.report (σ := 1.0) (n := 100) (ε := 0.5)

/-! ### Empty regime: nothing applies. -/

/-- With no parameters supplied, every bound is `none`. -/
#eval TightTail.report
