/-
Pythia.Numerical — applied numerical methods + analysis.

Pythia's numerical-methods lane: ODE existence + uniqueness, stability,
optimization first-order conditions, floating-point error analysis.
Mathlib has the underlying real-analysis machinery; this module
surfaces the named theorems applied mathematicians + engineers
quote.

## Modules

- `Pythia.Numerical.PicardLindelof`: local + global existence and
  uniqueness for ODEs with Lipschitz right-hand sides; continuous
  dependence on initial conditions.
- `Pythia.Numerical.Lyapunov`: Lyapunov stability + asymptotic
  stability + LaSalle's invariance principle for autonomous systems.
- `Pythia.Numerical.Kahan`: compensated summation correctness +
  backward-error bounds.
- `Pythia.Numerical.KKT`: Karush-Kuhn-Tucker first-order conditions;
  necessary at any local minimum under Slater's qualification +
  sufficient under convexity.

## Status

Scaffolds. Theorem signatures defined; proofs are scaffold sorries
pending Aristotle queue items 29-36. Mathlib provides the underlying
machinery (LipschitzWith, ConvexOn, deriv) but does not surface the
named theorems in applied form.
-/

import Pythia.Numerical.PicardLindelof
import Pythia.Numerical.Lyapunov
import Pythia.Numerical.Kahan
import Pythia.Numerical.KKT
