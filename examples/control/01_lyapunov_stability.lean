/-
Pythia starter pack: control theory / Lyapunov stability.

Foundation of stability analysis for dynamical systems: a Lyapunov
function `V(x) ≥ 0` whose time derivative is non-positive certifies
the equilibrium is stable. Pythia ships the scalar variant as
`@[stat_lemma]`; the full ODE form lives in `Pythia.Control.LyapunovODE`.

Run via:
    lake env lean examples/control/01_lyapunov_stability.lean
-/
import Pythia.Control.Lyapunov
import Pythia.Tactic.PythiaBang

open Pythia.Control

/-! ## Scalar Lyapunov function is non-negative

The scalar Lyapunov candidate `V(x) = x²`, exposed in pythia as
`scalarLyapunov x`, is non-negative everywhere. The structural
prerequisite for the stability theorem. The cascade closes this
via `positivity` (rung 3) without needing the named theorem. -/
example (x : ℝ) : 0 ≤ scalarLyapunov x := by
  pythia!

/-! ## Stable-decreasing condition

For a dissipative system `dx/dt = -α · x` with `α > 0`, the time
derivative of `V(x) = x²` along trajectories satisfies `dV/dt ≤ 0`,
so V is a Lyapunov function and the origin is stable.

The cascade does not close this on its own: the goal `dV_dt ≤ 0`
is too generic for aesop to filter on, and the hypothesis chain
needs `nlinarith [sq_nonneg x]` rather than plain linarith.
The named theorem packages the substitution + nlinarith hint. -/
example {alpha x dx_dt dV_dt : ℝ}
    (hAlpha : 0 < alpha)
    (hODE : dx_dt = -alpha * x)
    (hLyap : dV_dt = 2 * x * dx_dt) :
    dV_dt ≤ 0 :=
  scalar_lyapunov_stable_decreasing hAlpha hODE hLyap
