/-
Pythia starter pack — control theory / Lyapunov stability.

Foundation of stability analysis for dynamical systems: a Lyapunov
function `V(x) ≥ 0` whose time derivative is non-positive certifies
the equilibrium is stable. Pythia ships the scalar variant as a
@[stat_lemma]; the full ODE form lives in `Pythia.Control.LyapunovODE`.

Run via:
    lake env lean examples/control/01_lyapunov_stability.lean
-/
import Pythia.Control.Lyapunov
import Pythia.Tactic.PythiaBang

open Pythia

/-! ## Scalar Lyapunov function is non-negative

The scalar Lyapunov candidate `V(x) = x²` is non-negative everywhere;
this is the structural prerequisite for the stability theorem. -/
example (x : ℝ) : 0 ≤ scalarLyapunov x := scalar_lyapunov_nonneg x

/-! ## Stable-decreasing condition

For a dissipative system `dx/dt = -α · x` with `α > 0`, the time
derivative of `V(x) = x²` along trajectories satisfies
`dV/dt ≤ 0`, so V is a Lyapunov function and the origin is stable. -/
example (alpha x dx_dt dV_dt : ℝ) (hα : 0 < alpha)
    (h_dx : dx_dt = -alpha * x)
    (h_dV : dV_dt = 2 * x * dx_dt) :
    dV_dt ≤ 0 :=
  scalar_lyapunov_stable_decreasing hα h_dx h_dV
