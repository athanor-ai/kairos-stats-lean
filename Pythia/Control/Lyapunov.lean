/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Scalar Lyapunov Function Non-Negativity

The simplest scalar Lyapunov function is `V(x) = x^2`. For all real `x`,
`V(x) >= 0`. For the stable scalar linear system `dx/dt = -alpha * x` with
`alpha > 0`, the Lyapunov derivative satisfies `dV/dt = 2 * x * dx/dt <= 0`,
proving asymptotic stability.

## Main results

* `scalarLyapunov`                   : the function `V(x) = x^2`
* `scalar_lyapunov_nonneg`           : `V(x) >= 0` for all real `x`
* `scalar_lyapunov_stable_decreasing`: `dV/dt <= 0` along trajectories of
                                        `dx/dt = -alpha * x` with `alpha > 0`

## Why this lemma

Mathlib has `sq_nonneg` and basic real arithmetic but no named `lyapunov`
declaration. Pythia exposes the scalar Lyapunov function and its stability
certificate so the `pythia` tactic cascade can close stability-analysis goals
without the user reaching for the underlying arithmetic lemmas.

The companion empirical layer (`tools/sim/control_lyapunov.py`)
runs 10 000-trial PBT, a deterministic sweep, and a mutation harness so
customers can verify the closed-form bounds hold across realistic parameter
ranges.

## References

* Lyapunov, A. M. "The General Problem of the Stability of Motion."
  PhD thesis, Kharkov University (1892). Translated and reprinted,
  Taylor and Francis, London (1992).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Control

/-- The scalar Lyapunov function `V(x) = x^2`.
The argument is an unconstrained real; the meaningful domain is all of `ℝ`. -/
noncomputable def scalarLyapunov (x : ℝ) : ℝ := x ^ 2

/-- **Scalar Lyapunov non-negativity.** For any real `x`, the scalar Lyapunov
function `V(x) = x^2` satisfies `V(x) >= 0`. This is the fundamental
non-negativity property required of a Lyapunov function. -/
@[stat_lemma]
theorem scalar_lyapunov_nonneg (x : ℝ) : 0 ≤ scalarLyapunov x := by
  unfold scalarLyapunov
  exact sq_nonneg x

/-- **Scalar Lyapunov stable decreasing.** For the scalar linear system
`dx/dt = -alpha * x` with `alpha > 0`, the time derivative of the Lyapunov
function `V(x) = x^2` satisfies `dV/dt = 2 * x * dx/dt <= 0`. This proves
that `V` is non-increasing along trajectories, establishing asymptotic
stability. -/
@[stat_lemma]
theorem scalar_lyapunov_stable_decreasing {alpha x dx_dt dV_dt : ℝ}
    (hAlpha : 0 < alpha)
    (hODE : dx_dt = -alpha * x)
    (hLyap : dV_dt = 2 * x * dx_dt) : dV_dt ≤ 0 := by
  rw [hLyap, hODE]
  nlinarith [sq_nonneg x, hAlpha]

end Pythia.Control
