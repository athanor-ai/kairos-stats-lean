/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hooke's Law Spring Potential Energy Non-Negativity

The potential energy stored in a Hookean spring is defined as
`U(x) = (1/2) * k * x^2`, where `k` is the spring constant in N/m and
`x` is the displacement from equilibrium in meters. When `k >= 0`, the
stored energy is always non-negative.

## Main results

* `hookePE`           : the spring potential energy function `(1/2) * k * x^2`
* `hooke_pe_nonneg`   : `U >= 0` when `k >= 0`

## Why this lemma

Mathlib has `sq_nonneg` and real arithmetic but no named `hooke` or
`spring_pe` declaration. Pythia exposes the Hookean spring potential
energy and its non-negativity so the `pythia` tactic cascade can close
energy-conservation and stability goals without the user reaching for the
underlying arithmetic lemmas.

The companion empirical layer (`tools/sim/mechanical_hooke_spring.py`)
runs a 10 000-trial PBT, a deterministic sweep, and a mutation harness
so customers can verify the closed-form bound holds across realistic
spring constants (0 N/m to 1 MN/m) and displacement (-10 m to 10 m)
parameter ranges.

## References

* Hooke, R. "De Potentia Restitutiva, or of Spring, Explaining the Power
  of Springing Bodies." London: John Martyn (1678). ("Lectures on Spring")
* Goldstein, H., Poole, C., and Safko, J. "Classical Mechanics," 3rd ed.
  Addison-Wesley (2002), Section 2.2: Variational Principles and the
  Lagrange Equations.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Mechanical

/-- The Hookean spring potential energy `U = (1/2) * k * x^2`.
The arguments are unconstrained reals; the meaningful domain is
`k >= 0` (spring constant in N/m) and `x` any displacement in meters. -/
noncomputable def hookePE (k x : ℝ) : ℝ := (1/2) * k * x^2

/-- **Hooke's law spring potential energy non-negativity.** For any
non-negative spring constant `k` and any displacement `x`, the potential
energy `U = (1/2) * k * x^2` is non-negative. This is the fundamental
property that ensures a Hookean spring stores, rather than releases,
energy upon deformation. -/
@[stat_lemma]
theorem hooke_pe_nonneg {k : ℝ} (hk : 0 ≤ k) (x : ℝ) : 0 ≤ hookePE k x := by
  unfold hookePE
  have h2 : (0 : ℝ) ≤ 1/2 := by norm_num
  have hx2 : 0 ≤ x^2 := sq_nonneg x
  positivity

end Pythia.Mechanical
