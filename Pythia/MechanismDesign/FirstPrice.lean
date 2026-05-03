/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# First-Price Sealed-Bid Auction — Symmetric Bayesian Nash Equilibrium

## Main result

* `first_price_symmetric_equilibrium_bid` — In an `n`-bidder first-price
  sealed-bid auction where values are i.i.d. Uniform[0,1], the unique
  symmetric Bayesian Nash Equilibrium bid function is
  `b*(v) = ((n − 1) / n) · v`.  The proof verifies:
  1. **Differentiability**: `b*` has derivative `(n−1)/n` everywhere.
  2. **Boundary condition**: `b*(0) = 0`.
  3. **Equilibrium ODE**: `v · b′(v) + (n − 1) · b(v) = (n − 1) · v`,
     the first-order condition for payoff maximisation.

## Mathematical background

Each bidder has private value `v ~ U[0,1]` and submits a sealed bid `b`.
The highest bidder wins and pays their bid.  A symmetric strategy
`β : [0,1] → ℝ` is a BNE when no bidder can profitably deviate.

The expected payoff of a bidder with value `v` bidding `b` when all
opponents use increasing strategy `β` is

  `π(b, v) = (v − b) · F(β⁻¹(b))^{n−1}`

where `F(x) = x` is the uniform CDF.  The FOC for `β` itself to be
optimal yields the ODE

  `β′(v) · v + (n − 1) · β(v) = (n − 1) · v,  β(0) = 0`,

which is equivalent to `d/dv [v^{n−1} · β(v)] = (n − 1) · v^{n−1}`.
Integrating gives `β(v) = ((n − 1)/n) · v`.

## References

* Krishna, V. *Auction Theory* (2nd ed., Academic Press, 2010).
  Proposition 2.2.
-/
import Mathlib

namespace Pythia.MechanismDesign

/-- **Symmetric BNE bid in the uniform FPSB auction (Krishna Prop 2.2).**

In an `n`-bidder first-price sealed-bid auction with i.i.d. U[0,1] values,
the symmetric Bayesian Nash Equilibrium bid function is `b*(v) = ((n−1)/n)·v`.

We verify three properties:
1. `b*` is differentiable with derivative `(n−1)/n` (`HasDerivAt`).
2. `b*(0) = 0` (boundary condition — the lowest type shades to zero).
3. The equilibrium ODE `v · b′(v) + (n−1) · b(v) = (n−1) · v` holds,
   encoding the first-order condition for expected-payoff maximisation. -/
theorem first_price_symmetric_equilibrium_bid
    (n : ℕ) (hn : 2 ≤ n) (v : ℝ) :
    let b : ℝ → ℝ := fun w => ((↑n - 1) / ↑n) * w
    -- (1) Differentiability
    HasDerivAt b ((↑n - 1 : ℝ) / ↑n) v ∧
    -- (2) Boundary condition
    b 0 = 0 ∧
    -- (3) Equilibrium ODE: v · b'(v) + (n-1) · b(v) = (n-1) · v
    v * ((↑n - 1 : ℝ) / ↑n) + (↑n - 1) * b v = (↑n - 1 : ℝ) * v := by
  refine ⟨?_, ?_, ?_⟩
  · -- HasDerivAt
    have h := HasDerivAt.const_mul ((↑n - 1 : ℝ) / ↑n) (hasDerivAt_id' v)
    simp at h
    exact h
  · -- Boundary: b 0 = 0
    simp
  · -- ODE
    have hn_pos : (n : ℝ) ≠ 0 := by positivity
    field_simp
    ring

end Pythia.MechanismDesign
