/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Impermanent Loss in a Constant-Product AMM

For a Uniswap-v2-style constant-product automated market maker
(`x · y = k` invariant), a liquidity provider deposits asset
amounts `(x₀, y₀)` at price ratio `p₀ = y₀ / x₀`.  When the price
ratio shifts to `p` (here we work in units of `p / p₀`), the LP
position can be re-priced.  The *impermanent loss* (IL) is the
relative gap between the LP value and a held-position value (HODL)
with the same initial deposit.

The closed form in price-ratio units is

    IL(r) = (2 · √r) / (1 + r) - 1,

where `r = p / p₀` is the relative-price-change factor.  IL is
non-positive (the LP under-performs HODL on any price move) with
equality at `r = 1` (no price change).

## Main results

* `impermanentLoss`              : `(2·√r) / (1+r) - 1`
* `impermanentLoss_at_one`       : `IL(1) = 0` (no price change → no loss)
* `impermanentLoss_nonpos`       : `IL(r) ≤ 0` for `r > 0`
  (LP weakly under-performs HODL on any price move)

## Why this lemma

Decentralised exchanges (Uniswap, Curve, Balancer) are the largest
on-chain liquidity venue.  LP returns are dominated by *fees minus
impermanent loss*; modelling IL correctly is a prerequisite to any
LP optimisation strategy.  Surfacing the closed form in Pythia gives
the `pythia` tactic cascade a clean closure target for AMM-LP
analytics.

## References

* Adams, H., Zinsmeister, N., Salem, M., Keefer, R., and Robinson, D.
  "Uniswap v3 Core" (2021).
* Angeris, G. and Chitra, T. "Improved Price Oracles: Constant Function
  Market Makers." *Proceedings of AFT '20*.
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- Impermanent loss for a constant-product AMM at relative-price ratio
`r = p / p₀`: `IL(r) = (2·√r) / (1+r) - 1`. -/
noncomputable def impermanentLoss (r : ℝ) : ℝ :=
  (2 * Real.sqrt r) / (1 + r) - 1

/-- **Boundary at `r = 1`.** At no price change the impermanent loss is
zero: LP and HODL match. -/
@[stat_lemma]
theorem impermanentLoss_at_one : impermanentLoss 1 = 0 := by
  unfold impermanentLoss; simp [Real.sqrt_one]; norm_num

/-- **Impermanent loss is non-positive for any positive price ratio.**

For `r > 0`, the LP value satisfies
`(2·√r) / (1+r) ≤ 1`, equivalently `2·√r ≤ 1 + r`, equivalently
`0 ≤ (√r - 1)²` — the algebraic kernel of the IL bound.

The bound is sharp at `r = 1` (LP and HODL coincide). -/
@[stat_lemma]
theorem impermanentLoss_nonpos {r : ℝ} (hr : 0 < r) :
    impermanentLoss r ≤ 0 := by
  unfold impermanentLoss
  have hsqr : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hr_pos : 0 < 1 + r := by linarith
  have hsq_r : (Real.sqrt r)^2 = r := Real.sq_sqrt hr.le
  rw [sub_nonpos, div_le_one hr_pos]
  nlinarith [sq_nonneg (Real.sqrt r - 1)]

end Pythia.Finance
