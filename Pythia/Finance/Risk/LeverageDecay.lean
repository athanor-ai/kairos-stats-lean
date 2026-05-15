/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Leverage Decay (Volatility Drag in Daily-Rebalanced Leveraged ETFs)

A daily-rebalanced leveraged ETF with leverage ratio `L` targets a
daily return of `L · r` when the underlying moves by `r`.  Over two
periods with underlying returns `r₁` and `r₂`, the compounded ETF
gross return is

    (1 + L·r₁)(1 + L·r₂),

while the underlying two-period compounded gross return is

    1 + L·(r₁ + r₂ + r₁·r₂).

The gap between these two quantities is the *volatility drag* (also
called *leverage decay*):

    compoundTwoPeriod (L·r₁) (L·r₂) − L · compoundTwoPeriod r₁ r₂
      = L·(L−1)·r₁·r₂.

When `L ≥ 1` and both-period returns are same-sign (`r₁·r₂ ≥ 0`),
this drag is non-negative: the ETF *under-performs* the leveraged
buy-and-hold.  Higher leverage amplifies the drag monotonically.

The key identity `leverageDrag_identity` is a pure ring computation;
the sign and monotonicity results require `mul_nonneg` chains and
`nlinarith` for the product-of-linear-factors argument.

## Main results

* `leveragedReturn`               : `L · r` — single-period ETF return
* `compoundTwoPeriod`             : `(1 + r₁)(1 + r₂) − 1` — discrete two-period compounding
* `leverageDrag`                  : `L·(L−1)·r₁·r₂` — the volatility drag term
* `leveragedReturn_zero`          : `leveragedReturn L 0 = 0`
* `compoundTwoPeriod_comm`        : commutativity of two-period compounding
* `leverageDrag_identity`         : the fundamental drag decomposition identity
* `leverageDrag_nonneg_of_same_sign`: drag is non-negative for `L ≥ 1`, same-sign returns
* `leverageDrag_zero_at_unit_leverage`: unit leverage implies zero drag
* `leverageDrag_abs_mono_L`       : higher leverage amplifies drag when returns are same-sign

## Why this lemma

Daily-rebalanced leveraged ETFs (e.g. ProShares UPRO 3×, SQQQ −3×)
are widely held by quantitative practitioners as hedging and
short-term directional instruments.  Their long-horizon return
decomposition is a textbook source of confusion: the product of
daily compounded leveraged returns is *not* the leveraged product of
the underlying's compounded return.  The drag term `L·(L−1)·r₁·r₂`
is the precise algebraic statement of this gap.  Surfacing the
closed-form identity in Pythia gives the `pythia` tactic cascade a
clean closure target for leveraged-product return-attribution goals.

## References

* Cheng, M. and Madhavan, A. "The Dynamics of Leveraged and Inverse ETFs."
  *Journal of Investment Management* 7(4): 43-62 (2009).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Single-period leveraged ETF return: `leveragedReturn L r = L · r`. -/
def leveragedReturn (L r : ℝ) : ℝ := L * r

/-- Two-period discrete compounding: `(1 + r₁)(1 + r₂) − 1`. -/
def compoundTwoPeriod (r₁ r₂ : ℝ) : ℝ := (1 + r₁) * (1 + r₂) - 1

/-- Volatility drag (leverage decay) term: `L·(L−1)·r₁·r₂`. -/
def leverageDrag (L r₁ r₂ : ℝ) : ℝ := L * (L - 1) * r₁ * r₂

/-- **Zero return.** A zero underlying return produces a zero leveraged
return, regardless of leverage ratio. -/
@[stat_lemma]
theorem leveragedReturn_zero (L : ℝ) : leveragedReturn L 0 = 0 := by
  unfold leveragedReturn; simp

/-- **Commutativity of two-period compounding.** The order of the two
period returns does not affect the compounded result. -/
@[stat_lemma]
theorem compoundTwoPeriod_comm (r₁ r₂ : ℝ) :
    compoundTwoPeriod r₁ r₂ = compoundTwoPeriod r₂ r₁ := by
  unfold compoundTwoPeriod; ring

/-- **Fundamental leverage-decay identity.** The gap between compounding
the leveraged per-period returns and applying leverage to the
compounded underlying return equals `L·(L−1)·r₁·r₂`:

    compoundTwoPeriod (L·r₁) (L·r₂) − L · compoundTwoPeriod r₁ r₂
      = leverageDrag L r₁ r₂.

This is the algebraic kernel of volatility drag: the `L²·r₁·r₂` term
from the compounded ETF path minus the `L·r₁·r₂` cross term from the
leveraged underlying return leaves exactly `L·(L−1)·r₁·r₂`. -/
@[stat_lemma]
theorem leverageDrag_identity (L r₁ r₂ : ℝ) :
    compoundTwoPeriod (leveragedReturn L r₁) (leveragedReturn L r₂) -
      leveragedReturn L (compoundTwoPeriod r₁ r₂) =
    leverageDrag L r₁ r₂ := by
  unfold compoundTwoPeriod leveragedReturn leverageDrag; ring

/-- **Non-negativity of drag for same-sign returns.** When the leverage
ratio satisfies `L ≥ 1` and both-period returns are same-sign
(`r₁ · r₂ ≥ 0`), the volatility drag is non-negative:

    0 ≤ leverageDrag L r₁ r₂.

The leveraged ETF under-performs the leveraged buy-and-hold in
expectation whenever the underlying oscillates (same-sign-returns
period is the best case; opposite-sign periods flip the sign and make
the drag negative, i.e. the ETF over-compounds on reversals). -/
@[stat_lemma]
theorem leverageDrag_nonneg_of_same_sign {L r₁ r₂ : ℝ}
    (hL : 1 ≤ L) (hrr : 0 ≤ r₁ * r₂) :
    0 ≤ leverageDrag L r₁ r₂ := by
  unfold leverageDrag
  have hL0 : 0 ≤ L := by linarith
  have hLm1 : 0 ≤ L - 1 := by linarith
  have hLL : 0 ≤ L * (L - 1) := mul_nonneg hL0 hLm1
  -- leverageDrag unfolds to ((L * (L - 1)) * r₁) * r₂ (left-assoc).
  -- Rearrange to L*(L-1) * (r₁*r₂), both non-negative.
  have : L * (L - 1) * r₁ * r₂ = L * (L - 1) * (r₁ * r₂) := by ring
  linarith [mul_nonneg hLL hrr]

/-- **Unit leverage implies zero drag.** At `L = 1` the ETF replicates
the underlying exactly and the drag term vanishes. -/
@[stat_lemma]
theorem leverageDrag_zero_at_unit_leverage (r₁ r₂ : ℝ) :
    leverageDrag 1 r₁ r₂ = 0 := by
  unfold leverageDrag; ring

/-- **Monotone amplification of drag by leverage.** For `1 ≤ L₁ ≤ L₂`
and same-sign returns (`0 ≤ r₁ · r₂`), a higher leverage ratio
produces weakly larger volatility drag:

    leverageDrag L₁ r₁ r₂ ≤ leverageDrag L₂ r₁ r₂.

The drag factor `L·(L−1)` is increasing in `L` for `L ≥ 1` (it
equals `L² − L`, a convex quadratic on `[1, ∞)`), so higher leverage
strictly amplifies the path-dependence cost for non-trivial same-sign
return pairs. -/
@[stat_lemma]
theorem leverageDrag_abs_mono_L {L₁ L₂ : ℝ}
    (hL₁ : 1 ≤ L₁) (hL : L₁ ≤ L₂) {r₁ r₂ : ℝ} (hrr : 0 ≤ r₁ * r₂) :
    leverageDrag L₁ r₁ r₂ ≤ leverageDrag L₂ r₁ r₂ := by
  unfold leverageDrag
  -- Goal: L₁ * (L₁ - 1) * r₁ * r₂ ≤ L₂ * (L₂ - 1) * r₁ * r₂.
  -- Key factoring: L₂*(L₂-1) - L₁*(L₁-1) = (L₂-L₁)*(L₁+L₂-1) ≥ 0,
  -- since L₂-L₁ ≥ 0 and L₁+L₂-1 ≥ 1 (from 1 ≤ L₁ ≤ L₂).
  -- Then multiply by r₁*r₂ ≥ 0.
  have hdiff : 0 ≤ (L₂ - L₁) * (L₁ + L₂ - 1) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [mul_nonneg hdiff hrr]

end Pythia.Finance
