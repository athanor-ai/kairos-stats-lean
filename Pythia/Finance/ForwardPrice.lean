/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Forward Price for a Dividend-Paying Asset

Under no-arbitrage and continuous compounding, the forward price at
time 0 of a dividend-paying asset with current spot `S`, risk-free
rate `r`, continuous dividend yield `q`, and time to delivery `T` is

    F(S, r, q, T) = S · exp((r - q) · T).

The replication argument: short `e^{-qT}` units of the asset (the
dividend yield rebuilds the position to one unit at delivery) and
invest the proceeds at the risk-free rate.  No-arbitrage forces the
forward price to equal the future value of the dividend-adjusted
spot.

## Main results

* `forwardPrice`                : closed-form forward price `S · exp((r-q)·T)`
* `forwardPrice_pos`            : `0 < forwardPrice S r q T` when `S > 0`
* `forwardPrice_zero_time`      : `forwardPrice S r q 0 = S`
* `forwardPrice_zero_dividend`  : with `q = 0`, reduces to `S · exp(r·T)`

## Why this lemma

Mathlib has `Real.exp_pos` and `Real.exp_zero` but no named
`forward_price` declaration. Pythia exposes the closed-form forward
price and its boundary properties so the `pythia` tactic cascade can
close FX-forward / futures-pricing goals without the user reaching
for the underlying real-analysis lemmas.

## References

* Hull, J. C. *Options, Futures, and Other Derivatives*, 10th ed.
  Pearson (2017), §5.5 (forward price for an investment asset paying
  a known dividend yield).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- Forward price for a dividend-paying asset under continuous
compounding: `F(S, r, q, T) = S · exp((r - q) · T)`. -/
noncomputable def forwardPrice (S r q T : ℝ) : ℝ :=
  S * Real.exp ((r - q) * T)

/-- **Positivity.** For positive spot price, the forward price is
strictly positive at any rate / dividend yield / time horizon. -/
@[stat_lemma]
theorem forwardPrice_pos {S : ℝ} (hS : 0 < S) (r q T : ℝ) :
    0 < forwardPrice S r q T := by
  unfold forwardPrice; exact mul_pos hS (Real.exp_pos _)

/-- **Boundary at `T = 0`.** The forward price for immediate delivery
equals the spot price: `forwardPrice S r q 0 = S`. -/
@[stat_lemma]
theorem forwardPrice_zero_time (S r q : ℝ) :
    forwardPrice S r q 0 = S := by
  unfold forwardPrice; simp [mul_zero, Real.exp_zero]

/-- **No-dividend specialisation.** With zero dividend yield `q = 0`,
the forward price reduces to `S · exp(r · T)`. -/
@[stat_lemma]
theorem forwardPrice_zero_dividend (S r T : ℝ) :
    forwardPrice S r 0 T = S * Real.exp (r * T) := by
  unfold forwardPrice; simp [sub_zero]

end Pythia.Finance
