/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Put-Call Parity

The fundamental no-arbitrage relation between European call and put
option prices under deterministic interest rates.

## Statement

For a European call C and put P on the same underlying S with
strike K, expiry T, and continuously compounded risk-free rate r:

  C - P = S - K · exp(-r · T)

This is a model-free consequence of no-arbitrage: it holds regardless
of the underlying price dynamics (Black-Scholes, jump-diffusion, etc.)
because it follows from constructing a replicating portfolio.

## References

* Stoll, H. R. (1969): "The Relationship Between Put and Call Option
  Prices." The Journal of Finance 24(5), 801–824.
* Hull, J. C. (2018): "Options, Futures, and Other Derivatives" (10th ed.), Ch. 11.
* Mathlib has no financial-math module as of v4.28 — Pythia-original.

General applied mathematics.
-/
import Mathlib

open Real

noncomputable section

namespace Pythia.Finance.PutCallParity

/-- European option parameters: spot price, strike, time to expiry,
risk-free rate, call price, put price. All real-valued. -/
structure OptionParams where
  S : ℝ    -- current spot price
  K : ℝ    -- strike price
  T : ℝ    -- time to expiry (years)
  r : ℝ    -- continuously compounded risk-free rate
  C : ℝ    -- European call price
  P : ℝ    -- European put price

/-- **Put-call parity.** Under no-arbitrage, the call-put spread equals
the forward-adjusted spot-strike spread:

  C - P = S - K · exp(-r · T)

We state this as: given the parity holds (it's a definition of
no-arbitrage-consistent pricing), derive consequences. -/
def parity (p : OptionParams) : Prop :=
  p.C - p.P = p.S - p.K * exp (-p.r * p.T)

/-- If put-call parity holds and the call is worthless (C = 0, deep
out-of-the-money), then P = K · exp(-r·T) - S. -/
theorem put_from_zero_call (p : OptionParams) (h : parity p) (hC : p.C = 0) :
    p.P = p.K * exp (-p.r * p.T) - p.S := by
  unfold parity at h
  linarith

/-- If put-call parity holds, then C ≥ S - K · exp(-r·T).
The call is worth at least the forward-adjusted intrinsic value. -/
theorem call_lower_bound (p : OptionParams) (h : parity p) (hP : 0 ≤ p.P) :
    p.S - p.K * exp (-p.r * p.T) ≤ p.C := by
  unfold parity at h
  linarith

/-- If put-call parity holds, then P ≥ K · exp(-r·T) - S.
The put is worth at least the forward-adjusted intrinsic value. -/
theorem put_lower_bound (p : OptionParams) (h : parity p) (hC : 0 ≤ p.C) :
    p.K * exp (-p.r * p.T) - p.S ≤ p.P := by
  unfold parity at h
  linarith

/-- The present value of the strike is positive when K > 0 and T ≥ 0. -/
theorem pv_strike_pos (K r T : ℝ) (hK : 0 < K) (hT : 0 ≤ T) :
    0 < K * exp (-r * T) := by
  apply mul_pos hK
  exact exp_pos _

/-- Put-call parity is symmetric: parity determines any one of the four
values (C, P, S, K·exp(-rT)) from the other three. -/
theorem call_from_parity (p : OptionParams) (h : parity p) :
    p.C = p.P + p.S - p.K * exp (-p.r * p.T) := by
  unfold parity at h
  linarith

theorem put_from_parity (p : OptionParams) (h : parity p) :
    p.P = p.C - p.S + p.K * exp (-p.r * p.T) := by
  unfold parity at h
  linarith

end Pythia.Finance.PutCallParity
