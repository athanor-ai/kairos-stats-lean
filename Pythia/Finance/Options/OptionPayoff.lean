/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pythia.Finance.OptionPayoff: European Option Payoff Functions

This module formalizes the payoff functions for European call and put options
at the expiry date. The payoffs are determined solely by the terminal spot
price `S` and the strike price `K`, with no discounting.

## Definitions

* `expiryCallPayoff S K` : `max (S - K) 0` -- call payoff at expiry
* `expiryPutPayoff S K`  : `max (K - S) 0` -- put payoff at expiry

## Main results

* `expiryCallPayoff_nonneg`    : `0 ≤ expiryCallPayoff S K`
* `expiryPutPayoff_nonneg`     : `0 ≤ expiryPutPayoff S K`
* `expiryCallPayoff_itm`       : `K ≤ S → expiryCallPayoff S K = S - K`
* `expiryCallPayoff_otm`       : `S ≤ K → expiryCallPayoff S K = 0`
* `expiryPutPayoff_itm`        : `S ≤ K → expiryPutPayoff S K = K - S`
* `expiryPutPayoff_otm`        : `K ≤ S → expiryPutPayoff S K = 0`
* `payoff_parity`        : `expiryCallPayoff S K - expiryPutPayoff S K = S - K`
* `expiryCallPayoff_mono_spot` : `S1 ≤ S2 → expiryCallPayoff S1 K ≤ expiryCallPayoff S2 K`

The identity `payoff_parity` is the algebraic kernel of put-call parity: at
expiry, a long call combined with a short put replicates a forward contract with
strike `K`.

## References

* Cox, J. C. and Rubinstein, M. "Options Markets." Prentice-Hall (1985).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- The European call option payoff at expiry: `max(S - K, 0)`.

For spot price `S` and strike `K`, the holder exercises only when `S > K`,
receiving the in-the-money amount `S - K`. Out-of-the-money or at-the-money,
the payoff is zero (the option expires worthless). -/
def expiryCallPayoff (S K : ℝ) : ℝ := max (S - K) 0

/-- The European put option payoff at expiry: `max(K - S, 0)`.

For spot price `S` and strike `K`, the holder exercises only when `K > S`,
receiving the in-the-money amount `K - S`. Out-of-the-money or at-the-money,
the payoff is zero. -/
def expiryPutPayoff (S K : ℝ) : ℝ := max (K - S) 0

/-- **Non-negativity of call payoff.**

`max(S - K, 0)` is always at least zero: option payoffs are bounded below
by zero due to the holder's right (not obligation) to exercise. -/
@[stat_lemma]
theorem expiryCallPayoff_nonneg (S K : ℝ) : 0 ≤ expiryCallPayoff S K := by
  unfold expiryCallPayoff
  exact le_max_right _ _

/-- **Non-negativity of put payoff.**

`max(K - S, 0)` is always at least zero, by the same limited-liability
argument as `expiryCallPayoff_nonneg`. -/
@[stat_lemma]
theorem expiryPutPayoff_nonneg (S K : ℝ) : 0 ≤ expiryPutPayoff S K := by
  unfold expiryPutPayoff
  exact le_max_right _ _

/-- **In-the-money call payoff.**

When `K ≤ S`, the call is in-the-money and the payoff equals the intrinsic
value `S - K`. -/
@[stat_lemma]
theorem expiryCallPayoff_itm {S K : ℝ} (h : K ≤ S) : expiryCallPayoff S K = S - K := by
  unfold expiryCallPayoff
  exact max_eq_left (sub_nonneg.mpr h)

/-- **Out-of-the-money call payoff.**

When `S ≤ K`, the call is out-of-the-money (or at-the-money) and the payoff
is zero: exercise yields a non-positive amount so the holder does not exercise. -/
@[stat_lemma]
theorem expiryCallPayoff_otm {S K : ℝ} (h : S ≤ K) : expiryCallPayoff S K = 0 := by
  unfold expiryCallPayoff
  exact max_eq_right (sub_nonpos.mpr h)

/-- **In-the-money put payoff.**

When `S ≤ K`, the put is in-the-money and the payoff equals the intrinsic
value `K - S`. -/
@[stat_lemma]
theorem expiryPutPayoff_itm {S K : ℝ} (h : S ≤ K) : expiryPutPayoff S K = K - S := by
  unfold expiryPutPayoff
  exact max_eq_left (sub_nonneg.mpr h)

/-- **Out-of-the-money put payoff.**

When `K ≤ S`, the put is out-of-the-money (or at-the-money) and the payoff
is zero. -/
@[stat_lemma]
theorem expiryPutPayoff_otm {S K : ℝ} (h : K ≤ S) : expiryPutPayoff S K = 0 := by
  unfold expiryPutPayoff
  exact max_eq_right (sub_nonpos.mpr h)

/-- **Put-call parity at the payoff level.**

For all real `S` and `K`:

    expiryCallPayoff S K - expiryPutPayoff S K = S - K.

This is the algebraic kernel of put-call parity: at expiry, a portfolio that
is long one call and short one put replicates a forward contract with delivery
price `K`. The identity holds unconditionally (for any `S`, `K`), with no
assumption on the sign of `S - K`.

*Proof.* Split on `S ≤ K` vs `K ≤ S`. In each branch exactly one of the two
payoffs is in-the-money and the other is zero; the ITM and OTM lemmas reduce
the goal to a trivial linear identity closed by `linarith`. -/
@[stat_lemma]
theorem payoff_parity (S K : ℝ) : expiryCallPayoff S K - expiryPutPayoff S K = S - K := by
  rcases le_or_gt S K with h | h
  · -- S ≤ K: call is OTM (= 0), put is ITM (= K - S)
    rw [expiryCallPayoff_otm h, expiryPutPayoff_itm h]
    linarith
  · -- K < S: call is ITM (= S - K), put is OTM (= 0)
    have hle : K ≤ S := le_of_lt h
    rw [expiryCallPayoff_itm hle, expiryPutPayoff_otm hle]
    linarith

/-- **Monotonicity of call payoff in the spot price.**

If `S1 ≤ S2` then `expiryCallPayoff S1 K ≤ expiryCallPayoff S2 K`. A higher terminal
spot price can only increase (or preserve) the call payoff: the holder benefits
from a higher spot price and can never be worse off.

*Proof.* Both payoffs are `max(· - K, 0)`; apply `max_le_max_right` with the
fact that `S1 - K ≤ S2 - K` follows from `S1 ≤ S2` by `sub_le_sub_right`. -/
@[stat_lemma]
theorem expiryCallPayoff_mono_spot {S1 S2 K : ℝ} (h : S1 ≤ S2) :
    expiryCallPayoff S1 K ≤ expiryCallPayoff S2 K := by
  unfold expiryCallPayoff
  exact max_le_max_right 0 (sub_le_sub_right h K)

end Pythia.Finance
