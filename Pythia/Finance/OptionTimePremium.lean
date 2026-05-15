/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option Time Premium (Extrinsic Value)

The *time premium* (also called *extrinsic value*) of a European call option
is the excess of the option price over its intrinsic value:

    timePremium(C, S, K) = C - max(S - K, 0)

where `C` is the call price, `S` is the spot price, and `K` is the strike.

The intrinsic value `max(S - K, 0)` captures the immediate exercise value
of the option. Out-of-the-money (S <= K) intrinsic value is zero; the entire
option price is time premium. In-the-money (K <= S) the intrinsic value is
`S - K` and the time premium is the residual.

## Main definitions

* `intrinsicValue S K` : `max (S - K) 0` -- immediate exercise value
* `timePremium C S K`  : `C - intrinsicValue S K` -- extrinsic value

## Main results

* `intrinsicValue_nonneg`               : `0 <= intrinsicValue S K`
* `intrinsicValue_zero_otm`             : `S <= K → intrinsicValue S K = 0`
* `intrinsicValue_itm`                  : `K <= S → intrinsicValue S K = S - K`
* `intrinsicValue_mono_spot`            : `S1 <= S2 → intrinsicValue S1 K <= intrinsicValue S2 K`
* `timePremium_nonneg_of_price_ge_intrinsic` : `intrinsicValue S K <= C → 0 <= timePremium C S K`
* `timePremium_eq_price_otm`            : `S <= K → timePremium C S K = C`

## References

* Hull, J. C. *Options, Futures, and Other Derivatives*. Pearson (2017),
  Chapter 11 (properties of stock options; intrinsic vs. time value).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- The intrinsic value of a European call option with spot `S` and strike `K`.
This is the payoff from immediate exercise: `max(S - K, 0)`. -/
def intrinsicValue (S K : ℝ) : ℝ := max (S - K) 0

/-- The time premium (extrinsic value) of a European call with price `C`,
spot `S`, and strike `K`. This is the excess of the option price over
its intrinsic value: `C - max(S - K, 0)`. -/
def timePremium (C S K : ℝ) : ℝ := C - intrinsicValue S K

/-- **Non-negativity of intrinsic value.** The intrinsic value `max(S - K, 0)`
is always non-negative, since it is the larger of `S - K` and `0`. -/
@[stat_lemma]
theorem intrinsicValue_nonneg (S K : ℝ) : 0 ≤ intrinsicValue S K := by
  unfold intrinsicValue
  exact le_max_right _ _

/-- **Out-of-the-money intrinsic is zero.** When `S <= K` (the call is
out-of-the-money or at-the-money), the intrinsic value is zero: exercise
yields a non-positive amount, so the option is not exercised. -/
@[stat_lemma]
theorem intrinsicValue_zero_otm {S K : ℝ} (h : S ≤ K) : intrinsicValue S K = 0 := by
  unfold intrinsicValue
  exact max_eq_right (sub_nonpos.mpr h)

/-- **In-the-money intrinsic value.** When `K <= S` (the call is in-the-money),
the intrinsic value equals `S - K`: immediate exercise delivers `S - K > 0`. -/
@[stat_lemma]
theorem intrinsicValue_itm {S K : ℝ} (h : K ≤ S) : intrinsicValue S K = S - K := by
  unfold intrinsicValue
  exact max_eq_left (sub_nonneg.mpr h)

/-- **Monotonicity in spot price.** If `S1 <= S2` then
`intrinsicValue S1 K <= intrinsicValue S2 K`. A higher spot price can only
increase (or preserve) the intrinsic value of a call. -/
@[stat_lemma]
theorem intrinsicValue_mono_spot {S1 S2 K : ℝ} (h : S1 ≤ S2) :
    intrinsicValue S1 K ≤ intrinsicValue S2 K := by
  unfold intrinsicValue
  exact max_le_max_right 0 (sub_le_sub_right h K)

/-- **Non-negativity of time premium.** When the option price `C` is at least
the intrinsic value, the time premium `C - intrinsicValue S K` is non-negative.
This is the standard no-arbitrage condition: a rational call price cannot be
below intrinsic value. -/
@[stat_lemma]
theorem timePremium_nonneg_of_price_ge_intrinsic {C S K : ℝ}
    (h : intrinsicValue S K ≤ C) : 0 ≤ timePremium C S K := by
  unfold timePremium
  exact sub_nonneg.mpr h

/-- **Time premium equals price out-of-the-money.** When `S <= K`, the
intrinsic value is zero, so the entire option price is time premium:
`timePremium C S K = C`. -/
@[stat_lemma]
theorem timePremium_eq_price_otm {C S K : ℝ} (h : S ≤ K) :
    timePremium C S K = C := by
  unfold timePremium
  rw [intrinsicValue_zero_otm h]
  ring

end Pythia.Finance
