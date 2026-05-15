/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# FX Forward via Covered Interest Rate Parity

Under no-arbitrage and continuous compounding in both currencies, the
forward FX rate for delivery at time `T` is

    F(S, r_d, r_f, T) = S · exp((r_d - r_f) · T),

where `S` is the spot exchange rate (domestic per unit foreign),
`r_d` is the continuously-compounded domestic interest rate, and
`r_f` is the corresponding foreign rate.  This is the *covered
interest rate parity* relation: borrow in one currency, convert spot,
invest in the other, convert forward.  No-arbitrage forces the
forward rate to equal the differential-compounded spot.

## Main results

* `fxForward`                : `F(S, r_d, r_f, T) = S · exp((r_d - r_f)·T)`
* `fxForward_pos`            : `0 < fxForward S r_d r_f T` when `S > 0`
* `fxForward_zero_time`      : `fxForward S r_d r_f 0 = S`
* `fxForward_equal_rates`    : `r_d = r_f → fxForward = S` (no carry → forward equals spot)

## Why this lemma

Mathlib has `Real.exp_pos`, `Real.exp_zero`, `sub_self`, but no named
`fx_forward` or `interest_rate_parity` declaration.  Pythia surfaces
the covered-interest-rate-parity closed form so the `pythia` tactic
cascade can close FX-pricing goals without re-deriving them.

This complements `Pythia.Finance.forwardPrice` (which is the
dividend-paying-asset version with `r_d → r`, `r_f → q`); FX is the
same mathematical shape with two interest-rate arguments.

## References

* Hull, J. C. *Options, Futures, and Other Derivatives*, 10th ed.
  Pearson (2017), §5.10 (forward FX rates and interest-rate parity).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- Forward FX rate via covered interest rate parity:
    `F(S, r_d, r_f, T) = S · exp((r_d - r_f) · T)`. -/
noncomputable def fxForward (S r_d r_f T : ℝ) : ℝ :=
  S * Real.exp ((r_d - r_f) * T)

/-- **Positivity.** For positive spot, the FX forward rate is strictly
positive at any interest-rate differential and horizon. -/
@[stat_lemma]
theorem fxForward_pos {S : ℝ} (hS : 0 < S) (r_d r_f T : ℝ) :
    0 < fxForward S r_d r_f T := by
  unfold fxForward; exact mul_pos hS (Real.exp_pos _)

/-- **Boundary at `T = 0`.** The FX forward for immediate delivery
equals the spot rate. -/
@[stat_lemma]
theorem fxForward_zero_time (S r_d r_f : ℝ) :
    fxForward S r_d r_f 0 = S := by
  unfold fxForward; simp [mul_zero, Real.exp_zero, mul_one]

/-- **Equal-rates degeneracy.** When domestic and foreign rates are
equal, the forward FX rate equals the spot (no carry).  This is the
classical "no interest-rate differential ⟹ no forward premium /
discount" identity. -/
@[stat_lemma]
theorem fxForward_equal_rates (S r T : ℝ) :
    fxForward S r r T = S := by
  unfold fxForward; simp [sub_self, zero_mul, Real.exp_zero, mul_one]

end Pythia.Finance
