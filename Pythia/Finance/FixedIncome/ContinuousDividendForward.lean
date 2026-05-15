/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Continuous-Dividend Forward Price

For an asset paying a *continuous* dividend yield `q` (the cash-flow-
producing asset model — equity indices, FX, commodities with
convenience yield), the no-arbitrage forward price is

    F = S · exp((r − q) · T).

The structure generalises the zero-dividend forward
`Pythia.Finance.forwardPrice` (with `q = 0` reducing to the
standard `S · exp(r·T)`) and the FX forward
`Pythia.Finance.fxForward` (the cost-of-carry analogue with the
foreign rate playing the role of `q`).

## Main results

* `continuousDividendForward`             : `S · exp((r − q) · T)`
* `continuousDividendForward_zero_q`      : `q = 0` ⇒ reduces to `S · exp(r·T)`
* `continuousDividendForward_zero_T`      : `T = 0` ⇒ forward equals spot
* `continuousDividendForward_linear_S`    : linear in spot `S`
* `continuousDividendForward_equal_rates` : `r = q` ⇒ forward equals spot

## Why this lemma

The continuous-dividend forward is the cost-of-carry no-arbitrage
identity for the *single most-traded class of forwards in practice*:
equity-index futures (S&P, NDX, EUR50 — quoted using this exact
formula with `q` as the index dividend yield), FX forwards (covered
interest-rate parity), and commodity forwards with convenience-yield
adjustments.  Surfacing the algebraic closed form in Pythia gives the
`pythia` tactic cascade a clean closure target for cost-of-carry /
fair-forward-value computations across asset classes.

## References

* Hull, J. C. *Options, Futures, and Other Derivatives*, 10th ed.
  Pearson (2017), §5.5 (forwards on a stock paying a known dividend
  yield).
* Björk, T. *Arbitrage Theory in Continuous Time*, 3rd ed.
  Oxford University Press (2009), Ch. 7.
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- Continuous-dividend forward price under cost-of-carry. -/
noncomputable def continuousDividendForward (S r q T : ℝ) : ℝ :=
  S * Real.exp ((r - q) * T)

/-- **Zero-dividend specialisation.** With `q = 0` the continuous-
dividend forward reduces to the standard cost-of-carry forward
`S · exp(r·T)`. -/
@[stat_lemma]
theorem continuousDividendForward_zero_q (S r T : ℝ) :
    continuousDividendForward S r 0 T = S * Real.exp (r * T) := by
  unfold continuousDividendForward
  simp [sub_zero]

/-- **At-zero-time specialisation.** At `T = 0` the forward equals
the spot (instantaneous delivery, no carry cost). -/
@[stat_lemma]
theorem continuousDividendForward_zero_T (S r q : ℝ) :
    continuousDividendForward S r q 0 = S := by
  unfold continuousDividendForward
  simp [mul_zero, Real.exp_zero]

/-- **Scaling in spot.** Scaling `S` by `α` scales the forward by
`α` (the forward is linear-homogeneous in the underlying spot). -/
@[stat_lemma]
theorem continuousDividendForward_linear_S (S α r q T : ℝ) :
    continuousDividendForward (α * S) r q T
      = α * continuousDividendForward S r q T := by
  unfold continuousDividendForward
  ring

/-- **Equal-rate specialisation.** When the risk-free rate equals
the dividend yield (`r = q`), the carry cost vanishes and the forward
equals the spot — the cost-of-carry "no-carry" arbitrage condition
familiar from FX covered interest parity. -/
@[stat_lemma]
theorem continuousDividendForward_equal_rates (S r T : ℝ) :
    continuousDividendForward S r r T = S := by
  unfold continuousDividendForward
  simp [sub_self, zero_mul, Real.exp_zero]

end Pythia.Finance
