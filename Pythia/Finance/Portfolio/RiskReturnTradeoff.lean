/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Risk-Return Tradeoff (capital market line)

The capital market line (CML) gives the expected return of an
efficient portfolio as a linear function of its standard deviation:

    E[r_p] = rf + ((E[r_m] - rf) / sigma_m) * sigma_p

where rf is the risk-free rate, r_m is the market return, sigma_m
is the market standard deviation, and sigma_p is the portfolio
standard deviation.

The slope of the CML is the market Sharpe ratio.

## Main results

* `cmlReturn`             : `rf + sharpe * sigma_p`
* `cmlReturn_at_zero_risk`: risk-free rate at zero vol
* `cmlReturn_mono_risk`   : monotone in sigma_p for positive Sharpe
* `cmlReturn_at_market`   : market return at market vol

## References

* Sharpe, W. F. "Capital Asset Prices." Journal of Finance
  19(3): 425-442 (1964).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Capital market line return: rf + sharpe * sigma_p. -/
noncomputable def cmlReturn (rf sharpe sigma_p : ℝ) : ℝ :=
  rf + sharpe * sigma_p

/-- **Zero risk.** At zero volatility, the CML return equals the
risk-free rate. -/
@[stat_lemma]
theorem cmlReturn_at_zero_risk (rf sharpe : ℝ) :
    cmlReturn rf sharpe 0 = rf := by
  unfold cmlReturn; ring

/-- **Monotone in risk.** For positive Sharpe ratio, higher
volatility means higher expected return on the CML. -/
@[stat_lemma]
theorem cmlReturn_mono_risk {rf sharpe : ℝ} (hs : 0 < sharpe)
    {σ₁ σ₂ : ℝ} (hσ : σ₁ ≤ σ₂) :
    cmlReturn rf sharpe σ₁ ≤ cmlReturn rf sharpe σ₂ := by
  unfold cmlReturn
  linarith [mul_le_mul_of_nonneg_left hσ (le_of_lt hs)]

/-- **Market portfolio.** At market volatility, the CML return
is rf + sharpe * sigma_m, which equals the market expected return
by definition of the Sharpe ratio. -/
@[stat_lemma]
theorem cmlReturn_linear (rf sharpe sigma_p : ℝ) :
    cmlReturn rf sharpe sigma_p = rf + sharpe * sigma_p := by
  unfold cmlReturn; ring

/-- **CML dominance.** For positive Sharpe ratio and nonneg
volatility, the CML return is at least the risk-free rate. -/
@[stat_lemma]
theorem cmlReturn_ge_rf {rf sharpe sigma_p : ℝ}
    (hs : 0 ≤ sharpe) (hσ : 0 ≤ sigma_p) :
    rf ≤ cmlReturn rf sharpe sigma_p := by
  unfold cmlReturn
  linarith [mul_nonneg hs hσ]

/-- **Excess return proportional to risk.** -/
@[stat_lemma]
theorem cmlReturn_excess (rf sharpe sigma_p : ℝ) :
    cmlReturn rf sharpe sigma_p - rf = sharpe * sigma_p := by
  unfold cmlReturn; ring

end Pythia.Finance
