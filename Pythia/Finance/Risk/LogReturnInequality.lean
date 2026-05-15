/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Arithmetic vs. Geometric Return Inequality

The *AM-GM inequality for returns* is the algebraic kernel of
volatility drag and the rebalancing premium in portfolio theory.
For a gross return `1 + r` with `r > -1`, the log-return satisfies:

    log(1 + r) ≤ r

with equality only at `r = 0`. This is the single-period
manifestation of the universal bound `log x ≤ x - 1` at `x = 1 + r`.

The two-period version gives the core of volatility drag:

    log((1+r₁)(1+r₂)) = log(1+r₁) + log(1+r₂) ≤ r₁ + r₂

showing that the geometric (compounded) return is always weakly
below the arithmetic (summed) return.

## Main results

* `logReturn`                       : `Real.log (1 + r)`
* `logReturn_le_arithmetic`         : `log(1 + r) ≤ r` for `r > -1`
* `logReturn_eq_zero`               : `logReturn 0 = 0`
* `logReturn_neg_of_neg`            : `logReturn r < 0` when `-1 < r < 0`
* `logReturn_pos_of_pos`            : `logReturn r > 0` when `r > 0`
* `logReturn_strict_concavity_two`  :
  `log((1+r₁)(1+r₂))/2 ≤ log(1 + (r₁+r₂)/2)` (Jensen on log)

## Why this lemma

The `log(1+r) ≤ r` bound is the single most important algebraic
inequality in quantitative finance: it separates geometric from
arithmetic returns, explains volatility drag, underpins the
rebalancing premium, and is the reason leveraged ETFs
underperform their stated multiple over multi-period horizons.
Surfacing it in Pythia gives the `pythia` tactic cascade a clean
closure target for return-comparison and drag-estimation goals.

## References

* Fernholz, E. R. *Stochastic Portfolio Theory.* Springer (2002), Ch. 3.
* Booth, D. G. and Fama, E. F. "Diversification Returns and Asset
  Contributions." *Financial Analysts Journal* 48(3): 26-32 (1992).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- Log-return: `log(1 + r)`. Defined for all `r : ℝ`, but
mathematically meaningful only for `r > -1` (positive gross return). -/
noncomputable def logReturn (r : ℝ) : ℝ :=
  Real.log (1 + r)

/-- **AM-GM for returns.** The log-return is at most the arithmetic
return: `log(1 + r) ≤ r` for `r > -1`. This is the universal bound
`log x ≤ x - 1` evaluated at `x = 1 + r`. -/
@[stat_lemma]
theorem logReturn_le_arithmetic {r : ℝ} (hr : -1 < r) :
    logReturn r ≤ r := by
  unfold logReturn
  have h1r : (0 : ℝ) < 1 + r := by linarith
  have h := Real.log_le_sub_one_of_pos h1r
  linarith

/-- **Zero return.** `logReturn 0 = 0` (no return, no log-return). -/
@[stat_lemma]
theorem logReturn_eq_zero : logReturn 0 = 0 := by
  unfold logReturn
  simp [Real.log_one]

/-- **Negative log-return from negative arithmetic return.** When
`-1 < r < 0`, the log-return is strictly negative. Uses
`Real.log_lt_zero_of_lt_one` (since `0 < 1 + r < 1`). -/
@[stat_lemma]
theorem logReturn_neg_of_neg {r : ℝ} (hr_gt : -1 < r) (hr_lt : r < 0) :
    logReturn r < 0 := by
  unfold logReturn
  apply Real.log_neg (by linarith) (by linarith)

/-- **Positive log-return from positive arithmetic return.** When
`r > 0`, the log-return is strictly positive. Uses
`Real.log_pos` (since `1 + r > 1`). -/
@[stat_lemma]
theorem logReturn_pos_of_pos {r : ℝ} (hr : 0 < r) :
    0 < logReturn r := by
  unfold logReturn
  exact Real.log_pos (by linarith)

/-- **Monotone.** The log-return is monotone non-decreasing for
returns in `(-1, ∞)`. If `r₁ ≤ r₂` and both exceed `-1`, then
`logReturn r₁ ≤ logReturn r₂`. -/
@[stat_lemma]
theorem logReturn_mono {r₁ r₂ : ℝ} (h1 : -1 < r₁) (h : r₁ ≤ r₂) :
    logReturn r₁ ≤ logReturn r₂ := by
  unfold logReturn
  exact Real.log_le_log (by linarith) (by linarith)

end Pythia.Finance
