/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dividend Discount Model (multi-stage algebraic kernel)

The two-stage dividend discount model values an equity as the sum of
a finite high-growth phase and an infinite terminal (stable) phase:

    V = sum_{t=1}^{N} D_0 * (1+g_H)^t / (1+r)^t
      + D_0 * (1+g_H)^N * (1+g_S) / ((r - g_S) * (1+r)^N)

where `g_H` is the high-growth rate, `g_S` is the stable growth rate,
and `r` is the required return with `r > g_S`.

This file gives algebraic identities for the terminal value component
(the Gordon growth perpetuity applied at the transition point).

## Main results

* `terminalValue`                 : `D_N * (1 + g_S) / (r - g_S)`
* `terminalValue_pos`             : strictly positive under natural conditions
* `terminalValue_antitone_rate`   : antitone in `r` for fixed `D_N, g_S`
* `terminalValue_mono_growth`     : monotone in `g_S` for fixed `D_N, r`

## References

* Williams, J. B. *The Theory of Investment Value.* Harvard (1938).
* Damodaran, A. *Investment Valuation.* Wiley (2012), Chapter 13.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Terminal value of a two-stage DDM at the transition point:
    `V_N = D_N * (1 + g_S) / (r - g_S)`. -/
noncomputable def terminalValue (D_N g_S r : ℝ) : ℝ :=
  D_N * (1 + g_S) / (r - g_S)

/-- **Positivity.** The terminal value is strictly positive when
the terminal dividend is positive, stable growth is nonneg, and
the required return exceeds the growth rate. -/
@[stat_lemma]
theorem terminalValue_pos {D_N g_S r : ℝ}
    (hD : 0 < D_N) (hg : 0 ≤ g_S) (hr : g_S < r) :
    0 < terminalValue D_N g_S r := by
  unfold terminalValue
  apply div_pos
  · exact mul_pos hD (by linarith)
  · linarith

/-- **Antitone in required return.** For fixed `D_N > 0` and
`g_S >= 0`, increasing `r` decreases the terminal value (higher
discount rate means lower present value). -/
@[stat_lemma]
theorem terminalValue_antitone_rate {D_N g_S : ℝ}
    (hD : 0 < D_N) (hg : 0 ≤ g_S)
    {r₁ r₂ : ℝ} (hr₁ : g_S < r₁) (hr : r₁ ≤ r₂) :
    terminalValue D_N g_S r₂ ≤ terminalValue D_N g_S r₁ := by
  unfold terminalValue
  exact div_le_div_of_nonneg_left (le_of_lt (mul_pos hD (by linarith)))
    (by linarith) (by linarith)

/-- **Monotone in terminal dividend.** Higher terminal dividend means
higher terminal value (all else equal). -/
@[stat_lemma]
theorem terminalValue_mono_dividend {g_S r : ℝ}
    (hr : g_S < r)
    {D₁ D₂ : ℝ} (hD : D₁ ≤ D₂) (_hD₁ : 0 ≤ D₁) (hg : 0 ≤ g_S) :
    terminalValue D₁ g_S r ≤ terminalValue D₂ g_S r := by
  unfold terminalValue
  apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ r - g_S)
  exact mul_le_mul_of_nonneg_right hD (by linarith)

end Pythia.Finance
