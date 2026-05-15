/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Maximum Drawdown (algebraic identities)

The *drawdown* of a portfolio at time `t` relative to its running
maximum is

    DD(t) = peak(t) - value(t),

where `peak(t) = max_{s ≤ t} value(s)`. The *maximum drawdown* over
a horizon is the largest peak-to-trough decline.

This file gives the algebraic identities for drawdown as a function
of peak and current value, without invoking any stochastic or
time-series machinery. The running-maximum / supremum connection is
deferred to a measure-theoretic module.

## Main results

* `drawdown`                 : `peak - value`
* `drawdown_nonneg`          : `0 ≤ drawdown peak value` when `value ≤ peak`
* `drawdown_zero_at_peak`    : `drawdown peak peak = 0`
* `drawdown_mono_value`      : drawdown is antitone in value for fixed peak
* `drawdown_ratio`           : relative drawdown `drawdown peak value / peak`
* `drawdown_ratio_le_one`    : relative drawdown ≤ 1 when `0 < value` and
  `value ≤ peak`

## Why this lemma

Maximum drawdown is the primary risk metric for fund evaluation,
portfolio insurance trigger levels, and regulatory risk reporting
(MiFID II, SEC Form ADV). Surfacing the algebraic drawdown
identities in Pythia gives the `pythia` tactic cascade a clean
closure target for drawdown-bound and risk-metric goals.

## References

* Magdon-Ismail, M. and Atiya, A. F. "Maximum Drawdown."
  *Risk Magazine* 17(10): 99-102 (2004).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Drawdown: `peak - value`. The decline from the running maximum. -/
noncomputable def drawdown (peak value : ℝ) : ℝ :=
  peak - value

/-- Relative drawdown: `(peak - value) / peak`. The decline as a
fraction of the peak value. -/
noncomputable def drawdownRatio (peak value : ℝ) : ℝ :=
  drawdown peak value / peak

/-- **Non-negativity.** The drawdown is non-negative when the current
value does not exceed the peak. -/
@[stat_lemma]
theorem drawdown_nonneg {peak value : ℝ} (h : value ≤ peak) :
    0 ≤ drawdown peak value := by
  unfold drawdown
  exact sub_nonneg.mpr h

/-- **Zero at peak.** When the current value equals the peak, the
drawdown is zero (no decline). -/
@[stat_lemma]
theorem drawdown_zero_at_peak (peak : ℝ) :
    drawdown peak peak = 0 := by
  unfold drawdown; ring

/-- **Antitone in value.** For a fixed peak, a lower value means a
larger drawdown. -/
@[stat_lemma]
theorem drawdown_mono_value {peak : ℝ} {v₁ v₂ : ℝ} (h : v₁ ≤ v₂) :
    drawdown peak v₂ ≤ drawdown peak v₁ := by
  unfold drawdown
  exact sub_le_sub_left h peak

/-- **Monotone in peak.** For a fixed value, a higher peak means a
larger drawdown. -/
@[stat_lemma]
theorem drawdown_mono_peak {value : ℝ} {p₁ p₂ : ℝ} (h : p₁ ≤ p₂) :
    drawdown p₁ value ≤ drawdown p₂ value := by
  unfold drawdown
  exact sub_le_sub_right h value

/-- **Relative drawdown at most 1.** When both peak and value are
positive and value does not exceed peak, the relative drawdown
(as a fraction of peak) is in [0, 1]. The upper bound of 1 says
you cannot lose more than 100% of the peak. -/
@[stat_lemma]
theorem drawdownRatio_le_one {peak value : ℝ}
    (hp : 0 < peak) (_hv : 0 ≤ value) (h : value ≤ peak) :
    drawdownRatio peak value ≤ 1 := by
  unfold drawdownRatio drawdown
  rw [div_le_one hp]
  linarith

/-- **Relative drawdown non-negative.** Under the natural hypothesis
`value ≤ peak` with `peak > 0`, the ratio is non-negative. -/
@[stat_lemma]
theorem drawdownRatio_nonneg {peak value : ℝ}
    (hp : 0 < peak) (h : value ≤ peak) :
    0 ≤ drawdownRatio peak value := by
  unfold drawdownRatio
  exact div_nonneg (drawdown_nonneg h) (le_of_lt hp)

end Pythia.Finance
