/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sortino Ratio (algebraic form)

The Sortino ratio refines the Sharpe ratio by replacing total
volatility `σ` with the *downside deviation* `σ_d` — the
square-root of the average squared negative deviations from a target
return.  This corrects for the asymmetric-risk preference of most
investors (positive volatility is not "risk").

This file gives the algebraic form `sortinoRatio μ rf σ_d :=
(μ - rf) / σ_d`.  The semantic distinction between `σ` (total) and
`σ_d` (downside) is carried by the argument-name only; the
algebraic identities are identical to those of `Pythia.Finance.SharpeRatio`.

## Main results

* `sortinoRatio`                : `(μ - rf) / σ_d`
* `sortinoRatio_pos`            : `0 < sortinoRatio` when `rf < μ` and `0 < σ_d`
* `sortinoRatio_mono_excess`    : monotone in `μ - rf` for `0 < σ_d`
* `sortinoRatio_scale_invariant`:
  `sortinoRatio (α·μ) (α·rf) (α·σ_d) = sortinoRatio μ rf σ_d` for `α > 0`

## Why this lemma

Risk-adjusted-return metrics are the practitioner reporting standard.
Sharpe penalises upside volatility (a known weakness); Sortino
restricts to downside.  Surfacing both in Pythia gives the `pythia`
tactic cascade a clean closure target for risk-adjusted-return
sanity checks under either symmetric or asymmetric risk preferences.

## References

* Sortino, F. A. and Price, L. N. "Performance Measurement in a
  Downside Risk Framework." *Journal of Investing* 3(3): 59-64 (1994).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Sortino ratio (algebraic form): `(μ - rf) / σ_d`,
    where `σ_d` is the downside deviation. -/
noncomputable def sortinoRatio (μ rf σ_d : ℝ) : ℝ :=
  (μ - rf) / σ_d

/-- **Positivity.** Strictly positive when the expected return exceeds
the risk-free rate and the downside deviation is strictly positive. -/
@[stat_lemma]
theorem sortinoRatio_pos {μ rf σ_d : ℝ} (h_excess : rf < μ) (hσ : 0 < σ_d) :
    0 < sortinoRatio μ rf σ_d := by
  unfold sortinoRatio
  exact div_pos (sub_pos.mpr h_excess) hσ

/-- **Monotone in excess return.** For fixed positive downside
deviation, the Sortino ratio is monotone non-decreasing in
`μ - rf`. -/
@[stat_lemma]
theorem sortinoRatio_mono_excess {σ_d : ℝ} (hσ : 0 < σ_d)
    {μ₁ rf₁ μ₂ rf₂ : ℝ} (h : μ₁ - rf₁ ≤ μ₂ - rf₂) :
    sortinoRatio μ₁ rf₁ σ_d ≤ sortinoRatio μ₂ rf₂ σ_d := by
  unfold sortinoRatio
  exact div_le_div_of_nonneg_right h hσ.le

/-- **Scale invariance.** Rescaling all three arguments by a strictly
positive constant leaves the Sortino ratio unchanged. -/
@[stat_lemma]
theorem sortinoRatio_scale_invariant {α : ℝ} (hα : 0 < α) (μ rf σ_d : ℝ) :
    sortinoRatio (α * μ) (α * rf) (α * σ_d) = sortinoRatio μ rf σ_d := by
  unfold sortinoRatio
  rw [← mul_sub]
  exact mul_div_mul_left (μ - rf) σ_d hα.ne'

end Pythia.Finance
