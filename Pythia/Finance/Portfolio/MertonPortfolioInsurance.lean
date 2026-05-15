/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Merton Portfolio Insurance / CPPI (Constant Proportion Portfolio Insurance)

Constant Proportion Portfolio Insurance (CPPI) is a dynamic portfolio
strategy that maintains a fixed multiplier on the "cushion" -- the
excess of current wealth `W` over a protected floor `F`:

    exposure(W, F) = m * (W - F),

where `m > 0` is the multiplier and `C = W - F` is the cushion. The
investor holds `exposure` in the risky asset and the remainder `W -
exposure` in the safe asset (bonds / cash). Maintaining the floor
requires rebalancing continuously; in discrete time an intraday gap
risk can breach `F`, but the strategy provides protection on average.

CPPI generalises Leland-Rubinstein portfolio insurance (which
dynamically replicates a put option) by replacing the put with a linear
cushion rule. The multiplier `m` controls aggressiveness: `m = 1` gives
a "conservative CPPI" where exposure never exceeds wealth; `m > 1`
amplifies upside but also downside risk.

## Main results

* `cppiExposure`                           : `m * (W - F)`, the risky exposure
* `cppiCushion`                            : `W - F`, the cushion
* `cppiExposure_pos`                       : exposure is strictly positive when `m > 0`
  and `W > F`
* `cppiExposure_mono_wealth`               : exposure is monotone non-decreasing in wealth
* `cppiExposure_scale`                     : exposure scales linearly in the multiplier
* `cppiCushion_pos_iff`                    : cushion positive iff wealth exceeds the floor
* `cppiExposure_le_wealth_of_multiplier_le_one` : with `m ≤ 1` and `F ≥ 0`, exposure
  never exceeds wealth (conservative CPPI safety bound)
* `cppiExposure_nonneg`                    : exposure is non-negative whenever `m ≥ 0`
  and `F ≤ W`

## Why this lemma

Portfolio insurance is a cornerstone of institutional risk management
and structured product design. The algebraic kernel -- the cushion rule
and its safety bounds -- underpins regulatory capital-floor products,
pension liability-driven investment overlays, and volatility-targeting
strategies. Surfacing these identities in Pythia gives the `pythia`
tactic cascade clean closure targets for CPPI sizing and floor-safety
goals.

## References

* Black, F. and Jones, R. "Simplifying Portfolio Insurance."
  *Journal of Portfolio Management* 14(1): 48-51 (1987).
* Perold, A. F. and Sharpe, W. F. "Dynamic Strategies for Asset
  Allocation." *Financial Analysts Journal* 51(1): 149-160 (1995).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- CPPI risky exposure: `m * (W - F)`, where `W` is current wealth,
`F` is the floor (insured minimum), and `m` is the multiplier. -/
noncomputable def cppiExposure (m W F : ℝ) : ℝ :=
  m * (W - F)

/-- CPPI cushion: the excess of current wealth over the floor, `W - F`. -/
noncomputable def cppiCushion (W F : ℝ) : ℝ :=
  W - F

/-- **Positivity.** When the multiplier `m` is strictly positive and
wealth strictly exceeds the floor (`W > F`), the CPPI exposure is
strictly positive. The proof combines `mul_pos` with `sub_pos`. -/
@[stat_lemma]
theorem cppiExposure_pos {m W F : ℝ} (hm : 0 < m) (hWF : F < W) :
    0 < cppiExposure m W F := by
  unfold cppiExposure
  exact mul_pos hm (sub_pos.mpr hWF)

/-- **Monotone in wealth.** For fixed multiplier `m > 0` and floor `F`,
the CPPI exposure is monotone non-decreasing in wealth `W`. The proof
uses `mul_le_mul_of_nonneg_left` (scale by a non-negative factor
preserves order) and `sub_le_sub_right` (subtracting `F` from both
sides preserves the inequality). -/
@[stat_lemma]
theorem cppiExposure_mono_wealth {m F : ℝ} (hm : 0 < m)
    {W₁ W₂ : ℝ} (h : W₁ ≤ W₂) :
    cppiExposure m W₁ F ≤ cppiExposure m W₂ F := by
  unfold cppiExposure
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right h F) hm.le

/-- **Multiplier scaling.** Scaling the multiplier by `α` scales the
exposure by `α`. Ring identity. -/
@[stat_lemma]
theorem cppiExposure_scale (α m W F : ℝ) :
    cppiExposure (α * m) W F = α * cppiExposure m W F := by
  unfold cppiExposure
  ring

/-- **Cushion positivity iff.** The cushion is strictly positive if and
only if wealth strictly exceeds the floor. Uses `sub_pos` from
Mathlib.Algebra.Order.Sub.Defs.

The iff is split into two directed lemmas below for use by the `pythia`
cascade; the iff statement is provided here for human readability. -/
theorem cppiCushion_pos_iff {W F : ℝ} :
    0 < cppiCushion W F ↔ F < W := by
  unfold cppiCushion
  exact sub_pos

/-- **Forward direction of cushion positivity iff.**
If `F < W`, then `0 < cppiCushion W F`. -/
@[stat_lemma]
theorem cppiCushion_pos_of_lt {W F : ℝ} (h : F < W) :
    0 < cppiCushion W F :=
  cppiCushion_pos_iff.mpr h

/-- **Reverse direction of cushion positivity iff.**
If `0 < cppiCushion W F`, then `F < W`. -/
@[stat_lemma]
theorem lt_of_cppiCushion_pos {W F : ℝ} (h : 0 < cppiCushion W F) :
    F < W :=
  cppiCushion_pos_iff.mp h

/-- **Conservative CPPI safety bound.** When the multiplier satisfies
`0 < m` and `m ≤ 1`, the floor is non-negative (`0 ≤ F`), and wealth
covers the floor (`F ≤ W`), the risky exposure does not exceed current
wealth:

    cppiExposure m W F ≤ W.

Proof sketch: `m * (W - F) ≤ 1 * (W - F) = W - F ≤ W`. The first
inequality uses `mul_le_mul_of_nonneg_right` (multiplying a non-negative
quantity `W - F` by a smaller non-negative factor `m ≤ 1` shrinks it);
the second uses `sub_le_self` (subtracting a non-negative term from `W`
gives something at most `W`). -/
@[stat_lemma]
theorem cppiExposure_le_wealth_of_multiplier_le_one
    {m W F : ℝ} (hm_pos : 0 < m) (hm_le : m ≤ 1) (hF : 0 ≤ F) (hFW : F ≤ W) :
    cppiExposure m W F ≤ W := by
  unfold cppiExposure
  have hcushion : 0 ≤ W - F := sub_nonneg.mpr hFW
  -- m * (W - F) ≤ 1 * (W - F) = W - F, since m ≤ 1 and 0 ≤ W - F
  have h1 : m * (W - F) ≤ 1 * (W - F) :=
    mul_le_mul_of_nonneg_right hm_le hcushion
  -- W - F ≤ W  (since 0 ≤ F)
  have h2 : W - F ≤ W := sub_le_self W hF
  -- 0 < m ensures the strategy is active; 0 ≤ m closes the bound via linarith
  have hm_nonneg : 0 ≤ m := hm_pos.le
  linarith

/-- **Non-negativity.** When `m ≥ 0` and `F ≤ W` (cushion non-negative),
the exposure is non-negative. Uses `mul_nonneg` and `sub_nonneg`. -/
@[stat_lemma]
theorem cppiExposure_nonneg {m W F : ℝ} (hm : 0 ≤ m) (hFW : F ≤ W) :
    0 ≤ cppiExposure m W F := by
  unfold cppiExposure
  exact mul_nonneg hm (sub_nonneg.mpr hFW)

end Pythia.Finance
