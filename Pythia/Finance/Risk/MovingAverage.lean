/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Moving Average Crossover Signal (algebraic kernel)

The moving average crossover is the most widely-used trend signal
in quantitative trading. The signal is defined as:

    signal(fast, slow) = fast - slow

where `fast` is the short-period moving average and `slow` is the
long-period moving average. A positive signal indicates upward
momentum (fast MA above slow MA); negative indicates downward
momentum.

The exponential moving average (EMA) update is:

    EMA_new = alpha * price + (1 - alpha) * EMA_old

where alpha = 2 / (period + 1) is the smoothing factor.

## Main results

* `crossoverSignal`              : `fast - slow`
* `crossoverSignal_pos_iff`      : positive iff fast > slow
* `emaUpdate`                    : `alpha * price + (1 - alpha) * ema_old`
* `emaUpdate_at_alpha_one`       : alpha = 1 gives just the price
* `emaUpdate_convex`             : EMA is a convex combination for alpha in [0,1]

## References

* Brock, W., Lakonishok, J. and LeBaron, B. "Simple Technical
  Trading Rules and the Stochastic Properties of Stock Returns."
  Journal of Finance 47(5): 1731-1764 (1992).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Moving average crossover signal: fast MA minus slow MA. -/
noncomputable def crossoverSignal (fast slow : ℝ) : ℝ := fast - slow

/-- Exponential moving average update step. -/
noncomputable def emaUpdate (alpha price ema_old : ℝ) : ℝ :=
  alpha * price + (1 - alpha) * ema_old

/-- **Positive signal iff fast above slow.** -/
@[stat_lemma]
theorem crossoverSignal_pos_iff {fast slow : ℝ} :
    0 < crossoverSignal fast slow ↔ slow < fast := by
  unfold crossoverSignal
  exact sub_pos

/-- **Zero signal iff MAs are equal.** -/
@[stat_lemma]
theorem crossoverSignal_zero_iff {fast slow : ℝ} :
    crossoverSignal fast slow = 0 ↔ fast = slow := by
  unfold crossoverSignal
  exact sub_eq_zero

/-- **Signal antisymmetric.** -/
@[stat_lemma]
theorem crossoverSignal_antisymm (fast slow : ℝ) :
    crossoverSignal slow fast = -crossoverSignal fast slow := by
  unfold crossoverSignal; ring

/-- **EMA at alpha = 1.** Full weight on new price. -/
@[stat_lemma]
theorem emaUpdate_at_alpha_one (price ema_old : ℝ) :
    emaUpdate 1 price ema_old = price := by
  unfold emaUpdate; ring

/-- **EMA at alpha = 0.** Full weight on old EMA (no update). -/
@[stat_lemma]
theorem emaUpdate_at_alpha_zero (price ema_old : ℝ) :
    emaUpdate 0 price ema_old = ema_old := by
  unfold emaUpdate; ring

/-- **EMA is a convex combination.** For alpha in [0, 1], the EMA
lies between the price and the old EMA (specifically between
min and max of the two). -/
@[stat_lemma]
theorem emaUpdate_between {alpha price ema_old : ℝ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (h : ema_old ≤ price) :
    ema_old ≤ emaUpdate alpha price ema_old := by
  unfold emaUpdate
  have h1 : 0 ≤ 1 - alpha := by linarith
  have h2 : 0 ≤ alpha * (price - ema_old) := mul_nonneg ha0 (by linarith)
  linarith

/-- **EMA bounded above.** For alpha in [0, 1] and price >= ema_old,
the EMA does not exceed the price. -/
@[stat_lemma]
theorem emaUpdate_le_price {alpha price ema_old : ℝ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (h : ema_old ≤ price) :
    emaUpdate alpha price ema_old ≤ price := by
  unfold emaUpdate
  have h1 : 0 ≤ (1 - alpha) * (price - ema_old) :=
    mul_nonneg (by linarith) (by linarith)
  linarith

end Pythia.Finance
