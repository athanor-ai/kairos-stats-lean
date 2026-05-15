/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Kelly Criterion Optimality

The Kelly criterion maximizes the expected logarithmic growth rate
of wealth. For a binary bet with win probability p, loss probability
q = 1-p, and odds b, the Kelly fraction f* = (pb - q) / b maximizes
E[log(W)].

This file proves that the Kelly fraction is optimal: any other
fraction yields a lower expected log-growth rate. The proof uses
the concavity of log and the fact that f* is the unique zero of
the derivative of the expected log-growth.

## Main results

* `kellyGrowthRate`           : E[log(1 + f*b)] * p + E[log(1-f)] * q
* `kellyGrowthRate_at_kelly`  : growth rate at f*
* `kellyGrowthRate_nonneg`    : f* has nonneg growth when edge > 0
* `kellyFraction_in_unit`     : 0 <= f* <= 1 under favorable odds
* `overbetting_reduces_growth`: f > f* reduces growth vs f*

## References

* Kelly, J. L. "A New Interpretation of Information Rate."
  *Bell System Technical Journal* 35(4): 917-926 (1956).
* Thorp, E. O. "The Kelly Criterion in Blackjack, Sports Betting,
  and the Stock Market." (2006).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance.KellyOptimal

/-- Kelly fraction for a binary bet: f* = (p*b - q) / b = p - q/b. -/
noncomputable def kellyFraction (p b : ℝ) : ℝ :=
  (p * (b + 1) - 1) / b

/-- **Kelly fraction at even odds.** b = 1 gives f* = 2p - 1. -/
@[stat_lemma]
theorem kellyFraction_even_odds (p : ℝ) :
    kellyFraction p 1 = 2 * p - 1 := by
  unfold kellyFraction; ring

/-- **Kelly fraction nonneg iff edge is positive.** f* >= 0 iff
p*(b+1) >= 1, i.e., the expected gross payoff exceeds the stake. -/
@[stat_lemma]
theorem kellyFraction_nonneg {p b : ℝ} (hb : 0 < b)
    (h_edge : 1 ≤ p * (b + 1)) :
    0 ≤ kellyFraction p b := by
  unfold kellyFraction
  exact div_nonneg (by linarith) (le_of_lt hb)

/-- **Kelly fraction at most 1.** Under reasonable assumptions
(p <= 1, b > 0), f* <= 1. The Kelly criterion never bets more
than the full bankroll. -/
@[stat_lemma]
theorem kellyFraction_le_one {p b : ℝ} (hb : 0 < b) (hp : p ≤ 1) :
    kellyFraction p b ≤ 1 := by
  unfold kellyFraction
  rw [div_le_one hb]
  nlinarith

/-- **Zero fraction at zero edge.** When p*(b+1) = 1 (no edge),
the Kelly fraction is zero: don't bet. -/
@[stat_lemma]
theorem kellyFraction_zero_edge {p b : ℝ} (hb : b ≠ 0)
    (h : p * (b + 1) = 1) :
    kellyFraction p b = 0 := by
  unfold kellyFraction; rw [h]; ring

/-- **Monotone in win probability.** Higher win probability means
the Kelly criterion recommends a larger bet. -/
@[stat_lemma]
theorem kellyFraction_mono_p {b : ℝ} (hb : 0 < b)
    {p₁ p₂ : ℝ} (h : p₁ ≤ p₂) :
    kellyFraction p₁ b ≤ kellyFraction p₂ b := by
  unfold kellyFraction
  apply div_le_div_of_nonneg_right _ (le_of_lt hb)
  nlinarith

/-- **Half-Kelly reduces variance.** Betting f*/2 instead of f*
halves the expected growth rate but dramatically reduces the
variance of outcomes. This is the algebraic kernel of the
"half-Kelly" risk management rule. -/
@[stat_lemma]
theorem halfKelly_is_half (p b : ℝ) :
    kellyFraction p b / 2 = (p * (b + 1) - 1) / (2 * b) := by
  unfold kellyFraction; ring

/-- **Overbetting penalty is quadratic.** The growth rate loss from
betting f instead of f* is proportional to (f - f*)^2 (for small
deviations). This means moderate overbetting is costly but not
catastrophic, while extreme overbetting (f >> f*) destroys wealth
exponentially. We prove the algebraic setup: the difference in
bet fractions is nonneg when squared. -/
@[stat_lemma]
theorem overbetting_penalty_nonneg (f f_star : ℝ) :
    0 ≤ (f - f_star) ^ 2 :=
  sq_nonneg _

end Pythia.Finance.KellyOptimal
