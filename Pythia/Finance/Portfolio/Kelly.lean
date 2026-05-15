/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Kelly Criterion (optimal-fraction closed form)

For a binary-outcome bet with win-probability `p`, lose-probability
`q = 1 - p`, and net-odds `b > 0` (win `b` units per 1 unit staked,
lose `1` unit on loss), the *Kelly criterion* prescribes the
fraction of bankroll to stake to maximise the expected logarithmic
growth rate:

    f*(p, b) = p - q / b = (p · (b + 1) - 1) / b.

Equivalently, `f* = edge / odds = (p·b - q) / b`.

This file gives the algebraic closed form and its sign / monotonicity
properties — the bedrock of position-sizing under expected-utility-of-
log-wealth optimisation. Kelly underpins everything from blackjack
bankroll management to optimal portfolio leverage in continuous-time
finance (Thorp 1969, MacLean-Thorp-Ziemba 2010).

## Main results

* `kellyFraction`          : `(p · (b + 1) - 1) / b`
* `kellyFraction_zero_edge`: at `p · (b+1) = 1` (zero edge) → `f* = 0`
* `kellyFraction_mono_p`   : monotone non-decreasing in `p` for `b > 0`
* `kellyFraction_unit_odds`: `b = 1` reduces to `f* = 2p - 1`
  (even-money bet)

## Why this lemma

Position sizing is the dual of return prediction: knowing the edge
without knowing the right fraction to stake leaves expected-log-wealth
growth on the table.  Surfacing the closed-form Kelly identity in
Pythia gives the `pythia` tactic cascade a clean closure target for
bankroll-allocation / leverage-sizing goals.

## References

* Kelly, J. L. "A New Interpretation of Information Rate."
  *Bell System Technical Journal* 35(4): 917-926 (1956).
* Thorp, E. O. "Optimal Gambling Systems for Favorable Games."
  *Revue de l'Institut International de Statistique* 37(3): 273-293 (1969).
* MacLean, L. C., Thorp, E. O., and Ziemba, W. T.
  *The Kelly Capital Growth Investment Criterion.* World Scientific (2010).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Kelly-optimal fraction of bankroll for a binary bet with
win-probability `p` and net-odds `b`:
    `f*(p, b) = (p · (b + 1) - 1) / b`. -/
noncomputable def kellyFraction (p b : ℝ) : ℝ :=
  (p * (b + 1) - 1) / b

/-- **Zero-edge specialisation.** When the expected gross-payoff
`p · (b + 1)` equals 1 (no edge), the Kelly fraction is zero — do
not bet. -/
@[stat_lemma]
theorem kellyFraction_zero_edge {p b : ℝ} (hb : b ≠ 0)
    (h_zero : p * (b + 1) = 1) :
    kellyFraction p b = 0 := by
  unfold kellyFraction; rw [h_zero]; ring

/-- **Monotone in win-probability.** For fixed positive odds `b`,
the Kelly fraction is monotone non-decreasing in `p` — higher
win-probability ⟹ larger optimal stake. -/
@[stat_lemma]
theorem kellyFraction_mono_p {b : ℝ} (hb : 0 < b)
    {p₁ p₂ : ℝ} (h : p₁ ≤ p₂) :
    kellyFraction p₁ b ≤ kellyFraction p₂ b := by
  unfold kellyFraction
  have hb_plus : 0 < b + 1 := by linarith
  have h_num : p₁ * (b + 1) - 1 ≤ p₂ * (b + 1) - 1 := by
    have : p₁ * (b + 1) ≤ p₂ * (b + 1) := mul_le_mul_of_nonneg_right h hb_plus.le
    linarith
  exact div_le_div_of_nonneg_right h_num hb.le

/-- **Even-money specialisation.** At `b = 1` (1:1 payoff), Kelly
reduces to `f* = 2p - 1`. -/
@[stat_lemma]
theorem kellyFraction_unit_odds (p : ℝ) :
    kellyFraction p 1 = 2 * p - 1 := by
  unfold kellyFraction; ring

end Pythia.Finance
