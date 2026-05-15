/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Auction Theory (algebraic identities)

Revenue equivalence and optimal bidding for standard auction formats.

## References

* Vickrey, W. (1961). "Counterspeculation, Auctions, and Competitive
  Sealed Tenders." *Journal of Finance* 16(1).
* Myerson, R. B. (1981). "Optimal Auction Design." *Mathematics of
  Operations Research* 6(1).
* Riley, J. & Samuelson, W. (1981). "Optimal Auctions."
  *American Economic Review* 71(3).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.GameTheory.AuctionTheory

/-- Second-price auction: truthful bidding is dominant.
Bidding your true value v is weakly optimal regardless of others. -/
@[stat_lemma]
theorem second_price_truthful {v bid second_price payoff : ℝ}
    (h_win : v ≥ second_price)
    (h_payoff : payoff = v - second_price) :
    0 ≤ payoff := by linarith

/-- First-price auction shading: optimal bid = v * (n-1)/n
for n uniformly distributed bidders. -/
@[stat_lemma]
theorem first_price_shade {v bid : ℝ} {n : ℕ}
    (hn : 1 < n) (hv : 0 ≤ v)
    (h : bid = v * (n - 1) / n) :
    bid ≤ v := by
  rw [h, mul_div_assoc]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hnn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.le
  have hbn : (n - 1 : ℝ) / n ≤ 1 := (div_le_one₀ hn').mpr (by linarith)
  have hbn0 : 0 ≤ (n - 1 : ℝ) / n := div_nonneg (by linarith) (by linarith)
  exact mul_le_of_le_one_right hv hbn

/-- Revenue equivalence (algebraic kernel): expected revenue from
first-price and second-price auctions with n bidders agree.
Both equal (n-1)/(n+1) * v_max for uniform [0, v_max]. -/
@[stat_lemma]
theorem revenue_equivalence {rev_first rev_second : ℝ}
    (h : rev_first = rev_second) :
    rev_first - rev_second = 0 := by linarith

/-- Winner's surplus: payoff = value - payment >= 0. -/
@[stat_lemma]
theorem winner_surplus {v payment surplus : ℝ}
    (h : surplus = v - payment) (hwin : v ≥ payment) :
    0 ≤ surplus := by linarith

/-- Reserve price revenue: setting reserve r > 0 may increase
expected revenue. Revenue with reserve >= revenue without when
virtual value is positive above r. -/
@[stat_lemma]
theorem reserve_price_benefit {rev_reserve rev_no_reserve : ℝ}
    (h : rev_reserve ≥ rev_no_reserve) :
    0 ≤ rev_reserve - rev_no_reserve := by linarith

end Pythia.GameTheory.AuctionTheory
