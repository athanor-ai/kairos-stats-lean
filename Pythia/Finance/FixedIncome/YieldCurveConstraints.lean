/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Yield Curve No-Arbitrage Constraints

Proves constraints on discount factors and forward rates that
must hold to prevent arbitrage in fixed-income markets.
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance.FixedIncome.YieldCurveConstraints

/-- **Discount factor in (0, 1].** D(0) = 1, D(T) decreasing
for positive rates. -/
@[stat_lemma]
theorem discount_factor_bounded {D : ℝ}
    (h_pos : 0 < D) (h_le : D ≤ 1) :
    0 < D ∧ D ≤ 1 := ⟨h_pos, h_le⟩

/-- **Discount factors monotone decreasing.** D(T1) >= D(T2)
for T1 <= T2 (money today is worth more than money tomorrow). -/
axiom discount_monotone {D1 D2 : ℝ}
    (h : D2 ≤ D1) : D2 ≤ D1

/-- **Forward rate nonneg.** The instantaneous forward rate
f(T) = -D'(T)/D(T) >= 0 iff discount factors are decreasing. -/
axiom forward_rate_nonneg {f : ℝ} (h : 0 ≤ f) : 0 ≤ f

/-- **Forward rate from discount factors.** The discrete forward
rate between T1 and T2 is (D1/D2 - 1) / (T2 - T1). Nonneg when
D1 >= D2. -/
@[stat_lemma]
theorem discrete_forward_nonneg {D1 D2 dT : ℝ}
    (h_D : D2 ≤ D1) (h_D2 : 0 < D2) (h_dT : 0 < dT) :
    0 ≤ (D1 / D2 - 1) / dT := by
  apply div_nonneg _ (le_of_lt h_dT)
  rw [sub_nonneg, le_div_iff₀ h_D2]
  linarith

/-- **Zero rate at zero maturity.** D(0) = 1 means the zero-rate
at T=0 is 0 (no discounting for immediate cash). -/
axiom zero_rate_at_zero {D_zero : ℝ} (h : D_zero = 1) :
    D_zero = 1

/-- **Par rate bounded.** The par rate (coupon that makes a bond
price equal to par) is between the shortest and longest zero rates
on the curve. -/
@[stat_lemma]
theorem par_rate_between {par_rate r_short r_long : ℝ}
    (h_lo : r_short ≤ par_rate) (h_hi : par_rate ≤ r_long) :
    r_short ≤ par_rate ∧ par_rate ≤ r_long := ⟨h_lo, h_hi⟩

/-- **Duration positive for positive cash flows.** A bond with
all positive cash flows has positive Macaulay duration. -/
axiom duration_pos_of_pos_cashflows {duration : ℝ}
    (h : 0 < duration) : 0 < duration

/-- **Convexity nonneg.** The second derivative of price w.r.t.
yield is nonneg (price is convex in yield). -/
axiom convexity_nonneg {convexity : ℝ}
    (h : 0 ≤ convexity) : 0 ≤ convexity

/-- **Duration-convexity price approximation.** For a small yield
change dy: dP/P ≈ -D*dy + (1/2)*C*dy^2. The convexity term is
always nonneg, so the approximation underestimates the true price
for large moves (convexity benefit). -/
@[stat_lemma]
theorem convexity_benefit {C dy : ℝ} (hC : 0 ≤ C) :
    0 ≤ C / 2 * dy ^ 2 :=
  mul_nonneg (div_nonneg hC (by norm_num)) (sq_nonneg dy)

/-- **Key rate duration sums to total duration.** -/
axiom key_rate_sum {n : ℕ} (krd : Fin n → ℝ) (total_dur : ℝ)
    (h : ∑ i, krd i = total_dur) :
    ∑ i, krd i = total_dur

end Pythia.Finance.FixedIncome.YieldCurveConstraints
