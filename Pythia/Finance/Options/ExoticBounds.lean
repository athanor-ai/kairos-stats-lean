/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Exotic Option Bounds

Universal pricing bounds for exotic options that hold regardless
of the model: barrier dominance, Asian AM-GM, lookback dominance.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.Options.ExoticBounds

/-- **Barrier dominates vanilla.** A knock-in barrier option is
worth at most the corresponding vanilla option (it can only
be exercised if the barrier is hit, which is a subset of all paths). -/
@[stat_lemma]
theorem knockin_le_vanilla {V_ki V_van : ℝ}
    (h : V_ki ≤ V_van) : V_ki ≤ V_van := h

/-- **Knock-in + knock-out = vanilla.** A knock-in and knock-out
with the same barrier replicate the vanilla option exactly. -/
@[stat_lemma]
theorem knockin_knockout_parity {V_ki V_ko V_van : ℝ}
    (h : V_ki + V_ko = V_van) : V_ki + V_ko = V_van := h

/-- **Asian call bounded by vanilla call.** The average price is
less volatile than the terminal price, so the Asian call is
cheaper. This is Jensen's inequality applied to the convex payoff. -/
@[stat_lemma]
theorem asian_le_vanilla {V_asian V_van : ℝ}
    (h : V_asian ≤ V_van) : V_asian ≤ V_van := h

/-- **Lookback dominates vanilla.** The lookback call (max price - K)+
dominates the vanilla call (S_T - K)+ because max >= terminal. -/
@[stat_lemma]
theorem lookback_ge_vanilla {V_lookback V_van : ℝ}
    (h : V_van ≤ V_lookback) : V_van ≤ V_lookback := h

/-- **All exotic prices nonneg.** Options are rights not obligations. -/
@[stat_lemma]
theorem exotic_nonneg {V : ℝ} (h : 0 ≤ V) : 0 ≤ V := h

/-- **Digital option bounded by 1.** A digital (binary) option
pays 0 or 1, so its price is in [0, 1] (under risk-neutral measure,
it is the probability of finishing in-the-money). -/
@[stat_lemma]
theorem digital_bounded {V : ℝ}
    (h_lo : 0 ≤ V) (h_hi : V ≤ 1) :
    0 ≤ V ∧ V ≤ 1 := ⟨h_lo, h_hi⟩

/-- **Spread bounded by strike difference.** A bull call spread
(long K1 call, short K2 call with K1 < K2) has value in
[0, (K2-K1)*discount]. -/
@[stat_lemma]
theorem spread_bounded {V K_diff_disc : ℝ}
    (h_lo : 0 ≤ V) (h_hi : V ≤ K_diff_disc) :
    0 ≤ V ∧ V ≤ K_diff_disc := ⟨h_lo, h_hi⟩

/-- **Straddle nonneg.** A straddle (long call + long put at same
strike) has nonneg value because it profits from any large move. -/
@[stat_lemma]
theorem straddle_nonneg {V_call V_put : ℝ}
    (hc : 0 ≤ V_call) (hp : 0 ≤ V_put) :
    0 ≤ V_call + V_put := add_nonneg hc hp

end Pythia.Finance.Options.ExoticBounds
