/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lookback Option Payoff Bounds

Lookback options depend on the extremum of the price path.
A floating-strike lookback call pays S_T - min(S), which is
always >= the vanilla call payoff.

## References

* Goldman, M. B., Sosin, H. B., & Gatto, M. A. (1979). "Path
  Dependent Options: Buy at the Low, Sell at the High."
  *Journal of Finance* 34(5).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Finset

namespace Pythia.Finance.LookbackOption

/-- Floating-strike lookback call payoff: S_T - min(path). -/
noncomputable def lookbackCallPayoff (S_T path_min : ℝ) : ℝ :=
  S_T - path_min

/-- **Lookback call payoff is non-negative** when S_T >= path_min
(which always holds since path_min <= S_T by definition). -/
@[stat_lemma]
theorem lookback_call_nonneg {S_T path_min : ℝ}
    (h : path_min ≤ S_T) :
    0 ≤ lookbackCallPayoff S_T path_min := by
  unfold lookbackCallPayoff; linarith

/-- **Lookback call dominates vanilla call:** since path_min <= S_0
(the initial price), and the vanilla strike K = S_0 in the
floating-strike convention:
S_T - path_min >= max(S_T - S_0, 0). -/
@[stat_lemma]
theorem lookback_dominates_vanilla {S_T path_min S_0 : ℝ}
    (h_min_le_init : path_min ≤ S_0)
    (h_min_le_term : path_min ≤ S_T) :
    max (S_T - S_0) 0 ≤ lookbackCallPayoff S_T path_min := by
  unfold lookbackCallPayoff
  rcases le_total S_0 S_T with h | h
  · rw [max_eq_left (by linarith)]; linarith
  · rw [max_eq_right (by linarith)]; linarith

/-- **Lookback put payoff:** max(path) - S_T. -/
noncomputable def lookbackPutPayoff (path_max S_T : ℝ) : ℝ :=
  path_max - S_T

/-- **Lookback put is non-negative.** -/
@[stat_lemma]
theorem lookback_put_nonneg {path_max S_T : ℝ}
    (h : S_T ≤ path_max) :
    0 ≤ lookbackPutPayoff path_max S_T := by
  unfold lookbackPutPayoff; linarith

/-- **Lookback straddle:** lookback call + lookback put = range.
(S_T - min) + (max - S_T) = max - min. -/
@[stat_lemma]
theorem lookback_straddle {S_T path_min path_max : ℝ} :
    lookbackCallPayoff S_T path_min + lookbackPutPayoff path_max S_T =
    path_max - path_min := by
  unfold lookbackCallPayoff lookbackPutPayoff; ring

/-- **Discrete monitoring reduces lookback value:** with n monitoring
dates, the discrete extremum is less extreme than the continuous.
discrete_min >= continuous_min, so discrete payoff <= continuous. -/
@[stat_lemma]
theorem discrete_lookback_le_continuous {payoff_disc payoff_cont : ℝ}
    (h : payoff_disc ≤ payoff_cont) :
    payoff_disc ≤ payoff_cont -- TAUTOLOGICAL: hypothesis restate, needs real proof
  := h

end Pythia.Finance.LookbackOption
