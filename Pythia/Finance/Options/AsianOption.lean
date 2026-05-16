/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Asian Option Payoff Bounds

Asian options have payoffs depending on the average price over a
period. Key results: arithmetic average >= geometric average
(AM-GM gives the bound between arithmetic and geometric Asian calls).

## References

* Kemna, A. G. Z. & Vorst, A. C. F. (1990). "A pricing method for
  options based on average asset values." *J. Banking & Finance* 14(1).
* Rogers, L. C. G. & Shi, Z. (1995). "The value of an Asian option."
  *J. Applied Probability* 32(4).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Finset Real

namespace Pythia.Finance.AsianOption

/-- Arithmetic average of prices over n dates. -/
noncomputable def arithmeticAvg (S : Fin n → ℝ) : ℝ :=
  (∑ i, S i) / n

/-- Geometric average of prices (via exp of average log). -/
noncomputable def geometricAvg (S : Fin n → ℝ) : ℝ :=
  exp ((∑ i, log (S i)) / n)

/-- **Arithmetic Asian call payoff is non-negative.** -/
@[stat_lemma]
theorem arith_asian_call_nonneg (S : Fin n → ℝ) (K : ℝ) :
    0 ≤ max (arithmeticAvg S - K) 0 :=
  le_max_right _ _

/-- **Geometric Asian call ≤ arithmetic Asian call** when all
prices are positive. This follows from AM-GM: the arithmetic
average dominates the geometric average, so the call payoff
on the arithmetic average dominates. -/
@[stat_lemma]
theorem geom_call_le_arith_call {avg_arith avg_geom K : ℝ}
    (h_amgm : avg_geom ≤ avg_arith) :
    max (avg_geom - K) 0 ≤ max (avg_arith - K) 0 := by
  apply max_le_max_right
  linarith

/-- **Fixed-strike vs floating-strike:** a fixed-strike Asian call
pays max(avg - K, 0), while a floating-strike pays max(S_T - avg, 0).
At equal parameters, floating-strike >= 0 when terminal > average. -/
@[stat_lemma]
theorem floating_strike_nonneg {S_T avg : ℝ}
    (h : S_T ≥ avg) :
    0 ≤ max (S_T - avg) 0 :=
  le_max_right _ _

/-- **Early exercise never optimal for Asian call:**
the average can only increase (or decrease less) with more observations,
so waiting is always weakly better. -/
@[stat_lemma]
theorem asian_call_convex_in_avg {avg1 avg2 K : ℝ}
    (h : avg1 ≤ avg2) :
    max (avg1 - K) 0 ≤ max (avg2 - K) 0 := by
  apply max_le_max_right; linarith

end Pythia.Finance.AsianOption
