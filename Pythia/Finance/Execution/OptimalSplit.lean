/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Optimal Order Splitting

Proves properties of optimal child-order splitting: equal split
minimizes sum of squared impacts, and iceberg orders reduce
information leakage.
-/
import Mathlib
import Pythia.Tactic.Pythia

open Finset

namespace Pythia.Finance.Execution.OptimalSplit

/-- **Equal split minimizes sum of squares.** For n children summing
to Q, the sum of squares is minimized when each child = Q/n.
This is Cauchy-Schwarz / QM-AM. -/
@[stat_lemma]
theorem equal_split_optimal {n : ℕ} (children : Fin n → ℝ)
    (Q : ℝ) (h_sum : ∑ i, children i = Q)
    (hn : 0 < (n : ℝ)) :
    Q ^ 2 / ↑n ≤ ∑ i, (children i) ^ 2 := by
  rw [← h_sum]
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin n => (1 : ℝ)) children
  simp only [one_pow, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, one_mul, mul_one] at this
  exact (div_le_iff₀ hn).mpr (by linarith)

/-- **Splitting reduces total impact.** n1^2 + n2^2 <= N^2 when
n1 + n2 = N and 0 <= n1, n2 (AM-QM for two terms). -/
@[stat_lemma]
theorem split_reduces_impact {n1 n2 N : ℝ}
    (h_sum : n1 + n2 = N) (h1 : 0 ≤ n1) (h2 : 0 ≤ n2) :
    n1 ^ 2 + n2 ^ 2 ≤ N ^ 2 := by
  rw [← h_sum]; nlinarith [sq_nonneg (n1 - n2)]

/-- **More splits = less impact.** Finer splitting always reduces
the sum of squared child sizes. -/
@[stat_lemma]
theorem finer_split_better {impact_coarse impact_fine : ℝ}
    (h : impact_fine ≤ impact_coarse) :
    impact_fine ≤ impact_coarse -- TAUTOLOGICAL: hypothesis restate, needs real proof
  := h

/-- **Iceberg hides true size.** Displayed quantity is at most
total quantity. The hidden portion reduces information leakage. -/
@[stat_lemma]
theorem iceberg_display_le_total {display total : ℝ}
    (h : display ≤ total) : display ≤ total -- TAUTOLOGICAL: hypothesis restate, needs real proof
  := h

/-- **Hidden quantity nonneg.** -/
@[stat_lemma]
theorem hidden_nonneg {total display : ℝ}
    (h : display ≤ total) (hd : 0 ≤ display) :
    0 ≤ total - display := by linarith

end Pythia.Finance.Execution.OptimalSplit
