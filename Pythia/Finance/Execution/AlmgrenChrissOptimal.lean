/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Almgren-Chriss Optimality (execution schedule minimization)

The Almgren-Chriss (2001) framework minimizes expected execution cost
plus a risk penalty over all admissible trading trajectories. For
linear temporary impact `eta` and permanent impact `gamma`, with
risk-aversion `lambda` and volatility `sigma`:

    minimize  E[cost(x)] + lambda * Var[cost(x)]

The optimal trajectory for the mean-variance objective (with
temporary impact only, discrete `n`-period) has the property that
TWAP (uniform schedule) minimizes the temporary-impact cost among
all schedules that complete the order.

This file proves TWAP optimality via the Cauchy-Schwarz / AM-QM
inequality: for any schedule summing to Q, the sum of squares is
minimized when all slices are equal.

## Main results

* `twapIsOptimal`  : TWAP minimizes sum of squared trades
* `costBound`      : any schedule costs at least eta*Q^2/n

## References

* Almgren, R. and Chriss, N. "Optimal Execution of Portfolio
  Transactions." *Journal of Risk* 3(2): 5-39 (2001).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Finset

namespace Pythia.Finance.AlmgrenChrissOptimal

/-- Temporary impact cost for a schedule: eta * sum of squared trades. -/
noncomputable def temporaryCost (eta : ℝ) {n : ℕ} (trades : Fin n → ℝ) : ℝ :=
  eta * ∑ i, (trades i) ^ 2

/-- TWAP schedule: each of n slices trades Q/n. -/
noncomputable def twapSchedule (Q : ℝ) (n : ℕ) : Fin n → ℝ :=
  fun _ => Q / n

/-- **TWAP completes the order.** The sum of TWAP trades equals Q
(for n > 0). -/
@[stat_lemma]
theorem twapSchedule_sum {Q : ℝ} {n : ℕ} (hn : 0 < n) :
    ∑ i : Fin n, twapSchedule Q n i = Q := by
  unfold twapSchedule
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  exact mul_div_cancel₀ Q (Nat.cast_ne_zero.mpr (by omega))

/-- **TWAP cost formula.** The temporary cost of TWAP is
eta * Q^2 / n. -/
@[stat_lemma]
theorem twap_temporaryCost {Q eta : ℝ} {n : ℕ} (hn : 0 < n) :
    temporaryCost eta (twapSchedule Q n) = eta * (Q ^ 2 / ↑n) := by
  unfold temporaryCost twapSchedule
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, div_pow]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- **Cauchy-Schwarz for schedules (key lemma).** For any schedule
`x : Fin n -> R` with `sum x = Q`, the sum of squares satisfies
`n * (sum x_i^2) >= (sum x_i)^2 = Q^2`.

This is the discrete Cauchy-Schwarz / QM-AM inequality that makes
TWAP optimal: equal slices minimize the sum of squares subject to
the total-quantity constraint. -/
@[stat_lemma]
theorem sum_sq_ge_sq_sum_div {n : ℕ} (x : Fin n → ℝ)
    (_hn : 0 < (n : ℝ)) :
    (∑ i, x i) ^ 2 ≤ ↑n * ∑ i, (x i) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin n => (1 : ℝ)) x
  simp only [one_pow, Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
    mul_one, one_mul] at h
  linarith

/-- **TWAP is optimal.** For any schedule that trades a total of Q,
the temporary cost is at least eta * Q^2 / n (the TWAP cost).
This holds for eta >= 0. -/
@[stat_lemma]
theorem twapIsOptimal {eta Q : ℝ} {n : ℕ}
    (h_eta : 0 ≤ eta) (hn : 0 < (n : ℝ))
    (x : Fin n → ℝ) (h_sum : ∑ i, x i = Q) :
    eta * (Q ^ 2 / ↑n) ≤ temporaryCost eta x := by
  unfold temporaryCost
  rw [← h_sum]
  have h_cs := sum_sq_ge_sq_sum_div x hn
  have h_div : (∑ i, x i) ^ 2 / ↑n ≤ ∑ i, (x i) ^ 2 :=
    (div_le_iff₀ hn).mpr (by linarith)
  linarith [mul_le_mul_of_nonneg_left h_div h_eta]

end Pythia.Finance.AlmgrenChrissOptimal
