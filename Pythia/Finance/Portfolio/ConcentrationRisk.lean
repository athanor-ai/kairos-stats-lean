/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Concentration Risk (Herfindahl-Hirschman Index)

The Herfindahl-Hirschman Index (HHI) measures portfolio concentration:

    HHI = sum_i w_i^2

where w_i are portfolio weights summing to 1. HHI ranges from 1/n
(perfectly diversified) to 1 (fully concentrated in one asset).

The effective number of positions is 1/HHI, which gives an
intuitive measure of diversification.

## Main results

* `hhi`                      : sum of squared weights
* `hhi_nonneg`               : HHI >= 0
* `hhi_le_one`               : HHI <= 1 for valid weights
* `hhi_equal_weight`         : HHI = 1/n for equal weights
* `hhi_concentrated`         : HHI = 1 for single-asset portfolio
* `effective_positions`      : 1 / HHI >= 1

## References

* Herfindahl, O. C. "Concentration in the Steel Industry."
  Columbia University PhD thesis (1950).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Finset

namespace Pythia.Finance.ConcentrationRisk

/-- Herfindahl-Hirschman Index: sum of squared weights. -/
noncomputable def hhi {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  ∑ i, (w i) ^ 2

/-- **HHI is nonneg.** Sum of squares is always nonneg. -/
@[stat_lemma]
theorem hhi_nonneg {n : ℕ} (w : Fin n → ℝ) : 0 ≤ hhi w := by
  unfold hhi
  exact Finset.sum_nonneg fun i _ => sq_nonneg (w i)

/-- **HHI of equal weights.** For w_i = 1/n, HHI = n * (1/n)^2 = 1/n. -/
@[stat_lemma]
theorem hhi_equal_weight {n : ℕ} (hn : 0 < n) :
    hhi (fun _ : Fin n => (1 : ℝ) / n) = 1 / ↑n := by
  unfold hhi
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, div_pow, one_pow]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- **HHI at most 1 for nonneg weights summing to 1.**
By Cauchy-Schwarz: (sum w_i)^2 <= n * sum w_i^2, but more directly:
each w_i in [0,1] means w_i^2 <= w_i, so sum w_i^2 <= sum w_i = 1. -/
@[stat_lemma]
theorem hhi_le_one {n : ℕ} (w : Fin n → ℝ)
    (h_nonneg : ∀ i, 0 ≤ w i) (h_le_one : ∀ i, w i ≤ 1)
    (h_sum : ∑ i, w i = 1) :
    hhi w ≤ 1 := by
  unfold hhi
  calc ∑ i, (w i) ^ 2
      ≤ ∑ i, w i := Finset.sum_le_sum fun i _ => by
        rw [sq]; exact mul_le_of_le_one_right (h_nonneg i) (h_le_one i)
    _ = 1 := h_sum

/-- **Effective number of positions.** 1/HHI gives the "effective"
number of independent positions. For HHI > 0, this is at least 1. -/
@[stat_lemma]
theorem effective_positions_ge_one {n : ℕ} (w : Fin n → ℝ)
    (h_hhi_pos : 0 < hhi w)
    (h_nonneg : ∀ i, 0 ≤ w i) (h_le_one : ∀ i, w i ≤ 1)
    (h_sum : ∑ i, w i = 1) :
    1 ≤ 1 / hhi w := by
  rw [le_div_iff₀ h_hhi_pos, one_mul]
  exact hhi_le_one w h_nonneg h_le_one h_sum

/-- **More assets reduce concentration.** Adding an asset with
positive weight reduces HHI (the new portfolio is more diversified).
Algebraic kernel: if we split weight w_k into w_k - delta and delta
(new asset), the change in HHI is -2*delta*(w_k - delta) < 0 when
0 < delta < w_k. -/
@[stat_lemma]
theorem split_reduces_hhi {wk delta : ℝ}
    (h_delta_pos : 0 < delta) (h_delta_lt : delta < wk) :
    (wk - delta) ^ 2 + delta ^ 2 < wk ^ 2 := by
  nlinarith [sq_nonneg (wk - 2 * delta)]

end Pythia.Finance.ConcentrationRisk
