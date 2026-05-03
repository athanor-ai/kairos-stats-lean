/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bornhuetter-Ferguson IBNR Reserve Estimator: Unbiasedness

We formalize and prove the classical unbiasedness result for the
Bornhuetter-Ferguson (BF) incurred-but-not-reported (IBNR) reserving
estimator under the standard actuarial model.

## Model

For a single accident year with development periods `j ∈ Fin J`:
* `C j : Ω → ℝ` is cumulative paid claims at development period `j`.
* `q : Fin J → ℝ` is the (exogenously given) incremental payout pattern
  with `q j ∈ [0,1]` and `∑ j, q j = 1`.
* `Π_i : ℝ` is the a-priori expected ultimate loss.
* **Model assumption**: `E[C j] = Pi_i · ∑_{l ≤ j} q l` for each `j`.

## BF Estimator

The BF estimator for the outstanding reserve at development period `k` is:
  `R_BF(k) = Π_i · (1 - ∑_{l ≤ k} q l)`

## Main Result

`bornhuetter_ferguson_unbiased`: The BF estimator is unbiased, i.e.,
  `E[C(J-1) - C(k)] = R_BF(k)` for all development periods `k`.

The proof uses linearity of expectation and the model assumption, together
with the fact that the payout pattern sums to 1.

## References

* Bornhuetter, R.L. and Ferguson, R.E. (1972). "The actuary and IBNR".
* Wüthrich, M.V. and Merz, M. (2008). "Stochastic Claims Reserving Methods
  in Insurance", Chapter 2.
-/

import Mathlib

open MeasureTheory Finset

namespace Pythia

/-
In `Fin J`, the element `⟨J-1, _⟩` is the maximum, so `Finset.Iic` of it
equals `Finset.univ`.
-/
lemma fin_Iic_last (J : ℕ) (hJ : 0 < J) :
    Finset.Iic (⟨J - 1, by omega⟩ : Fin J) = Finset.univ := by
  grind +splitImp

/-
**Bornhuetter-Ferguson unbiasedness theorem.**

Under the standard actuarial model where `E[C j] = Π_i · ∑_{l ≤ j} q l`,
the BF reserve estimator `R_BF(k) = Π_i · (1 - ∑_{l ≤ k} q l)` is unbiased
for the true outstanding reserve `E[C(J-1) - C(k)]`.

This is a per-accident-year result; the theorem holds for arbitrary
(possibly non-zero) a-priori expectation `Pi_i`.
-/
theorem bornhuetter_ferguson_unbiased
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (J : ℕ) (hJ : 0 < J)
    (q : Fin J → ℝ)
    (h_q_bounded : ∀ j, 0 ≤ q j ∧ q j ≤ 1)
    (h_q_total : ∑ j : Fin J, q j = 1)
    (Pi_i : ℝ)
    (C : Fin J → Ω → ℝ)
    (hC_int : ∀ j, Integrable (C j) μ)
    (h_model : ∀ j : Fin J, ∫ ω, C j ω ∂μ =
      Pi_i * ∑ l ∈ Finset.Iic j, q l) :
    ∀ k : Fin J,
      ∫ ω, (C ⟨J - 1, by omega⟩ ω - C k ω) ∂μ =
        Pi_i * (1 - ∑ l ∈ Finset.Iic k, q l) := by
  intro k
  have h_sum : ∑ l ∈ Finset.univ, q l = 1 := by
    exact h_q_total;
  rw [ MeasureTheory.integral_sub ( hC_int _ ) ( hC_int _ ), h_model, h_model ];
  rw [ ← mul_sub, ← h_sum, show ( Finset.Iic ⟨ J - 1, Nat.sub_lt hJ zero_lt_one ⟩ : Finset ( Fin J ) ) = Finset.univ from Finset.eq_univ_of_forall fun x => Finset.mem_Iic.2 ( Nat.le_pred_of_lt x.is_lt ) ]

end Pythia