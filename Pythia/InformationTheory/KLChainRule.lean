/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pythia.InformationTheory.KLChainRule

**KL-divergence chain rule for product distributions**: if `p₁ ⊗ p₂`
and `q₁ ⊗ q₂` are product PMFs over a product type `α × β`, then

  `KL(p₁⊗p₂ ‖ q₁⊗q₂) = KL(p₁ ‖ q₁) + KL(p₂ ‖ q₂)`.

## Main definitions

* `prodDist p₁ p₂` — the product distribution `(a, b) ↦ p₁ a · p₂ b`.

## Main results

* `klFinite_prod` — the KL chain rule for independent factors.

## Proof strategy

Expand `log` of a product into a sum of logs, then factor the double
sum into the product of single sums using `∑ p₁ = 1`, `∑ p₂ = 1`.

## References

* Cover, T. M. and Thomas, J. A. "Elements of Information Theory."
  2nd ed. Wiley (2006). Theorem 2.7.3.
-/

import Mathlib
import Pythia.InformationTheory.GibbsInequality

open Finset BigOperators

namespace Pythia.InformationTheory

/-- Product distribution from two marginals. -/
noncomputable def prodDist {α β : Type*} (p₁ : α → ℝ) (p₂ : β → ℝ) :
    α × β → ℝ :=
  fun ab => p₁ ab.1 * p₂ ab.2

/-
**KL-divergence chain rule for product distributions**
(Cover–Thomas, Theorem 2.7.3).

For product PMFs `p₁⊗p₂` and `q₁⊗q₂` over `α × β`:
  `KL(p₁⊗p₂ ‖ q₁⊗q₂) = KL(p₁‖q₁) + KL(p₂‖q₂)`.

**Proof.** Each term of the double sum factors as
  `p₁(a)p₂(b) · log((p₁(a)p₂(b))/(q₁(a)q₂(b)))`
  = `p₁(a)p₂(b) · [log(p₁(a)/q₁(a)) + log(p₂(b)/q₂(b))]`.
Distributing and summing, the cross terms factor:
  `∑_{a,b} p₁(a)p₂(b) log(p₁(a)/q₁(a))`
  = `[∑_b p₂(b)] · [∑_a p₁(a) log(p₁(a)/q₁(a))]`
  = `1 · KL(p₁‖q₁)`,
and symmetrically for the other term.
-/
theorem klFinite_prod {α β : Type*} [Fintype α] [Fintype β]
    (p₁ : α → ℝ) (p₂ : β → ℝ) (q₁ : α → ℝ) (q₂ : β → ℝ)
    (hp₁_nonneg : ∀ a, 0 ≤ p₁ a) (hp₂_nonneg : ∀ b, 0 ≤ p₂ b)
    (hq₁_nonneg : ∀ a, 0 ≤ q₁ a) (hq₂_nonneg : ∀ b, 0 ≤ q₂ b)
    (hp₁_sum : ∑ a, p₁ a = 1) (hp₂_sum : ∑ b, p₂ b = 1)
    (hq₁_sum : ∑ a, q₁ a = 1) (hq₂_sum : ∑ b, q₂ b = 1)
    (h_ac₁ : ∀ a, 0 < p₁ a → 0 < q₁ a)
    (h_ac₂ : ∀ b, 0 < p₂ b → 0 < q₂ b) :
    klFinite (prodDist p₁ p₂) (prodDist q₁ q₂) =
      klFinite p₁ q₁ + klFinite p₂ q₂ := by
  -- Split the KL-divergence into the sum of two KL-divergences.
  have h_split : klFinite (prodDist p₁ p₂) (prodDist q₁ q₂) = ∑ a, ∑ b, p₁ a * p₂ b * (Real.log (p₁ a / q₁ a) + Real.log (p₂ b / q₂ b)) := by
    rw [ ← Finset.sum_product' ];
    refine' Finset.sum_congr rfl fun x _ => _;
    by_cases hx₁ : p₁ x.1 = 0 <;> by_cases hx₂ : p₂ x.2 = 0 <;> simp +decide [ *, prodDist ];
    rw [ ← Real.log_mul ( div_ne_zero hx₁ ( ne_of_gt ( h_ac₁ _ ( lt_of_le_of_ne ( hp₁_nonneg _ ) ( Ne.symm hx₁ ) ) ) ) ) ( div_ne_zero hx₂ ( ne_of_gt ( h_ac₂ _ ( lt_of_le_of_ne ( hp₂_nonneg _ ) ( Ne.symm hx₂ ) ) ) ) ), mul_div_mul_comm ];
  simp_all +decide [ mul_add, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, Finset.sum_add_distrib ];
  simp +decide only [← Finset.mul_sum _ _ _, ← sum_mul, hp₂_sum];
  simp +decide [ hp₁_sum, hp₂_sum, klFinite ]

end Pythia.InformationTheory