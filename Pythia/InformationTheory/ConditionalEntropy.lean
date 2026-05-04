/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pythia.InformationTheory.ConditionalEntropy

Conditional entropy for finite discrete distributions and the
fundamental inequality **conditioning reduces entropy**: `H(X|Y) ≤ H(X)`.

## Main definitions

* `jointEntropy pXY` — joint Shannon entropy `H(X,Y) = ∑_{a,b} negMulLog(pXY(a,b))`.
* `marginalY pXY` — marginal `p_Y(b) = ∑_a pXY(a,b)`.
* `condEntropy pXY` — conditional entropy `H(X|Y) = H(X,Y) − H(Y)`.

## Main results

* `condEntropy_le_entropy` — conditioning reduces entropy:
  `H(X|Y) ≤ H(X)`, equivalently `I(X;Y) ≥ 0`.
  Follows from Gibbs' inequality / KL non-negativity.

## References

* Cover, T. M. and Thomas, J. A. "Elements of Information Theory."
  2nd ed. Wiley (2006). Theorem 2.6.5.
-/

import Mathlib
import Pythia.InformationTheory.KLChainRule

open Finset BigOperators

namespace Pythia.InformationTheory

/-- Shannon entropy for a distribution over a finite type. -/
noncomputable def entropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  ∑ a : α, Real.negMulLog (p a)

/-- Joint Shannon entropy `H(X,Y) = ∑_{a,b} negMulLog(pXY(a,b))`. -/
noncomputable def jointEntropy {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) : ℝ :=
  ∑ ab : α × β, Real.negMulLog (pXY ab)

/-- Marginal distribution over `α` from a joint distribution on `α × β`. -/
noncomputable def marginalX {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) : α → ℝ :=
  fun a => ∑ b : β, pXY (a, b)

/-- Marginal distribution over `β` from a joint distribution on `α × β`. -/
noncomputable def marginalY {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) : β → ℝ :=
  fun b => ∑ a : α, pXY (a, b)

/-- Conditional entropy `H(X|Y) = H(X,Y) − H(Y)`.

This is defined as the difference of joint entropy and marginal entropy,
which equals `−∑_{a,b} pXY(a,b) · log(pXY(a,b) / pY(b))` for valid
joint distributions. -/
noncomputable def condEntropy {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) : ℝ :=
  jointEntropy pXY - entropy (marginalY pXY)

/-
**Conditioning reduces entropy** (Cover–Thomas, Theorem 2.6.5):
`H(X|Y) ≤ H(X)`.

Equivalently, mutual information `I(X;Y) = H(X) − H(X|Y) ≥ 0`.

This is proved via Gibbs' inequality: `I(X;Y) = KL(pXY ‖ pX ⊗ pY) ≥ 0`.

The proof proceeds by showing:
  `H(X) − H(X|Y) = H(X) − (H(X,Y) − H(Y))`
  `= H(X) + H(Y) − H(X,Y)`
  `= ∑_{a,b} pXY(a,b) log(pXY(a,b) / (pX(a) · pY(b)))`
  `= KL(pXY ‖ pX ⊗ pY) ≥ 0`.

Hypothesis `h_kl_nonneg` packages the KL non-negativity of the
joint vs. product-of-marginals, which follows from `klFinite_nonneg`.
-/
theorem condEntropy_le_entropy {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ)
    (h_nonneg : ∀ ab, 0 ≤ pXY ab)
    (_h_sum : ∑ ab : α × β, pXY ab = 1)
    (h_kl_nonneg :
      0 ≤ klFinite pXY (prodDist (marginalX pXY) (marginalY pXY))) :
    condEntropy pXY ≤ entropy (marginalX pXY) := by
  unfold condEntropy entropy;
  unfold klFinite prodDist at h_kl_nonneg;
  -- Let's simplify the expression for the KL divergence.
  have h_kl_simplified : ∑ a, pXY a * Real.log (pXY a / (marginalX pXY a.1 * marginalY pXY a.2)) = ∑ a, pXY a * Real.log (pXY a) - ∑ a, pXY a * Real.log (marginalX pXY a.1) - ∑ a, pXY a * Real.log (marginalY pXY a.2) := by
    rw [ ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib ];
    refine' Finset.sum_congr rfl fun x _ => _;
    by_cases hx : pXY x = 0 <;> by_cases hx' : marginalX pXY x.1 = 0 <;> by_cases hx'' : marginalY pXY x.2 = 0 <;> simp +decide [ *, Real.log_div, Real.log_mul ] ; ring;
    · exact absurd hx' ( ne_of_gt ( lt_of_lt_of_le ( lt_of_le_of_ne ( h_nonneg x ) ( Ne.symm hx ) ) ( Finset.single_le_sum ( fun a _ => h_nonneg ( x.1, a ) ) ( Finset.mem_univ x.2 ) ) ) );
    · exact absurd hx' ( ne_of_gt ( lt_of_lt_of_le ( lt_of_le_of_ne ( h_nonneg x ) ( Ne.symm hx ) ) ( Finset.single_le_sum ( fun a _ => h_nonneg ( x.1, a ) ) ( Finset.mem_univ x.2 ) ) ) );
    · exact absurd hx'' ( ne_of_gt ( lt_of_lt_of_le ( lt_of_le_of_ne ( h_nonneg x ) ( Ne.symm hx ) ) ( Finset.single_le_sum ( fun a _ => h_nonneg ( a, x.2 ) ) ( Finset.mem_univ x.1 ) ) ) );
    · ring;
  -- Let's simplify the expression for the marginal entropies.
  have h_marginalX : ∑ a, pXY a * Real.log (marginalX pXY a.1) = ∑ a, marginalX pXY a * Real.log (marginalX pXY a) := by
    simp +decide [ marginalX, Finset.sum_mul _ _ _ ];
    exact Fintype.sum_prod_type fun x => pXY x * Real.log (∑ b, pXY (x.1, b))
  have h_marginalY : ∑ a, pXY a * Real.log (marginalY pXY a.2) = ∑ b, marginalY pXY b * Real.log (marginalY pXY b) := by
    simp +decide [ marginalY, Finset.sum_mul _ _ _ ];
    rw [ Finset.sum_comm ];
    rw [ Finset.sum_sigma' ];
    refine' Finset.sum_bij ( fun x _ => ⟨ x.1, x.2 ⟩ ) _ _ _ _ <;> simp +decide;
  unfold jointEntropy; simp_all +decide [ Real.negMulLog ] ; linarith;

end Pythia.InformationTheory