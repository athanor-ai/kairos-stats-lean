/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pythia.InformationTheory.GibbsInequality

**Gibbs' inequality**: the Kullback–Leibler divergence between two
finite probability mass functions is non-negative.

## Main definitions

* `klFinite p q` — KL divergence `∑ a, p a * log (p a / q a)` for
  discrete distributions over a finite type.

## Main results

* `klFinite_nonneg` — `KL(p ‖ q) ≥ 0` for valid PMFs with `q`
  absolutely continuous with respect to `p`.

## Proof strategy

Apply `Real.log_le_sub_one_of_pos` (i.e., `log t ≤ t − 1`) pointwise
to `t = q(a) / p(a)` and sum, using `∑ p = ∑ q = 1`.

## References

* Cover, T. M. and Thomas, J. A. "Elements of Information Theory."
  2nd ed. Wiley (2006). Theorem 2.6.3 (Information Inequality).
-/

import Mathlib

open Finset BigOperators

namespace Pythia.InformationTheory

/-- Finite KL divergence (relative entropy) between discrete distributions.
`klFinite p q = ∑ a, p(a) · log(p(a)/q(a))`. -/
noncomputable def klFinite {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ a : α, p a * Real.log (p a / q a)

/-
**Gibbs' inequality** (Cover–Thomas, Theorem 2.6.3):
the KL divergence between two valid PMFs is non-negative.

For `p, q : α → ℝ` with `p, q ≥ 0`, `∑ p = 1`, `∑ q = 1`, and
`q` absolutely continuous w.r.t. `p` (i.e., `p a > 0 → q a > 0`),
we have `KL(p ‖ q) = ∑ a, p a · log(p a / q a) ≥ 0`.

**Proof.** Since `log t ≤ t − 1` for all `t > 0`, we have for each `a`
with `p a > 0`:
  `−p a · log(q a / p a) ≥ −p a · (q a / p a − 1) = p a − q a`.
Summing over all `a` and using `∑ p = ∑ q = 1` gives `KL(p‖q) ≥ 0`.
-/
theorem klFinite_nonneg {α : Type*} [Fintype α]
    (p q : α → ℝ)
    (hp_nonneg : ∀ a, 0 ≤ p a)
    (hq_nonneg : ∀ a, 0 ≤ q a)
    (hp_sum : ∑ a, p a = 1)
    (hq_sum : ∑ a, q a = 1)
    (h_ac : ∀ a, 0 < p a → 0 < q a) :
    0 ≤ klFinite p q := by
  -- Since $\log t \leq t - 1$ for all $t > 0$, we have for each $a$ with $p a > 0$:
  have h_log_le : ∀ a, p a > 0 → p a * Real.log (p a / q a) ≥ p a - q a := by
    intro a ha; have := Real.log_le_sub_one_of_pos ( div_pos ( h_ac a ha ) ha ) ; rw [ Real.log_div ] at this <;> try linarith [ h_ac a ha ];
    rw [ Real.log_div ] <;> nlinarith [ h_ac a ha, mul_div_cancel₀ ( q a ) ha.ne' ];
  have h_sum_le : ∑ a, p a * Real.log (p a / q a) ≥ ∑ a, (p a - q a) := by
    exact Finset.sum_le_sum fun a _ => if ha : p a = 0 then by simp +decide [ ha, Real.log_zero, hp_nonneg, hq_nonneg ] else h_log_le a ( lt_of_le_of_ne ( hp_nonneg a ) ( Ne.symm ha ) );
  unfold klFinite; simp_all +decide [ Finset.sum_sub_distrib ] ;

end Pythia.InformationTheory