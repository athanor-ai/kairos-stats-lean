/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pythia.InformationTheory.MutualInfo

Non-negativity of mutual information I(X;Y) ≥ 0.

## Main results

* `mutual_info_nonneg_via_gibbs` — parametrized form: given a
  Gibbs-inequality hypothesis, mutual information is nonneg.

## Design note

The full proof of I(X;Y) ≥ 0 reduces, via the log-sum inequality /
Gibbs inequality, to showing that the quantity

  ∑_{a,b} p(a) W(a|b) · log [ W(a|b) / (∑_{a'} p(a') W(a'|b)) ]

is nonneg — i.e., that a certain KL divergence between the joint
distribution and the product of its marginals is nonneg.  In
Mathlib v4.28.0 the relevant KL nonneg result is available for
`MeasureTheory.Measure`-based KL (`InformationTheory.klDiv`), but
lifting a finite double sum into that framework and unfolding the
`irreducible_def` of `klDiv` is several hundred lines.  We therefore
ship the honest-scaffold form: the statement is parametrized by the
Gibbs hypothesis, and the proof body is a definitional unfolding plus
`exact`.  A comment records exactly what would be needed for the
unconditional form so that it can be closed when Mathlib adds a
discrete finite-sum KL nonneg API.

## References

* Cover, T. M. and Thomas, J. A. "Elements of Information Theory."
  2nd ed. Wiley (2006). Theorem 2.4.1.
* Gibbs inequality: KL(p‖q) ≥ 0 with equality iff p = q a.s.
-/

import Mathlib
import Pythia.InformationTheory.ChannelCapacity

namespace Pythia.InformationTheory

/-- **Mutual information is non-negative (parametrized / Gibbs form).**

Given `h_gibbs : 0 ≤ ∑ a, ∑ b, p a * W a b * Real.log (W a b /
(∑ a', p a' * W a' b))`, we conclude `0 ≤ mutualInfo p W`.

The hypothesis `h_gibbs` is the Gibbs / log-sum inequality instantiated
to the finite double sum that equals `mutualInfo p W` by definition.
The proof is a one-line definitional unfolding: once you supply the
nonneg witness the conclusion is immediate from `unfold mutualInfo`.

To upgrade to the unconditional `mutual_info_nonneg` theorem one would
need a discrete-PMF instantiation of `InformationTheory.klDiv_nonneg`
(currently only available in the continuous measure-theoretic form in
Mathlib v4.28.0) together with the identification
  `mutualInfo p W = KL(p_XY ‖ p_X ⊗ p_Y)`
for the appropriate discrete measures.

Citation: Cover-Thomas §2.4.1. -/
theorem mutual_info_nonneg_via_gibbs
    {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (W : α → β → ℝ)
    (h_gibbs : 0 ≤ ∑ a : α, ∑ b : β,
        p a * W a b * Real.log (W a b / (∑ a' : α, p a' * W a' b))) :
    0 ≤ mutualInfo p W := by
  unfold mutualInfo
  exact h_gibbs

end Pythia.InformationTheory
