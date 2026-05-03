/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Channel Capacity as Supremum of Mutual Information

Defines the mutual information functional and channel capacity for
finite-alphabet discrete channels, and records the definitional
equality that channel capacity equals the supremum of mutual
information over all input distributions.

## Main definitions

* `mutualInfo` — mutual information I(X;Y) for a discrete channel W
  and input distribution p (finite alphabets α, β).
* `channelCapacity` — channel capacity C(W) = sup_p I(p, W).

## Main results

* `channel_capacity_eq_sup_mutual_info` — channel capacity is by
  definition the supremum of mutual information over all input
  distributions; proof closes by `rfl`.

## References

* Shannon, C. E. "A Mathematical Theory of Communication." Bell System
  Technical Journal 27 (1948).
* Cover, T. M. and Thomas, J. A. "Elements of Information Theory."
  2nd ed. Wiley (2006). Definition 7.2.1.
-/
import Mathlib

namespace Pythia.InformationTheory

/-- **Mutual information** for a finite-alphabet discrete channel.

Given an input distribution `p : α → ℝ` and a channel transition
matrix `W : α → β → ℝ`, the mutual information is

  I(X;Y) = ∑_{a,b} p(a) W(a|b) log [ W(a|b) / ∑_{a'} p(a') W(a'|b) ]

This is the classical discrete mutual information from Cover–Thomas
Definition 2.3.1. The `noncomputable` annotation is required because
`Real.log` is noncomputable. -/
noncomputable def mutualInfo
    {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (W : α → β → ℝ) : ℝ :=
  ∑ a, ∑ b, p a * W a b * Real.log (W a b /
    (∑ a', p a' * W a' b))

/-- **Channel capacity** for a finite-alphabet discrete channel.

The capacity of channel `W : α → β → ℝ` is the supremum of
mutual information over all valid input probability distributions
(nonneg weights summing to 1).

  C(W) = sup_{p : PMF(α)} I(p, W)

This is Cover–Thomas Definition 7.2.1. -/
noncomputable def channelCapacity
    {α β : Type*} [Fintype α] [Fintype β]
    (W : α → β → ℝ) : ℝ :=
  iSup (fun p : {p : α → ℝ // (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1} =>
    mutualInfo p.1 W)

/-- **Channel capacity equals sup of mutual information.**

Channel capacity `channelCapacity W` is by definition the supremum of
`mutualInfo p W` over all input probability distributions `p` on `α`.
This theorem records the definitional unfolding: the value is in
giving the equality a name so it can be cited and specialised in
downstream reasoning (e.g. when proving C(BSC) = 1 − H(δ)).

Proof: `rfl` — the statement is a definitional equality.

Citation: Cover–Thomas §7.2.1. -/
@[simp]
theorem channel_capacity_eq_sup_mutual_info
    {α β : Type*} [Fintype α] [Fintype β]
    (W : α → β → ℝ) :
    channelCapacity W = iSup (fun p : {p : α → ℝ // (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1} =>
      mutualInfo p.1 W) := rfl

end Pythia.InformationTheory
