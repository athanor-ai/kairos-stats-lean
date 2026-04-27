/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Mass-Action Conservation for a Single Reversible Reaction

For a reversible reaction `A ⇌ B`, the total moles `n_A(t) + n_B(t)` are
conserved over time. Given two snapshots `(nA0, nB0)` and `(nA1, nB1)` linked
by a reaction extent `xi` via `nA1 = nA0 - xi` and `nB1 = nB0 + xi`, we
conclude `nA0 + nB0 = nA1 + nB1`.

## Main results

* `mass_action_conservation_pair` : total moles are conserved under a single
  reversible stoichiometric step.

## Why this lemma

Mathlib has no named `mass_action` declaration in this per-reaction
stoichiometric form. The CRN abstraction in `Pythia/Bio/MassAction.lean` is a
separate, network-level object. This lemma captures the elementary conservation
identity that every reaction-extent calculation relies on.

The companion empirical layer (`tools/sim/chemistry_mass_action.py`) runs a
10 000-trial PBT, a deterministic sweep, and a mutation harness so customers
can verify the conservation identity holds across realistic mole and extent
ranges.

## References

* Guldberg, C. M. and Waage, P. "Studier over Affiniteten."
  *Forhandlinger Videnskabs-Selskabet i Christiania* (1864).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Chemistry

/-- **Mass-action conservation for a single reversible reaction.**
Given two snapshots `(nA0, nB0)` and `(nA1, nB1)` of mole amounts for
species A and B, and a reaction extent `xi` satisfying `nA1 = nA0 - xi`
and `nB1 = nB0 + xi`, the total moles are conserved:
`nA0 + nB0 = nA1 + nB1`. -/
@[stat_lemma]
theorem mass_action_conservation_pair {nA0 nB0 nA1 nB1 xi : ℝ}
    (hA : nA1 = nA0 - xi) (hB : nB1 = nB0 + xi) :
    nA0 + nB0 = nA1 + nB1 := by
  rw [hA, hB]; ring

end Pythia.Chemistry
