/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Condorcet Winner — Majority Characterization (Uniqueness Direction)

## Main results

* `condorcet_majority_disjointness` — Abstract cardinality lemma: two disjoint
  sets of voters cannot each constitute a strict majority of N.

* `condorcet_winner_majority_characterization` — If `a*` is a Condorcet
  winner (beats every other alternative by strict majority) and `pref` is
  asymmetric (no voter ranks both `a* > b` and `b > a*`), then no other
  alternative `b ≠ a*` can also beat `a*` by strict majority.

## Proof sketch

The two filtered sets
  `S  = {i : pref i a* b}`   (voters preferring a* over b)
  `T  = {i : pref i b a*}`   (voters preferring b over a*)
are disjoint by `h_disjoint`.  Hence
  card S + card T ≤ card univ = N.
But `hcondorcet` gives  card S * 2 > N,
and the negand claims      card T * 2 > N.
Adding: (card S + card T) * 2 > 2N, so card S + card T > N.
Contradiction.  `omega` closes after rewriting in natural-number arithmetic.

## Notes on `open Classical`

The spec's `hcondorcet` and the conclusion use `Finset.filter` on predicates
of the form `fun i : N => pref i a_star b`.  Lean's kernel requires a
`Decidable` instance for these predicates.  Rather than propagating a
cumbersome uncurried `DecidablePred` hypothesis, we open `Classical` locally,
which provides `Decidable` for every proposition and lets the statement compile
without restricting the class of preference relations.

## References

* Condorcet, M. de. *Essai sur l'application de l'analyse à la probabilité des
  décisions rendues à la pluralité des voix* (1785).
* Black, D. *The Theory of Committees and Elections*. Cambridge (1958).
* Nisan, Roughgarden, Tardos, Vazirani. *Algorithmic Game Theory* Ch. 10
  (Cambridge University Press, 2007).
-/
import Mathlib

namespace Pythia.MechanismDesign

/-- **Condorcet disjointness lemma (abstract form).**
Two disjoint finite sets of voters cannot each constitute a strict majority
of the total electorate.  This is the pure combinatorial core of the
Condorcet winner uniqueness argument. -/
theorem condorcet_majority_disjointness
    {N : Type*} [Fintype N] [DecidableEq N]
    (S T : Finset N)
    (hcondorcet : S.card * 2 > Fintype.card N)
    (h_disjoint : Disjoint S T) :
    ¬ (T.card * 2 > Fintype.card N) := by
  intro h_T_wins
  have hcard_sum : S.card + T.card ≤ Fintype.card N := by
    have hunion : (S ∪ T).card = S.card + T.card :=
      Finset.card_union_of_disjoint h_disjoint
    calc S.card + T.card = (S ∪ T).card := hunion.symm
      _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card N := Finset.card_univ
  omega

-- `open Classical in` must precede the doc comment (Lean 4 syntax constraint).
-- The full docstring is in the module header above.
open Classical in
/-- **Condorcet winner majority characterization.**
If `a*` defeats every other alternative by strict majority (Condorcet winner),
and the preference relation `pref` is asymmetric (no voter ranks both
`a* ≻ b` and `b ≻ a*` simultaneously), then no alternative `b ≠ a*` can
also beat `a*` by strict majority.

This is the *uniqueness direction*: two distinct Condorcet winners cannot
coexist.  The proof constructs the majority coalitions via `Finset.filter`,
shows they are disjoint from the asymmetry hypothesis, and applies the
combinatorial `condorcet_majority_disjointness` lemma.

`open Classical` supplies `Decidable` instances for the filtered predicates
without restricting the class of preference relations. -/
theorem condorcet_winner_majority_characterization
    {A N : Type*} [Fintype A] [Fintype N] [DecidableEq A] [DecidableEq N]
    (pref : N → A → A → Prop)
    (a_star : A)
    (hcondorcet : ∀ b : A, b ≠ a_star →
      (Finset.univ.filter (fun i : N => pref i a_star b)).card * 2 >
      Fintype.card N)
    (b : A) (hb : b ≠ a_star)
    (h_disjoint : ∀ i : N, ¬ (pref i a_star b ∧ pref i b a_star)) :
    ¬ ((Finset.univ.filter (fun i : N => pref i b a_star)).card * 2 >
       Fintype.card N) := by
  intro h_b_wins
  -- Coalition S: voters ranking a* above b; coalition T: voters ranking b above a*
  set S := Finset.univ.filter (fun i : N => pref i a_star b)
  set T := Finset.univ.filter (fun i : N => pref i b a_star)
  -- S and T are disjoint by preference asymmetry
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_filter]
    intro i _ hS hT
    exact h_disjoint i ⟨hS, hT⟩
  -- Apply the abstract combinatorial lemma
  exact condorcet_majority_disjointness S T (hcondorcet b hb) hdisj h_b_wins

end Pythia.MechanismDesign
