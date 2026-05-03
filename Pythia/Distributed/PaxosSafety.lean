/-
Copyright (c) 2026 Pythia Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pythia
-/
import Mathlib
import Pythia.Distributed.Basic

/-!
# Paxos Single-Decree Safety

We formalise Lamport's 1998 Theorem 1: in a single-decree Paxos system,
any two chosen values must be equal.

## Modelling

* **Nodes / Ballots / Values.** The set of acceptor nodes is a `Finset Node`,
  ballots carry a `LinearOrder`, and values have `DecidableEq`.

* **`vote : Node → Ballot → Option Value`** records which value (if any) each
  acceptor voted for at each ballot.

* **`Chosen v`** holds when a strict-majority quorum all voted for `v` at
  the same ballot.

* **`SafeAt v b`** says: for every earlier ballot `c < b` and every
  strict-majority quorum `Q`, some member of `Q` either abstained at `c`
  or voted for `v`.  This captures the combined effect of the Paxos
  Phase-1b / Phase-2a rules.

* **`PaxosInvariant`** bundles two properties that any correct Paxos run
  maintains:
  1. *One value per ballot* (`vote_unique`).
  2. *Every vote is safe* (`vote_safe`).

## Main result

* `paxos_single_decree_safety`: `Chosen v₁ → Chosen v₂ → v₁ = v₂`.

## References

* L. Lamport, "The Part-Time Parliament", *ACM TOCS* 16(2), 1998 — Theorem 1.
* L. Lamport, "Paxos Made Simple", *ACM SIGACT News* 32(4), 2001.
-/

namespace Pythia.Distributed

section PaxosSafety

variable {Node : Type*} {Ballot : Type*} {Value : Type*}
  [DecidableEq Node] [DecidableEq Value] [LinearOrder Ballot]

variable (nodes : Finset Node) (vote : Node → Ballot → Option Value)

/-- A value `v` is **chosen** when a strict-majority quorum all voted for `v`
at the same ballot. -/
def Chosen (v : Value) : Prop :=
  ∃ (b : Ballot) (Q : Finset Node),
    Q ⊆ nodes ∧ 2 * Q.card > nodes.card ∧ ∀ n ∈ Q, vote n b = some v

/-- `SafeAt v b` says: for every earlier ballot `c` and every majority
quorum `Q`, some member of `Q` either abstained or voted for `v` at `c`.
This is the combined effect of Phase-1b / Phase-2a. -/
def SafeAt (v : Value) (b : Ballot) : Prop :=
  ∀ c, c < b → ∀ Q : Finset Node,
    Q ⊆ nodes → 2 * Q.card > nodes.card →
    ∃ n ∈ Q, vote n c = none ∨ vote n c = some v

/-- The **Paxos voting invariant**: every cast vote is safe at its ballot,
and at most one value is voted per ballot. -/
structure PaxosInvariant : Prop where
  /-- One value per ballot: if two nodes voted at the same ballot, they voted
  for the same value. -/
  vote_unique : ∀ (n₁ n₂ : Node) (b : Ballot) (v₁ v₂ : Value),
    vote n₁ b = some v₁ → vote n₂ b = some v₂ → v₁ = v₂
  /-- Every vote is safe: if node `n` voted `v` at ballot `b` and `n`
  belongs to the node set, then `SafeAt v b`. -/
  vote_safe : ∀ (n : Node) (b : Ballot) (v : Value),
    n ∈ nodes → vote n b = some v → SafeAt nodes vote v b

/-
**Paxos single-decree safety** (Lamport 1998, Theorem 1):
if two values are both chosen, they must be equal.

*Proof sketch.* Let `v₁` be chosen at ballot `b₁` via quorum `Q₁`, and
`v₂` at `b₂` via `Q₂`.  Compare `b₁` and `b₂`:

* `b₁ = b₂`: any member of `Q₁` voted `v₁` and any member of `Q₂` voted
  `v₂` at the same ballot; `vote_unique` gives `v₁ = v₂`.

* `b₁ < b₂`: pick any `n₂ ∈ Q₂`; since `n₂` voted `v₂` at `b₂`,
  `vote_safe` gives `SafeAt v₂ b₂`.  Instantiate with `c := b₁` and
  `Q := Q₁` to find `m ∈ Q₁` with `vote m b₁ = none ∨ vote m b₁ = some v₂`.
  But `m ∈ Q₁` so `vote m b₁ = some v₁`; the `none` branch is absurd,
  so `some v₁ = some v₂`, hence `v₁ = v₂`.

* `b₂ < b₁`: symmetric.
-/
omit [DecidableEq Value] in
theorem paxos_single_decree_safety
    (inv : PaxosInvariant nodes vote)
    (v₁ v₂ : Value)
    (hv₁ : Chosen nodes vote v₁)
    (hv₂ : Chosen nodes vote v₂) :
    v₁ = v₂ := by
  rcases hv₁ with ⟨ b₁, Q₁, hQ₁_sub, hQ₁_maj, hQ₁_vote ⟩
  rcases hv₂ with ⟨ b₂, Q₂, hQ₂_sub, hQ₂_maj, hQ₂_vote ⟩
  by_cases h_cases : b₁ = b₂;
  · have := Pythia.Distributed.paxos_quorum_intersection Q₁ Q₂ hQ₁_sub hQ₂_sub hQ₁_maj hQ₂_maj;
    grind +splitIndPred;
  · -- Without loss of generality, assume $b₁ < b₂$.
    wlog h_wlog : b₁ < b₂ generalizing b₁ b₂ Q₁ Q₂ v₁ v₂;
    · exact Eq.symm ( this v₂ v₁ b₂ Q₂ hQ₂_sub hQ₂_maj hQ₂_vote b₁ Q₁ hQ₁_sub hQ₁_maj hQ₁_vote ( Ne.symm h_cases ) ( lt_of_le_of_ne ( le_of_not_gt h_wlog ) ( Ne.symm h_cases ) ) );
    · obtain ⟨ n₂, hn₂ ⟩ := Finset.card_pos.mp ( by linarith : 0 < Finset.card Q₂ );
      have := inv.vote_safe n₂ b₂ v₂ ( hQ₂_sub hn₂ ) ( hQ₂_vote n₂ hn₂ );
      obtain ⟨ m, hm₁, hm₂ ⟩ := this b₁ h_wlog Q₁ hQ₁_sub hQ₁_maj;
      grind

end PaxosSafety

end Pythia.Distributed