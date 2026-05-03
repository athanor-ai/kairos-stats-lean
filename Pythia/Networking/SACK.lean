/-
  Pythia.Networking.SACK
  SACK block non-overlap: sorted SACK blocks are pairwise disjoint.

  RFC 2018 §3: SACK blocks are non-overlapping and listed in
  ascending order of left edge. We prove the formal counterpart:
  a list of SackBlocks sorted by right-edge ≤ left-edge of the
  next block is pairwise left-disjoint (l[i].right ≤ l[j].left for i < j).

  Acceptance gate: zero unproved obligations, only axioms
  {propext, Classical.choice, Quot.sound}.
-/
import Mathlib

namespace Pythia.Networking.SACK

/-- A SACK block with strict left < right invariant. -/
structure SackBlock where
  left  : ℕ
  right : ℕ
  h     : left < right

/-- "Left disjoint": first block ends before second begins. -/
def LeftDisjoint (a b : SackBlock) : Prop := a.right ≤ b.left

/-- The gap-sorted predicate: consecutive blocks satisfy right ≤ next.left. -/
def gapSorted : List SackBlock → Prop
  | []          => True
  | [_]         => True
  | a :: b :: t => a.right ≤ b.left ∧ gapSorted (b :: t)

/-- gapSorted tail. -/
private theorem gapSorted_tail {x : SackBlock} {l : List SackBlock}
    (h : gapSorted (x :: l)) : gapSorted l := by
  rcases l with _ | ⟨y, rest⟩
  · exact trivial
  · exact h.2

/-- In a gapSorted list, the head is LeftDisjoint from every element. -/
private theorem gapSorted_head_disj {a : SackBlock} :
    ∀ {l : List SackBlock}, gapSorted (a :: l) → ∀ b ∈ l, LeftDisjoint a b := by
  intro l
  induction l generalizing a with
  | nil => intro _ b hb; exact absurd hb List.not_mem_nil
  | cons hd tl ih =>
      intro hgs b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb_tl
      · exact hgs.1
      · -- a.right ≤ hd.left < hd.right ≤ b.left
        have h1 : a.right ≤ hd.left := hgs.1
        have h2 : hd.right ≤ b.left := ih hgs.2 b hb_tl
        exact Nat.le_trans h1 (Nat.le_trans hd.h.le h2)

/-- gapSorted implies List.Pairwise LeftDisjoint. -/
theorem gapSorted_pairwise : ∀ (l : List SackBlock), gapSorted l →
    l.Pairwise LeftDisjoint := by
  intro l
  induction l with
  | nil => intro; exact List.Pairwise.nil
  | cons hd tl ih =>
      intro hgs
      exact List.Pairwise.cons (gapSorted_head_disj hgs) (ih (gapSorted_tail hgs))

/-- Main theorem: for a gapSorted list, blocks at indices i < j satisfy
    l[i].right ≤ l[j].left. -/
theorem sack_selective_ack_gap_non_overlap
    (l : List SackBlock) (h : gapSorted l)
    (i j : ℕ) (hi : i < l.length) (hj : j < l.length) (hij : i < j) :
    (l[i]).right ≤ (l[j]).left := by
  have hpw := gapSorted_pairwise l h
  rw [List.pairwise_iff_getElem] at hpw
  exact hpw i j hi hj hij

end Pythia.Networking.SACK
