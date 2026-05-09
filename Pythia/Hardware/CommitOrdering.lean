/-
Copyright (c) 2025 Pythia Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Pythia.Hardware.CommitOrdering — in-order commit from an out-of-order CPU.

Key safety property: an OoO (out-of-order) processor commits instructions
in *program order* even though they may execute in a different order.

Model (abstract, no full microarchitecture):

  · An *instruction* carries a `programOrder : ℕ` index — its position
    in the static instruction stream.
  · The *ROB (Reorder Buffer)* is modelled as a `List Instruction` strictly
    sorted by `programOrder`.  The head is always the oldest un-committed entry.
  · *Execution* may re-sequence instructions; we model this as any bijection
    on commit-slot indices.
  · *Commit* drains the ROB from the head, so commit events respect the
    sorted order.
  · *Architectural state* is modelled as a type `State` updated by applying
    committed instructions one-by-one via a user-supplied `step` function.

Four theorems:

  1. `commit_in_program_order`             — if slot i commits before slot j,
                                             then i's programOrder < j's programOrder.
  2. `rob_preserves_order`                 — the ROB commit pointer advances
                                             monotonically through program order.
  3. `ooo_execute_inorder_commit`          — even if execute(j) precedes execute(i)
                                             for i <_po j, commit(i) precedes commit(j).
  4. `architectural_state_matches_sequential` — OoO architectural state after n commits
                                             equals sequential execution of the same
                                             program-order prefix.
-/

import Mathlib

namespace Pythia.Hardware.CommitOrdering

-- ---------------------------------------------------------------------------
-- § 1  Types
-- ---------------------------------------------------------------------------

/-- An abstract instruction.  Only its program-order index matters. -/
structure Instruction where
  programOrder : ℕ
  deriving DecidableEq, Repr

/-- The commit state tracks the next expected program-order index and
    the count of instructions committed so far. -/
structure CommitState where
  /-- Program-order index of the next instruction to commit. -/
  pointer : ℕ
  /-- Total number of instructions committed so far. -/
  count   : ℕ

-- ---------------------------------------------------------------------------
-- § 2  ROB sorted invariant
-- ---------------------------------------------------------------------------

/-- A ROB is *sorted* when its entries are strictly increasing in program order.
    This ensures the head is always the oldest ready-to-commit instruction. -/
def ROBSorted (rob : List Instruction) : Prop :=
  rob.Pairwise (fun a b => a.programOrder < b.programOrder)

-- ---------------------------------------------------------------------------
-- § 3  commitSeq — the commit drain function
-- ---------------------------------------------------------------------------

/-- `commitSeq cs rob n` simulates `n` commit-drain attempts on a ROB.
    At each step, if the ROB head's `programOrder` equals `cs.pointer`,
    the head is committed (returned in the output list) and the pointer
    advances.  Otherwise the attempt is a no-op. -/
def commitSeq (cs : CommitState) (rob : List Instruction) :
    ℕ → List Instruction × CommitState
  | 0       => ([], cs)
  | n + 1   =>
    match rob with
    | []       => ([], cs)
    | hd :: tl =>
      if hd.programOrder = cs.pointer then
        let (rest, cs') :=
          commitSeq { pointer := cs.pointer + 1, count := cs.count + 1 } tl n
        (hd :: rest, cs')
      else
        commitSeq cs rob n

-- ---------------------------------------------------------------------------
-- § 4  Structural lemmas about commitSeq
-- ---------------------------------------------------------------------------

@[simp] private lemma commitSeq_zero (cs : CommitState) (rob : List Instruction) :
    commitSeq cs rob 0 = ([], cs) := rfl

@[simp] private lemma commitSeq_nil (cs : CommitState) (n : ℕ) :
    commitSeq cs [] n = ([], cs) := by cases n <;> rfl

private lemma commitSeq_fst_cons_match
    (cs : CommitState) (hd : Instruction) (tl : List Instruction) (m : ℕ)
    (hpop : hd.programOrder = cs.pointer) :
    (commitSeq cs (hd :: tl) (m + 1)).1 =
    hd :: (commitSeq { pointer := cs.pointer + 1, count := cs.count + 1 } tl m).1 := by
  simp [commitSeq, hpop]

private lemma commitSeq_snd_cons_match
    (cs : CommitState) (hd : Instruction) (tl : List Instruction) (m : ℕ)
    (hpop : hd.programOrder = cs.pointer) :
    (commitSeq cs (hd :: tl) (m + 1)).2 =
    (commitSeq { pointer := cs.pointer + 1, count := cs.count + 1 } tl m).2 := by
  simp [commitSeq, hpop]

private lemma commitSeq_cons_no_match
    (cs : CommitState) (hd : Instruction) (tl : List Instruction) (m : ℕ)
    (hpop : ¬ hd.programOrder = cs.pointer) :
    commitSeq cs (hd :: tl) (m + 1) = commitSeq cs (hd :: tl) m := by
  simp [commitSeq, hpop]

-- ---------------------------------------------------------------------------
-- § 5  Key structural invariant: the output is a prefix of the ROB
-- ---------------------------------------------------------------------------

/-- **Prefix invariant**: the list of instructions committed by `commitSeq`
    is always an initial segment (prefix) of the sorted ROB; moreover, the
    final commit pointer equals `cs.pointer + k` where `k` is the prefix
    length.

    This is the central lemma that all four theorems reduce to. -/
private lemma commitSeq_is_prefix
    (cs : CommitState) (rob : List Instruction)
    (hsorted : ROBSorted rob)
    (hstart : ∀ i (hi : i < rob.length),
        (rob.get ⟨i, hi⟩).programOrder = cs.pointer + i) :
    ∀ n, ∃ k ≤ rob.length,
        (commitSeq cs rob n).1 = rob.take k ∧
        (commitSeq cs rob n).2.pointer = cs.pointer + k := by
  intro n
  induction n generalizing cs rob with
  | zero => exact ⟨0, Nat.zero_le _, by simp, by simp⟩
  | succ m ih =>
    cases rob with
    | nil => exact ⟨0, Nat.zero_le _, by simp, by simp⟩
    | cons hd tl =>
      by_cases hpop : hd.programOrder = cs.pointer
      · -- Head matches: commit it and recurse on the tail.
        have hsorted_tl : ROBSorted tl := List.Pairwise.of_cons hsorted
        have hstart_tl : ∀ i (hi : i < tl.length),
            (tl.get ⟨i, hi⟩).programOrder = (cs.pointer + 1) + i := by
          intro i hi
          have h := hstart (i + 1) (by simp; omega)
          -- Relate (hd :: tl).get ⟨i + 1, _⟩ = tl.get ⟨i, _⟩ definitionally.
          have heq : (hd :: tl).get ⟨i + 1, by simp; omega⟩ = tl.get ⟨i, hi⟩ := rfl
          rw [heq] at h; omega
        obtain ⟨k, hkle, hk1, hk2⟩ :=
          ih { pointer := cs.pointer + 1, count := cs.count + 1 } tl
            hsorted_tl hstart_tl
        refine ⟨k + 1, by simp; omega, ?_, ?_⟩
        · rw [commitSeq_fst_cons_match _ _ _ _ hpop]; simp [hk1]
        · rw [commitSeq_snd_cons_match _ _ _ _ hpop]; simp at hk2 ⊢; omega
      · -- Head does not match: no progress this step.
        obtain ⟨k, hkle, hk1, hk2⟩ := ih cs (hd :: tl) hsorted hstart
        rw [commitSeq_cons_no_match _ _ _ _ hpop]
        exact ⟨k, hkle, hk1, hk2⟩

-- ---------------------------------------------------------------------------
-- § 6  Derived lemma: programOrder of the j-th committed instruction
-- ---------------------------------------------------------------------------

/-- The `j`-th element of the commit output has
    `programOrder = cs.pointer + j`. -/
private lemma commitSeq_getElem_programOrder
    (cs : CommitState) (rob : List Instruction)
    (hsorted : ROBSorted rob)
    (hstart : ∀ i (hi : i < rob.length),
        (rob.get ⟨i, hi⟩).programOrder = cs.pointer + i)
    (n j : ℕ) (hj : j < (commitSeq cs rob n).1.length) :
    ((commitSeq cs rob n).1[j]'hj).programOrder = cs.pointer + j := by
  obtain ⟨k, hkle, hk1, _⟩ := commitSeq_is_prefix cs rob hsorted hstart n
  -- Compute the index bound in rob.
  have hjrob : j < rob.length := by
    have hj' : j < (rob.take k).length := by rwa [← hk1]
    rw [List.length_take] at hj'
    exact Nat.lt_of_lt_of_le hj' (Nat.min_le_right k rob.length)
  -- Rewrite the commitSeq element to the corresponding rob.take element.
  have h_take : (rob.take k)[j]'(by rwa [← hk1]) = rob[j]'hjrob := List.getElem_take
  rw [show (commitSeq cs rob n).1[j]'hj = (rob.take k)[j]'(by rwa [← hk1]) from by
    simp only [hk1]]
  rw [h_take]
  exact hstart j hjrob

-- ---------------------------------------------------------------------------
-- § 7  Theorem 1 — commit_in_program_order
-- ---------------------------------------------------------------------------

/-- **Theorem 1**: if instruction `i` commits before instruction `j`
    (i.e. `i < j` in the commit-sequence indices), then
    `programOrder(committed[i]) < programOrder(committed[j])`.

    This is the fundamental safety property: commit respects program order
    even though execution does not. -/
theorem commit_in_program_order
    (cs : CommitState) (rob : List Instruction)
    (hsorted : ROBSorted rob)
    (hstart : ∀ i (hi : i < rob.length),
        (rob.get ⟨i, hi⟩).programOrder = cs.pointer + i)
    (n i j : ℕ)
    (hij : i < j)
    (hi : i < (commitSeq cs rob n).1.length)
    (hj : j < (commitSeq cs rob n).1.length) :
    ((commitSeq cs rob n).1[i]'hi).programOrder <
    ((commitSeq cs rob n).1[j]'hj).programOrder := by
  have hpi := commitSeq_getElem_programOrder cs rob hsorted hstart n i hi
  have hpj := commitSeq_getElem_programOrder cs rob hsorted hstart n j hj
  omega

-- ---------------------------------------------------------------------------
-- § 8  Theorem 2 — rob_preserves_order
-- ---------------------------------------------------------------------------

/-- **Theorem 2**: the ROB commit pointer advances monotonically —
    it never decreases across any number of commit drain steps. -/
theorem rob_preserves_order
    (cs : CommitState) (rob : List Instruction) (n : ℕ) :
    cs.pointer ≤ (commitSeq cs rob n).2.pointer := by
  induction n generalizing cs rob with
  | zero => simp
  | succ m ih =>
    cases rob with
    | nil => simp
    | cons hd tl =>
      by_cases hpop : hd.programOrder = cs.pointer
      · rw [commitSeq_snd_cons_match _ _ _ _ hpop]
        have ih' := ih { pointer := cs.pointer + 1, count := cs.count + 1 } tl
        simp at ih'; omega
      · rw [commitSeq_cons_no_match _ _ _ _ hpop]
        exact ih cs (hd :: tl)

-- ---------------------------------------------------------------------------
-- § 9  Execution permutation model
-- ---------------------------------------------------------------------------

/-- An execution order is any function on commit-slot indices.
    Out-of-order execution corresponds to a permutation of these slots. -/
def ExecOrder (n : ℕ) : Type := Fin n → Fin n

/-- A valid execution order is a bijection (permutation). -/
def ValidExecOrder {n : ℕ} (exec : ExecOrder n) : Prop :=
  Function.Bijective exec

-- ---------------------------------------------------------------------------
-- § 10  Theorem 3 — ooo_execute_inorder_commit
-- ---------------------------------------------------------------------------

/-- **Theorem 3** (OoO execute, in-order commit): even if instruction `j`
    is *executed* before instruction `i` (where `i <_po j` in program order),
    `i` is *committed* before `j`.

    The execution order `_exec` is an arbitrary permutation; the theorem
    holds regardless of how the scheduler chose to execute instructions.
    Commit order is determined solely by the sorted ROB, not by `_exec`. -/
theorem ooo_execute_inorder_commit
    (cs : CommitState) (rob : List Instruction)
    (hsorted : ROBSorted rob)
    (hstart : ∀ i (hi : i < rob.length),
        (rob.get ⟨i, hi⟩).programOrder = cs.pointer + i)
    (n i j : ℕ)
    (hij : i < j)
    (hi : i < (commitSeq cs rob n).1.length)
    (hj : j < (commitSeq cs rob n).1.length)
    -- The execution order is an arbitrary permutation — OoO execution.
    (_exec : ExecOrder n)
    (_hvalid : ValidExecOrder _exec) :
    -- Commit still places i before j in program order.
    ((commitSeq cs rob n).1[i]'hi).programOrder <
    ((commitSeq cs rob n).1[j]'hj).programOrder :=
  -- Commit order is fully determined by the sorted ROB, independent of _exec.
  commit_in_program_order cs rob hsorted hstart n i j hij hi hj

-- ---------------------------------------------------------------------------
-- § 11  Sequential execution model and Theorem 4
-- ---------------------------------------------------------------------------

variable {State : Type*}

/-- Apply a list of instructions sequentially to an initial state.
    This models the "in-order" reference machine. -/
def seqExec (step : Instruction → State → State)
    (init : State) (instrs : List Instruction) : State :=
  instrs.foldl (fun s instr => step instr s) init

/-- **Theorem 4**: the architectural state produced by committing `n` steps
    on the OoO machine equals the state produced by applying a prefix of
    the program-order instruction stream sequentially.

    Formally: there exists a `k` such that the OoO commit sequence equals
    `rob.take k`, and therefore `seqExec` applied to both yields the same
    architectural state. -/
theorem architectural_state_matches_sequential
    (step : Instruction → State → State)
    (cs : CommitState) (rob : List Instruction)
    (hsorted : ROBSorted rob)
    (hstart : ∀ i (hi : i < rob.length),
        (rob.get ⟨i, hi⟩).programOrder = cs.pointer + i)
    (init : State) (n : ℕ) :
    ∃ k,
      seqExec step init (commitSeq cs rob n).1 =
      seqExec step init (rob.take k) := by
  obtain ⟨k, _, hk1, _⟩ := commitSeq_is_prefix cs rob hsorted hstart n
  exact ⟨k, by rw [hk1]⟩

end Pythia.Hardware.CommitOrdering
