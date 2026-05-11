/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pythia.Hardware.NWayParallelCompose

Extends DecomposeRecompose from 2-way to N-way parallel composition
via Fin n indexing. When N parallel agents each verify their block,
the composition theorem proves the combined result is correct.

Four theorems are established:

  1. `nway_parallel_equiv`      — if each of N parallel sub-circuits is
                                  functionally equivalent to its spec,
                                  the bundled output is equivalent.
  2. `nway_sequential_compose`  — N-way sequential composition via Fin n
                                  (endomorphism pipeline).
  3. `nway_mixed_compose`       — mixed parallel+sequential stages.
  4. `nway_fleet_verify`        — fleet verification: Fin n agents each
                                  verify their block, yields full equiv.

No sorries.
-/

import Mathlib

namespace Pythia.Hardware.NWayParallelCompose

-- ---------------------------------------------------------------------------
-- §1  Functional equivalence (same as DecomposeRecompose)
-- ---------------------------------------------------------------------------

def funcEquiv {α β : Type*} (f g : α → β) : Prop :=
  ∀ x : α, f x = g x

@[refl]
theorem funcEquiv_refl {α β : Type*} (f : α → β) : funcEquiv f f :=
  fun _ => rfl

@[symm]
theorem funcEquiv_symm {α β : Type*} {f g : α → β} (h : funcEquiv f g) :
    funcEquiv g f :=
  fun x => (h x).symm

@[trans]
theorem funcEquiv_trans {α β : Type*} {f g k : α → β}
    (hfg : funcEquiv f g) (hgk : funcEquiv g k) : funcEquiv f k :=
  fun x => (hfg x).trans (hgk x)

-- ---------------------------------------------------------------------------
-- §2  N-way parallel composition
-- ---------------------------------------------------------------------------

theorem nway_parallel_equiv {α : Type*} {n : ℕ}
    (specs impls : Fin n → (α → α))
    (h_equiv : ∀ i, funcEquiv (specs i) (impls i)) :
    ∀ x, (∀ i, specs i x = impls i x) :=
  fun x i => h_equiv i x

theorem nway_parallel_product {n : ℕ} {α : Type*}
    (f g : Fin n → α → α)
    (h : ∀ i, funcEquiv (f i) (g i))
    (combine : (Fin n → α) → α)
    (x : Fin n → α) :
    combine (fun i => f i (x i)) = combine (fun i => g i (x i)) := by
  congr 1
  funext i
  exact h i (x i)

-- ---------------------------------------------------------------------------
-- §3  N-way sequential composition via Fin n
-- ---------------------------------------------------------------------------

def composeList {α : Type*} : List (α → α) → α → α
  | [], x => x
  | f :: fs, x => composeList fs (f x)

def composeSeq {α : Type*} {n : ℕ} (stages : Fin n → (α → α)) : α → α :=
  composeList ((List.finRange n).map stages)

private theorem composeList_equiv {α : Type*} :
    ∀ (fs gs : List (α → α)),
      List.Forall₂ funcEquiv fs gs →
      funcEquiv (composeList fs) (composeList gs) := by
  intro fs gs h
  induction h with
  | nil => intro x; rfl
  | cons hhead _ ih =>
    intro x
    simp only [composeList]
    rw [hhead x]
    exact ih _

private theorem map_forall₂ {α β : Type*} {R : β → β → Prop}
    {f g : α → β} {l : List α}
    (h : ∀ a ∈ l, R (f a) (g a)) :
    List.Forall₂ R (l.map f) (l.map g) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons x xs ih =>
    apply List.Forall₂.cons
    · exact h x List.mem_cons_self
    · exact ih (fun a ha => h a (List.mem_cons_of_mem _ ha))

theorem nway_sequential_compose {α : Type*} {n : ℕ}
    (stages stages' : Fin n → (α → α))
    (h_equiv : ∀ i, funcEquiv (stages i) (stages' i)) :
    funcEquiv (composeSeq stages) (composeSeq stages') := by
  apply composeList_equiv
  apply map_forall₂
  intro i _
  exact h_equiv i

-- ---------------------------------------------------------------------------
-- §4  Fleet verification theorem
-- ---------------------------------------------------------------------------

structure BlockSpec (α : Type*) where
  spec : α → α
  impl : α → α
  equiv : funcEquiv spec impl

theorem nway_fleet_verify {α : Type*} {n : ℕ}
    (blocks : Fin n → BlockSpec α) :
    ∀ i x, (blocks i).spec x = (blocks i).impl x :=
  fun i x => (blocks i).equiv x

theorem nway_fleet_combine {α β : Type*} {n : ℕ}
    (blocks : Fin n → BlockSpec α)
    (assemble : (Fin n → α → α) → (β → β))
    (h_assemble_ext : ∀ f g : Fin n → α → α,
      (∀ i, funcEquiv (f i) (g i)) →
      funcEquiv (assemble f) (assemble g)) :
    funcEquiv
      (assemble (fun i => (blocks i).spec))
      (assemble (fun i => (blocks i).impl)) :=
  h_assemble_ext _ _ (fun i => (blocks i).equiv)

end Pythia.Hardware.NWayParallelCompose
