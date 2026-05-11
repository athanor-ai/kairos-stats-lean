/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pythia.Hardware.AssumeGuarantee

Assume-guarantee compositional verification: proving that independently
verified components compose correctly.

This is the formal backbone for fleet parallel verification: when N agents
each verify a block under stated assumptions, the composition theorem
proves the combined design is correct — provided each block's assumptions
are discharged by other blocks' guarantees.

Key results:

  1. `ag_sequential_2`        — 2-component sequential composition (pipeline).
  2. `ag_sequential_n`        — N-component sequential pipeline (induction).
  3. `ag_parallel_independent` — N independent parallel blocks.
  4. `ag_parallel_discharged`  — N parallel blocks with env assumptions.
  5. `ag_seeded_2`            — 2-component seeded AG (NOT full circular;
                                requires external seed A₁∨A₂).
  6. `ag_dag`                 — DAG-structured composition (well-founded
                                recursion on topological order — this IS
                                the real composition theorem).
  7. `ag_fleet_composition`   — extraction lemma: applies FleetBlock.verified
                                to each block. Structurally trivial; the work
                                is in constructing the FleetBlock instances.

Honest limitations:
  - ag_seeded_2 is NOT full circular AG. Real circular AG needs a
    well-foundedness argument (Alur & Henzinger 1999).
  - ag_fleet_composition delegates the hard part (proving env_needed
    for each block) to the caller. The theorem just extracts specs
    from pre-verified blocks.
  - ag_dag IS substantive: well-founded recursion on a topological
    order resolves all dependencies without external seeds.

No sorries.
-/

import Mathlib

namespace Pythia.Hardware.AssumeGuarantee

-- ---------------------------------------------------------------------------
-- §1  Abstract component model
-- ---------------------------------------------------------------------------

structure Component where
  assumption : Prop
  guarantee  : Prop
  valid      : assumption → guarantee

-- ---------------------------------------------------------------------------
-- §2  Sequential (pipeline) composition — 2 components
-- ---------------------------------------------------------------------------

theorem ag_sequential_2
    (c₁ c₂ : Component)
    (h_entry : c₁.assumption)
    (h_interface : c₁.guarantee → c₂.assumption) :
    c₁.guarantee ∧ c₂.guarantee :=
  let g₁ := c₁.valid h_entry
  ⟨g₁, c₂.valid (h_interface g₁)⟩

-- ---------------------------------------------------------------------------
-- §3  Sequential pipeline — N components
-- ---------------------------------------------------------------------------

theorem ag_sequential_n
    (assumptions guarantees : ℕ → Prop)
    (valid : ∀ i, assumptions i → guarantees i)
    (h_entry : assumptions 0)
    (h_chain : ∀ i, guarantees i → assumptions (i + 1)) :
    ∀ i, guarantees i := by
  intro i
  induction i with
  | zero => exact valid 0 h_entry
  | succ k ih => exact valid (k + 1) (h_chain k ih)

-- ---------------------------------------------------------------------------
-- §4  Parallel independent blocks (no cross-assumptions)
-- ---------------------------------------------------------------------------

theorem ag_parallel_independent {n : ℕ}
    (blocks : Fin n → Component)
    (h_all_assumed : ∀ i, (blocks i).assumption) :
    ∀ i, (blocks i).guarantee :=
  fun i => (blocks i).valid (h_all_assumed i)

-- ---------------------------------------------------------------------------
-- §5  Parallel with discharged assumptions
-- ---------------------------------------------------------------------------

theorem ag_parallel_discharged {n : ℕ}
    (blocks : Fin n → Component)
    (env : Prop) (h_env : env)
    (h_discharge : ∀ i, env → (blocks i).assumption) :
    ∀ i, (blocks i).guarantee :=
  fun i => (blocks i).valid (h_discharge i h_env)

-- ---------------------------------------------------------------------------
-- §6  Seeded assume-guarantee (2 components)
--
-- NOTE: This is NOT full circular assume-guarantee (which requires a
-- well-foundedness argument to break circularity, cf. Alur & Henzinger 1999).
-- This is the SEEDED variant: given an external seed (A₁ ∨ A₂), the
-- dependencies can be resolved sequentially. The seed is a real requirement,
-- not a dodge — it represents the "first mover" in a non-circular ordering.
-- ---------------------------------------------------------------------------

theorem ag_seeded_2
    (A₁ A₂ G₁ G₂ : Prop)
    (h₁ : A₁ → G₁) (h₂ : A₂ → G₂)
    (h_discharge₁ : G₂ → A₁) (h_discharge₂ : G₁ → A₂)
    (h_seed : A₁ ∨ A₂) :
    G₁ ∧ G₂ := by
  cases h_seed with
  | inl ha₁ =>
    have g₁ := h₁ ha₁
    have g₂ := h₂ (h_discharge₂ g₁)
    exact ⟨g₁, g₂⟩
  | inr ha₂ =>
    have g₂ := h₂ ha₂
    have g₁ := h₁ (h_discharge₁ g₂)
    exact ⟨g₁, g₂⟩

-- ---------------------------------------------------------------------------
-- §7  DAG-structured composition
-- ---------------------------------------------------------------------------

def ag_dag_aux {n : ℕ}
    (assumptions guarantees : Fin n → Prop)
    (valid : ∀ i, assumptions i → guarantees i)
    (order : Fin n → ℕ)
    (discharge : ∀ i, (∀ j, order j < order i → guarantees j) → assumptions i)
    (i : Fin n) : guarantees i :=
  valid i (discharge i (fun j _ => ag_dag_aux assumptions guarantees valid order discharge j))
termination_by order i

theorem ag_dag {n : ℕ}
    (assumptions guarantees : Fin n → Prop)
    (valid : ∀ i, assumptions i → guarantees i)
    (order : Fin n → ℕ)
    (discharge : ∀ i, (∀ j, order j < order i → guarantees j) → assumptions i) :
    ∀ i, guarantees i :=
  ag_dag_aux assumptions guarantees valid order discharge

-- ---------------------------------------------------------------------------
-- §8  Fleet composition — the orchestrator theorem
-- ---------------------------------------------------------------------------

structure FleetBlock where
  spec       : Prop
  env_needed : Prop
  verified   : env_needed → spec

theorem ag_fleet_composition {n : ℕ}
    (blocks : Fin n → FleetBlock)
    (h_env : ∀ i, (blocks i).env_needed) :
    ∀ i, (blocks i).spec :=
  fun i => (blocks i).verified (h_env i)

theorem ag_fleet_all_specs {n : ℕ}
    (blocks : Fin n → FleetBlock)
    (h_env : ∀ i, (blocks i).env_needed)
    (topSpec : Prop)
    (h_top : (∀ i, (blocks i).spec) → topSpec) :
    topSpec :=
  h_top (ag_fleet_composition blocks h_env)

-- ---------------------------------------------------------------------------
-- §9  N-way parallel composition (extends DecomposeRecompose)
-- ---------------------------------------------------------------------------

theorem nway_parallel_compose {α : Type*} {n : ℕ}
    (specs : Fin n → (α → Prop))
    (impls : Fin n → (α → Prop))
    (h_refine : ∀ i x, impls i x → specs i x) :
    ∀ x, (∀ i, impls i x) → (∀ i, specs i x) :=
  fun x h_all i => h_refine i x (h_all i)

theorem nway_parallel_and {n : ℕ}
    (props : Fin n → Prop)
    (proofs : ∀ i, props i) :
    ∀ i, props i := proofs

end Pythia.Hardware.AssumeGuarantee
