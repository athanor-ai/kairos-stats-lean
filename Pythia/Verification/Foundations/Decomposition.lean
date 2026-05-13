/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pythia.Verification.Foundations.Decomposition

Formally verified soundness of hierarchical circuit decompose-and-recompose
optimization.  Circuits are modeled as pure functions; functional equivalence
is pointwise equality of outputs for all inputs.

This module is part of the **4+1 universal invariant set** that the
customer-facing `flow_guard` preflight gate cites. The other public
invariants live in:

  * `Pythia.Verification.Foundations.Refinement`  — Burch-Dill refinement
  * `Pythia.Verification.Foundations.Induction`   — k-induction soundness
  * `Pythia.Verification.Foundations.Composition` — compositional refinement schema
  * `Pythia.AxiomAudit`                           — trusted-base receipt

Four theorems are established:

  1. `decomposition_recomposition_sound` — sequential two-stage decomposition:
       if f = g ∘ h and g' ≡ g and h' ≡ h then g' ∘ h' ≡ f.

  2. `parallel_decompose_sound` — parallel (fan-out / fan-in) decomposition:
       if f = ⟨g, h⟩ and g' ≡ g and h' ≡ h then ⟨g', h'⟩ ≡ f.

  3. `n_way_decompose_sound` — n-way serial decomposition via a `List` of
       stages: if each stage fᵢ' is pointwise equal to fᵢ then the composed
       pipeline preserves the overall function.

  4. `hierarchical_optimize_sound` — module/sub-module substitution:
       if sub-module S is replaced by S' where S' ≡ S, the enclosing
       module M (parametrised by S) produces equivalent outputs.

The headline `decomposition_recomposition_sound` is the formerly-private
`decompose_recompose_sound` renamed per the 2026-05-13 signature audit so
the customer-facing label matches the proof. The private namespace
`Pythia.Hardware.DecomposeRecompose` retains a backwards-compatibility
re-export under the old name.
-/

import Mathlib

namespace Pythia.Verification.Foundations.Decomposition

-- ---------------------------------------------------------------------------
-- Functional equivalence
-- ---------------------------------------------------------------------------

/-- Two circuits are *functionally equivalent* when they agree on every input.
    This is the standard notion of combinational equivalence used in EDA
    (e.g., as checked by a combinational miter). -/
def funcEquiv {α β : Type*} (f g : α → β) : Prop :=
  ∀ x : α, f x = g x

/-- Functional equivalence is reflexive. -/
@[refl]
theorem funcEquiv_refl {α β : Type*} (f : α → β) : funcEquiv f f :=
  fun _ => rfl

/-- Functional equivalence is symmetric. -/
@[symm]
theorem funcEquiv_symm {α β : Type*} {f g : α → β} (h : funcEquiv f g) :
    funcEquiv g f :=
  fun x => (h x).symm

/-- Functional equivalence is transitive. -/
@[trans]
theorem funcEquiv_trans {α β : Type*} {f g k : α → β}
    (hfg : funcEquiv f g) (hgk : funcEquiv g k) : funcEquiv f k :=
  fun x => (hfg x).trans (hgk x)

-- ---------------------------------------------------------------------------
-- Theorem 1 — sequential two-stage decompose-and-recompose
-- ---------------------------------------------------------------------------

/-- **Decomposition / recomposition soundness (sequential).**

    If a circuit `f : α → γ` decomposes into two stages `g : β → γ` and
    `h : α → β` so that `f = g ∘ h`, and if each stage is independently
    optimized to a functionally equivalent replacement (`h'` for `h` and
    `g'` for `g`), then the recomposed circuit `g' ∘ h'` is functionally
    equivalent to the original `f`.

    This is the formal basis for hierarchical sequential optimization
    passes: each pipeline stage can be optimized in isolation.

    Note. Originally `Pythia.Hardware.DecomposeRecompose.decompose_recompose_sound`;
    renamed in the 2026-05-13 signature audit so the public label matches the
    proof. The old name is re-exported from the private namespace for
    backwards compatibility. -/
theorem decomposition_recomposition_sound
    {α β γ : Type*}
    (f : α → γ) (g : β → γ) (h : α → β)
    (g' : β → γ) (h' : α → β)
    (hdecomp : ∀ x, f x = g (h x))
    (hg : funcEquiv g g')
    (hh : funcEquiv h h') :
    funcEquiv (g' ∘ h') f := by
  intro x
  simp only [Function.comp]
  rw [← hh x, ← hg (h x), ← hdecomp x]

-- ---------------------------------------------------------------------------
-- Theorem 2 — parallel decompose-and-recompose
-- ---------------------------------------------------------------------------

/-- **Decompose-recompose soundness (parallel).**

    If a circuit `f : α → β × γ` splits into two independent parallel paths
    `g : α → β` and `h : α → γ` so that `f x = (g x, h x)` for all `x`,
    and if each path is optimized to an equivalent replacement, then the
    recombined circuit `fun x => (g' x, h' x)` is functionally equivalent
    to `f`.

    This covers fan-out designs where a single input drives two independent
    sub-circuits whose outputs are merged (e.g., two parallel ALU datapaths,
    dual-rail encoders, or side-channel + functional paths). -/
theorem parallel_decompose_sound
    {α β γ : Type*}
    (f : α → β × γ) (g : α → β) (h : α → γ)
    (g' : α → β) (h' : α → γ)
    (hdecomp : ∀ x, f x = (g x, h x))
    (hg : funcEquiv g g')
    (hh : funcEquiv h h') :
    funcEquiv (fun x => (g' x, h' x)) f := by
  intro x
  rw [hdecomp x, hg x, hh x]

-- ---------------------------------------------------------------------------
-- Theorem 3 — n-way serial decomposition
-- ---------------------------------------------------------------------------

/-- Apply a list of endomorphisms left-to-right (pipeline composition).
    `pipelineCompose [f₀, f₁, …, fₙ] x` computes `fₙ (… (f₁ (f₀ x)) …)`. -/
def pipelineCompose {α : Type*} (stages : List (α → α)) (x : α) : α :=
  stages.foldl (fun acc f => f acc) x

/-- Key lemma: if two lists of endomorphisms are related pairwise by `Forall₂`,
    their left-folds from any equal initial values agree. -/
private theorem foldl_forall₂ {α : Type*} :
    ∀ (ss ss' : List (α → α)) (init : α),
    List.Forall₂ (funcEquiv (α := α) (β := α)) ss ss' →
    ss.foldl (fun acc f => f acc) init =
    ss'.foldl (fun acc f => f acc) init := by
  intro ss ss' init h
  induction h generalizing init with
  | nil => rfl
  | cons hhead _ ih =>
    simp only [List.foldl_cons]
    rw [hhead init]
    exact ih _

/-- **Decompose-recompose soundness (n-way).**

    If a circuit is realized as a pipeline of `n` stages `f₀, f₁, …, fₙ₋₁`,
    and each stage `fᵢ'` is a functionally equivalent replacement for `fᵢ`,
    then the pipeline formed from the optimized stages is functionally
    equivalent to the original pipeline.

    The hypothesis uses `List.Forall₂` — a simultaneous inductive predicate
    on two lists — which exactly captures "the lists have the same length and
    each pair of corresponding elements satisfies the given relation."

    This generalizes `decomposition_recomposition_sound` from 2 to an arbitrary
    number of stages and is the formal backbone for multi-pass RTL
    optimization flows (e.g., retiming, remapping, buffer insertion) where
    each pass touches one pipeline stage at a time. -/
theorem n_way_decompose_sound
    {α : Type*}
    (stages stages' : List (α → α))
    (hstages : List.Forall₂ (funcEquiv (α := α) (β := α)) stages stages') :
    funcEquiv (pipelineCompose stages) (pipelineCompose stages') := by
  intro x
  simp only [pipelineCompose]
  exact foldl_forall₂ stages stages' x hstages

-- ---------------------------------------------------------------------------
-- Theorem 4 — hierarchical module substitution
-- ---------------------------------------------------------------------------

/-- **Hierarchical optimization soundness.**

    A module `M` is parametrised by a sub-module `S : σ → τ`.  If `S` is
    replaced by a functionally equivalent implementation `S'`, then the
    resulting module `M S'` is functionally equivalent to the original `M S`.

    This is the formal basis for hierarchical design-rule-check flows,
    sub-module black-boxing, and IP replacement: one can swap out a verified
    sub-module for an optimized drop-in replacement without re-verifying the
    enclosing module, provided the sub-module's I/O contract is preserved.

    The proof is one line: unfolding `funcEquiv` and using `hS` to rewrite
    the inner call is all that is required, since `M` treats `S` as a
    black box. -/
theorem hierarchical_optimize_sound
    {α σ τ β : Type*}
    (M : (σ → τ) → α → β)
    (S S' : σ → τ)
    (hS : funcEquiv S S') :
    funcEquiv (M S') (M S) := by
  intro x
  congr 1
  funext y
  exact (hS y).symm

end Pythia.Verification.Foundations.Decomposition
