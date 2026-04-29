/-
  CedarMicro.Ty. Palamedes-ready type language (flat, 2 nullary ctors).

  Line-for-line port of `palamedes-lean/Palamedes/Data/STLC/Ty.lean`
  (577 LOC), specialised to a flat Ty (bool + int, no recursive arms).
  The flatness collapses several sections of the STLC pattern into
  triviality. we keep the parallel structure for readability and so
  the pattern is obvious when we port Expr.

  Scaffolding exposed at the end of this module:
    Gen.arbTy              unconstrained Ty generator
    Gen.caseTy             case-elim combinator over Ty
    Gen.CorrectGen.s_arbTy / s_caseTy   (subtype-refined versions)
    Gen.Total.total_arbTy / total_Ty_caseTy   (@[aesop safe (totality)])
    Ty.as_or, Ty.deforest_eq   (in Ty.rec form. Palamedes's pattern)

  Once CedarMicro.Expr lands the same pattern, `generator_search`
  against `isWellTyped` has everything it needs.
-/

import Pythia.LanguageSemantics.Palamedes.Gen
import Pythia.LanguageSemantics.Palamedes.CorrectGen
import Pythia.LanguageSemantics.Palamedes.Total

namespace Pythia.LanguageSemantics.Cedar

-- ── TypeDef ─────────────────────────────────────────────────────────

inductive Ty : Type where
  | bool
  | int
  deriving DecidableEq, Repr

-- ── BaseFunctor ─────────────────────────────────────────────────────

/-- Companion functor. Both constructors are nullary so this is a copy
    of Ty, but we keep it explicit to parallel the STLC pattern
    (Expr.lean's companion functor is non-trivial). -/
inductive TyF (α : Type) where
  | bool : TyF α
  | int : TyF α

theorem TyF_or
    {α : Type}
    {Pbool Pint : Prop}
    {τ : TyF α} :
    TyF.rec Pbool Pint τ ↔ (Pbool ∧ τ = .bool) ∨ (Pint ∧ τ = .int) := by
  match τ with
  | .bool => simp
  | .int => simp

-- ── RecursionSchemes ────────────────────────────────────────────────

def Ty.fold {α : Type} (z_bool z_int : α) (τ : Ty) : α :=
  match τ with
  | .bool => z_bool
  | .int  => z_int

@[simp] theorem Ty.fold_bool : Ty.fold zb zi .bool = zb := rfl
@[simp] theorem Ty.fold_int  : Ty.fold zb zi .int  = zi := rfl

def Ty.accuM [Monad m] {α σ : Type}
    (f_bool : σ → m α) (f_int : σ → m α)
    (τ : Ty) (i : σ) : m α :=
  match τ with
  | .bool => f_bool i
  | .int  => f_int i

@[simp] theorem Ty.accuM_bool [Monad m] {α σ} {fb fi : σ → m α} {i : σ} :
    Ty.accuM fb fi (.bool : Ty) i = fb i := rfl
@[simp] theorem Ty.accuM_int [Monad m] {α σ} {fb fi : σ → m α} {i : σ} :
    Ty.accuM fb fi (.int : Ty) i = fi i := rfl

-- ── Unfold ──────────────────────────────────────────────────────────

open Gen

private def Ty.unfold_aux (n : Nat) (f : α → Gen (TyF α)) (x : α) : Gen (Option Ty) :=
  match n with
  | 0 => pure none
  | _ + 1 => do
    match (← f x) with
    | .bool => pure (some .bool)
    | .int  => pure (some .int)

@[simp]
theorem Ty.unfold_aux_monotonic :
    some v ∈ 〚Ty.unfold_aux n f b〛 →
    some v ∈ 〚Ty.unfold_aux (n + m) f b〛 := by
  induction n generalizing v f b
  case zero =>
    simp [Ty.unfold_aux]
  case succ n' _ih =>
    unfold Ty.unfold_aux
    simp
    intro τ hτ h
    cases τ <;> simp_all +arith
    · case bool => exact ⟨TyF.bool, hτ, rfl⟩
    · case int  => exact ⟨TyF.int,  hτ, rfl⟩

@[irreducible]
def Ty.unfold (f : α → Gen (TyF α)) (x : α) : Gen Ty :=
  .indexed (fun n => Ty.unfold_aux n f x)

@[simp]
def Ty.unfold_support (P : α → TyF α → Prop) (x : α) (τ : Ty) : Prop :=
  match τ with
  | .bool => P x .bool
  | .int  => P x .int

@[simp]
theorem Ty.support_unfold :
    support (Ty.unfold f x) = Ty.unfold_support (fun x' => support (f x')) x := by
  funext τ
  simp_all
  induction τ generalizing x with
  | bool =>
    apply Iff.intro
    · intro h
      simp_all [unfold]
      replace ⟨n, h⟩ := h
      cases n <;> simp_all [Ty.unfold_aux]
      case succ n' =>
        replace ⟨v', hv', h⟩ := h
        cases v' <;> simp_all
    · intros h
      simp_all [unfold]
      exact ⟨1, TyF.bool, h, rfl⟩
  | int =>
    apply Iff.intro
    · intro h
      simp_all [unfold]
      replace ⟨n, h⟩ := h
      cases n <;> simp_all [Ty.unfold_aux]
      case succ n' =>
        replace ⟨v', hv', h⟩ := h
        cases v' <;> simp_all
    · intros h
      simp_all [unfold]
      exact ⟨1, TyF.int, h, rfl⟩

theorem Ty.support_unfold_congr
    {hf : ∀ {b}, support (f b) = support (f' b)} :
    support (Ty.unfold f b) = support (Ty.unfold f' b) := by
  aesop

-- ── FoldCoercion ────────────────────────────────────────────────────
-- FoldConversions + FoldMerging elided: both are proved by induction
-- on a τ that's flat, degenerating each theorem to a 2-case simp with
-- no recursive hypothesis to apply. Not useful until we need them.

theorem Ty.coerce_to_fold
    {τ : Ty} {f : Ty → α} {zb zi : α}
    (h₁ : f .bool = zb := by rfl)
    (h₂ : f .int  = zi := by rfl) :
    f τ = Ty.fold zb zi τ := by
  induction τ <;> simp_all

theorem Ty.coerce_match
    {τ : Ty} {f : Ty → α} {zb zi : α}
    (h₁ : f .bool = zb)
    (h₂ : f .int  = zi) :
    f τ = Ty.rec zb zi τ := by
  induction τ <;> simp_all

-- ── Gen.arbTy / Gen.caseTy ──────────────────────────────────────────

namespace Gen

@[irreducible]
def arbTy : Gen Ty := Ty.unfold
  (fun _ => pick (pure TyF.bool) (pure TyF.int))
  PUnit.unit

def caseTy
    (τ : Ty)
    (gb : (τ = Ty.bool) → Gen α)
    (gi : (τ = Ty.int)  → Gen α) :
    Gen α :=
  match τ with
  | .bool => gb rfl
  | .int  => gi rfl

@[simp]
theorem support_arbTy :
    support arbTy = fun _ => True := by
  simp [arbTy]
  funext v
  induction v <;> simp_all

@[simp]
def support_Ty_caseTy
    {gb : (τ = Ty.bool) → Gen α}
    {gi : (τ = Ty.int)  → Gen α} :
    support (caseTy τ (fun h => gb h) (fun h => gi h)) =
    (fun a =>
      (∃ h : τ = Ty.bool, a ∈ 〚gb h〛) ∨
      (∃ h : τ = Ty.int,  a ∈ 〚gi h〛)) := by
  funext
  simp
  apply Iff.intro
  · intro h
    cases τ <;> aesop
  · intro h
    cases h <;> aesop

-- ── CorrectGen refinements ──────────────────────────────────────────

namespace CorrectGen

@[reducible]
def s_arbTy : @CorrectGen Ty (fun _ => True) :=
  Subtype.mk arbTy <| by funext v; simp

@[reducible]
def s_caseTy
    {Q : α → Prop}
    {P : α → Ty → Prop}
    (τ : Ty)
    (h : ∀ {a}, P a τ = Q a)
    (gb : CorrectGen (fun a => P a .bool))
    (gi : CorrectGen (fun a => P a .int)) :
    CorrectGen Q :=
    Subtype.mk
      (caseTy τ (fun _ => gb.val) (fun _ => gi.val)) <| by
    match τ with
    | .bool => simp [gb.property, h]
    | .int  => simp [gi.property, h]

end CorrectGen

-- ── Totality. aesop-registered for generator_search ────────────────

namespace Total

/-- `Ty.unfold g b` is total whenever the step function `g` is total
    at every argument. Mirrors STLC/Ty.lean:435. Proof reduces to
    induction on fuel; the two base cases (bool/int) close by simp. -/
@[simp]
def Ty.total_unfold
    (h : ∀ b, total (g b)) :
    total (Ty.unfold g b) := by
  simp [Ty.unfold]
  apply _root_.Gen.Total.total_indexed
  intro n
  induction n generalizing b with
  | zero => simp [Ty.unfold_aux]
  | succ n' _ih =>
    simp [Ty.unfold_aux]
    apply _root_.Gen.Total.total_bind <;> try apply h
    intro τ _
    cases τ <;> simp

@[simp, aesop safe (rule_sets := [totality])]
theorem total_arbTy : total arbTy := by
  simp [Gen.arbTy]

@[simp, aesop safe (rule_sets := [totality])]
theorem total_Ty_caseTy
    {gb : (τ = Ty.bool) → Gen α}
    {gi : (τ = Ty.int)  → Gen α}
    (hb : ∀ h, total (gb h))
    (hi : ∀ h, total (gi h)) :
    total (Gen.caseTy τ (fun h => gb h) (fun h => gi h)) := by
  cases τ
  case bool => exact hb rfl
  case int  => exact hi rfl

end Total

end Gen

-- ── PrettyPrint (nice-to-have) ──────────────────────────────────────

namespace PrettyPrint

def Ty.toString : Ty → String
  | .bool => "bool"
  | .int  => "int"

instance : ToString Ty where
  toString := Ty.toString

end PrettyPrint

-- ── Recursor-form as_or / deforest_eq. critical for Palamedes ──────

theorem Ty.deforest_eq
    {b bb bi : β} :
    Ty.rec bb bi τ = b ↔
    Ty.rec (bb = b) (bi = b) τ := by
  induction τ <;> aesop

theorem Ty.as_or
    {P_bool P_int : Prop} :
    Ty.rec P_bool P_int τ ↔
    (τ = .bool ∧ P_bool) ∨ (τ = .int ∧ P_int) := by
  induction τ <;> aesop

end Pythia.LanguageSemantics.Cedar
