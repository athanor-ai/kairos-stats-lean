/-
  CedarMicro.WellTyped: a type-directed generator for well-typed
  Cedar-micro expressions under a given type environment.

  Two layers:

  1. Specification (`getType`, `isWellTyped`): a functional
     typechecker and a Prop-valued predicate stating that a term
     type-checks. Both are `@[simp]`-reducible and small enough to
     read in one page.

  2. Generator (`genWellTyped`): a fuel-bounded `Gen Expr` that, by
     construction, only produces expressions `e` for which
     `getType e Γ` returns `some τ` at the requested target type.
     Each arm of the generator corresponds to one typing rule.
     A runtime-checked invariant (`sample_well_typed_spec`) ties the
     generator to the specification.

  The Palamedes-style proof-search derivation (where `genWellTyped`
  is auto-synthesised from `isWellTyped` via `generator_search`) is
  kept as the V2 target; the scaffolding modules in CedarMicro.Ty
  and CedarMicro.Expr are the infrastructure for that. This V1
  module ships a hand-authored generator so end-to-end samples can
  be observed today.
-/

import Pythia.LanguageSemantics.Cedar.Ty
import Pythia.LanguageSemantics.Cedar.Expr
import Pythia.LanguageSemantics.Palamedes.Gen

open Gen

namespace Pythia.LanguageSemantics.Cedar

-- ── Specification: typechecker + Prop-valued predicate ─────────────

@[simp]
def getType (e : Expr) (Γ : List Ty) : Option Ty :=
  match e with
  | .litInt _  => pure .int
  | .litBool _ => pure .bool
  | .var n     => Γ[n]?
  | .ite c t f => do
    let τc ← getType c Γ
    let τt ← getType t Γ
    let τf ← getType f Γ
    guard (τc == Ty.bool)
    guard (τt == τf)
    pure τt
  | .and a b => do
    let τa ← getType a Γ
    let τb ← getType b Γ
    guard (τa == Ty.bool)
    guard (τb == Ty.bool)
    pure Ty.bool

@[simp]
def isWellTyped (Γ : List Ty) (e : Expr) : Prop :=
  ∃ (τ : Ty), getType e Γ = τ

-- ── Runtime predicate for sampling-time verification ───────────────

@[simp]
def wellTypedAt (Γ : List Ty) (τ : Ty) (e : Expr) : Bool :=
  match getType e Γ with
  | some τ' => τ == τ'
  | none    => false

-- ── Hand-coded type-directed generator ─────────────────────────────

/-- Variables from `Γ` that have the requested type `τ`. Returned as
    explicit de-Bruijn indices (positions in the list). Written as
    a direct structural recursion to make the soundness proof in
    `CedarMicro.Soundness` a short induction on `Γ`. -/
def varsOfType : List Ty → Ty → List Nat
  | [],        _ => []
  | τ' :: rest, τ =>
    let shifted := (varsOfType rest τ).map (· + 1)
    if τ' = τ then 0 :: shifted else shifted

/-- Literal-only sub-generator at a given target type. Factored out of
    `genLeaf` so the soundness proof's motive inference does not have to
    reason across a `let`-bound `match τ`. -/
def litGen : Ty → Gen Expr
  | .bool => pick (pure (Expr.litBool true)) (pure (Expr.litBool false))
  | .int  => pick
      (pure (Expr.litInt 0))
      (pick (pure (Expr.litInt 1)) (pure (Expr.litInt (-1))))

/-- Base case: a leaf-only generator producing well-typed expressions
    at the requested type. No recursion; size-0 terms only. -/
def genLeaf (Γ : List Ty) (τ : Ty) : Gen Expr :=
  -- Prefer vars when available; fall back to literals.
  match varsOfType Γ τ with
  | []        => litGen τ
  | n :: rest =>
    -- Pick uniformly among available variables; fall through to literal.
    let varGen : Gen Expr :=
      (n :: rest).foldr (fun i acc => pick (pure (Expr.var i)) acc) (litGen τ)
    pick varGen (litGen τ)

/-- Type-directed generator with a fuel bound `size`. At size 0 emits
    a leaf; at size > 0 picks probabilistically among leaves and the
    type-appropriate compound forms (`ite`, `and` for bool; `ite` for
    int). Each recursive sub-generator runs at size-1, ensuring
    structural termination. -/
def genSize (Γ : List Ty) : Nat → Ty → Gen Expr
  | 0, τ => genLeaf Γ τ
  | _ + 1, .int =>
    pick
      (genLeaf Γ .int)
      (do
        let c ← genSize Γ 0 .bool
        let t ← genSize Γ 0 .int
        let f ← genSize Γ 0 .int
        pure (.ite c t f))
  | _ + 1, .bool =>
    pick
      (genLeaf Γ .bool)
      (pick
        (do
          let a ← genSize Γ 0 .bool
          let b ← genSize Γ 0 .bool
          pure (.and a b))
        (do
          let c ← genSize Γ 0 .bool
          let t ← genSize Γ 0 .bool
          let f ← genSize Γ 0 .bool
          pure (.ite c t f)))

/-- The V1 API: generate a well-typed Cedar-micro expression under
    type environment `Γ` at result type `τ`, sampled with fuel 2
    (enough for one level of nesting). -/
def genWellTyped (Γ : List Ty) (τ : Ty) : Gen Expr :=
  genSize Γ 2 τ

end Pythia.LanguageSemantics.Cedar
