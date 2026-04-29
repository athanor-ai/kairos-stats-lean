/-
  CedarMicro.Expr. the Cedar-micro expression grammar with full Palamedes
  scaffolding so `generator_search (fun e => isWellTyped Γ e)` closes.

  Port of `palamedes-lean/Palamedes/Data/STLC/Term.lean` with the
  constructor set replaced.
-/

import Pythia.LanguageSemantics.Palamedes.Gen
import Pythia.LanguageSemantics.Palamedes.CorrectGen
import Pythia.LanguageSemantics.Palamedes.Total
import Pythia.LanguageSemantics.Cedar.Ty

namespace Pythia.LanguageSemantics.Cedar

inductive Expr : Type where
  | litInt  : Int → Expr
  | litBool : Bool → Expr
  | var     : Nat → Expr
  | ite     : Expr → Expr → Expr → Expr
  | and     : Expr → Expr → Expr
  deriving Repr

-- ── BaseFunctor ─────────────────────────────────────────────────────

inductive ExprF (α : Type) where
  | litInt  : Int → ExprF α
  | litBool : Bool → ExprF α
  | var     : Nat → ExprF α
  | ite     : (c t f : α) → ExprF α
  | and     : (a b : α) → ExprF α

theorem ExprF_or
    {α : Type}
    {PlitI : Int → Prop}
    {PlitB : Bool → Prop}
    {Pvar : Nat → Prop}
    {Pite : α → α → α → Prop}
    {Pand : α → α → Prop}
    {e : ExprF α} :
    ExprF.rec PlitI PlitB Pvar Pite Pand e ↔
    (∃ n, e = .litInt n ∧ PlitI n) ∨
    (∃ b, e = .litBool b ∧ PlitB b) ∨
    (∃ n, e = .var n ∧ Pvar n) ∨
    (∃ c t f, e = .ite c t f ∧ Pite c t f) ∨
    (∃ a b, e = .and a b ∧ Pand a b) := by
  cases e <;> aesop

-- ── RecursionSchemes ────────────────────────────────────────────────

def Expr.fold {α : Type}
    (zI : Int → α) (zB : Bool → α) (zn : Nat → α)
    (f_ite : α → α → α → α) (f_and : α → α → α)
    (e : Expr) : α :=
  match e with
  | .litInt n  => zI n
  | .litBool b => zB b
  | .var n     => zn n
  | .ite c t f =>
    f_ite (Expr.fold zI zB zn f_ite f_and c)
          (Expr.fold zI zB zn f_ite f_and t)
          (Expr.fold zI zB zn f_ite f_and f)
  | .and a b =>
    f_and (Expr.fold zI zB zn f_ite f_and a)
          (Expr.fold zI zB zn f_ite f_and b)

@[simp] theorem Expr.fold_litInt {n : Int} :
  Expr.fold zI zB zn f_ite f_and (.litInt n) = zI n := rfl
@[simp] theorem Expr.fold_litBool {b : Bool} :
  Expr.fold zI zB zn f_ite f_and (.litBool b) = zB b := rfl
@[simp] theorem Expr.fold_var {n : Nat} :
  Expr.fold zI zB zn f_ite f_and (.var n) = zn n := rfl
@[simp] theorem Expr.fold_ite {c t f : Expr} :
  Expr.fold zI zB zn f_ite f_and (.ite c t f) =
    f_ite (Expr.fold zI zB zn f_ite f_and c)
          (Expr.fold zI zB zn f_ite f_and t)
          (Expr.fold zI zB zn f_ite f_and f) := rfl
@[simp] theorem Expr.fold_and {a b : Expr} :
  Expr.fold zI zB zn f_ite f_and (.and a b) =
    f_and (Expr.fold zI zB zn f_ite f_and a)
          (Expr.fold zI zB zn f_ite f_and b) := rfl

def Expr.accuM [Monad m] {α σ : Type}
    (st_ite : σ → σ × σ × σ) (st_and : σ → σ × σ)
    (zI : Int → σ → m α) (zB : Bool → σ → m α) (zn : Nat → σ → m α)
    (f_ite : α → α → α → σ → m α) (f_and : α → α → σ → m α)
    (e : Expr) (i : σ) : m α :=
  match e with
  | .litInt n  => zI n i
  | .litBool b => zB b i
  | .var n     => zn n i
  | .ite c t f => do
    let (sc, st, sf) := st_ite i
    let vc ← Expr.accuM st_ite st_and zI zB zn f_ite f_and c sc
    let vt ← Expr.accuM st_ite st_and zI zB zn f_ite f_and t st
    let vf ← Expr.accuM st_ite st_and zI zB zn f_ite f_and f sf
    f_ite vc vt vf i
  | .and a b => do
    let (sa, sb) := st_and i
    let va ← Expr.accuM st_ite st_and zI zB zn f_ite f_and a sa
    let vb ← Expr.accuM st_ite st_and zI zB zn f_ite f_and b sb
    f_and va vb i

-- ── Unfold ──────────────────────────────────────────────────────────

open Gen

private def Expr.unfold_aux (n : Nat) (f : α → Gen (ExprF α)) (x : α) : Gen (Option Expr) :=
  match n with
  | 0 => pure none
  | n + 1 => do
    match (← f x) with
    | .litInt i  => pure (some (.litInt i))
    | .litBool b => pure (some (.litBool b))
    | .var n     => pure (some (.var n))
    | .ite xc xt xf => do
      let ec ← Expr.unfold_aux n f xc
      let et ← Expr.unfold_aux n f xt
      let ef ← Expr.unfold_aux n f xf
      pure (do pure (.ite (← ec) (← et) (← ef)))
    | .and xa xb => do
      let ea ← Expr.unfold_aux n f xa
      let eb ← Expr.unfold_aux n f xb
      pure (do pure (.and (← ea) (← eb)))

@[simp]
theorem Expr.unfold_aux_monotonic :
    some v ∈ 〚Expr.unfold_aux n f x〛 →
    some v ∈ 〚Expr.unfold_aux (n + m) f x〛 := by
  induction n generalizing v f x
  case zero =>
    simp [Expr.unfold_aux]
  case succ α n' _ih =>
    unfold Expr.unfold_aux
    simp
    intro e he h
    cases e <;> simp_all +arith
    case litInt i  => exists ExprF.litInt i
    case litBool b => exists ExprF.litBool b
    case var n     => exists ExprF.var n
    case ite xc xt xf =>
      replace ⟨oc, hc, ot, ht, of_, hf, h⟩ := h
      cases oc <;> simp_all
      case some vc =>
        cases ot <;> simp_all
        case some vt =>
          cases of_ <;> simp_all
          case some vf =>
            exists ExprF.ite xc xt xf; simp_all
            exists vc; simp_all
            exists vt; simp_all
            exists vf; simp_all
    case and xa xb =>
      replace ⟨oa, ha, ob, hb, h⟩ := h
      cases oa <;> simp_all
      case some va =>
        cases ob <;> simp_all
        case some vb =>
          exists ExprF.and xa xb; simp_all
          exists va; simp_all
          exists vb; simp_all

@[irreducible]
def Expr.unfold (f : α → Gen (ExprF α)) (x : α) : Gen Expr :=
  .indexed (fun n => Expr.unfold_aux n f x)

@[simp]
def Expr.unfold_support (P : α → ExprF α → Prop) (x : α) (e : Expr) : Prop :=
  match e with
  | .litInt i  => P x (.litInt i)
  | .litBool b => P x (.litBool b)
  | .var n     => P x (.var n)
  | .ite c t f => ∃ xc xt xf,
    P x (.ite xc xt xf) ∧
    Expr.unfold_support P xc c ∧
    Expr.unfold_support P xt t ∧
    Expr.unfold_support P xf f
  | .and a b => ∃ xa xb,
    P x (.and xa xb) ∧
    Expr.unfold_support P xa a ∧
    Expr.unfold_support P xb b

/-- The load-bearing simp rule Palamedes's `generator_search` needs:
    the support of an `Expr.unfold` is characterised by
    `Expr.unfold_support` applied to the step function's support.

    Ported (in structure) from `palamedes-lean/Palamedes/Data/STLC/
    Term.lean:189-319` with the five Cedar-micro constructors in
    place of STLC's four. The flat arms (`litInt`, `litBool`, `var`)
    are symmetric to STLC `var`; the ternary `ite` arm parallels
    STLC `app` with one extra sub-term; the binary `and` arm
    parallels STLC `app`. -/
@[simp]
theorem Expr.support_unfold {α : Type} {f : α → Gen (ExprF α)} {x : α} :
    _root_.Gen.support (Expr.unfold f x) =
      Expr.unfold_support (fun x' => _root_.Gen.support (f x')) x := by
  funext e
  simp_all
  induction e generalizing x
  case litInt i =>
    apply Iff.intro
    · intro h
      simp_all [Expr.unfold]
      replace ⟨n, h⟩ := h
      cases n <;> simp_all [Expr.unfold_aux]
      case succ n' =>
        replace ⟨v', hv', h⟩ := h
        cases v' <;> simp_all
        case ite xc xt xf =>
          replace ⟨oc, hc, ot, ht, of_, hf, h⟩ := h
          cases oc <;> simp_all
          cases ot <;> simp_all
          cases of_ <;> simp_all
        case and xa xb =>
          replace ⟨oa, ha, ob, hb, h⟩ := h
          cases oa <;> simp_all
          cases ob <;> simp_all
    · intro h
      simp_all [Expr.unfold]
      exists 1
      exists ExprF.litInt i
  case litBool b =>
    apply Iff.intro
    · intro h
      simp_all [Expr.unfold]
      replace ⟨n, h⟩ := h
      cases n <;> simp_all [Expr.unfold_aux]
      case succ n' =>
        replace ⟨v', hv', h⟩ := h
        cases v' <;> simp_all
        case ite xc xt xf =>
          replace ⟨oc, hc, ot, ht, of_, hf, h⟩ := h
          cases oc <;> simp_all
          cases ot <;> simp_all
          cases of_ <;> simp_all
        case and xa xb =>
          replace ⟨oa, ha, ob, hb, h⟩ := h
          cases oa <;> simp_all
          cases ob <;> simp_all
    · intro h
      simp_all [Expr.unfold]
      exists 1
      exists ExprF.litBool b
  case var n =>
    apply Iff.intro
    · intro h
      simp_all [Expr.unfold]
      replace ⟨k, h⟩ := h
      cases k <;> simp_all [Expr.unfold_aux]
      case succ k' =>
        replace ⟨v', hv', h⟩ := h
        cases v' <;> simp_all
        case ite xc xt xf =>
          replace ⟨oc, hc, ot, ht, of_, hf, h⟩ := h
          cases oc <;> simp_all
          cases ot <;> simp_all
          cases of_ <;> simp_all
        case and xa xb =>
          replace ⟨oa, ha, ob, hb, h⟩ := h
          cases oa <;> simp_all
          cases ob <;> simp_all
    · intro h
      simp_all [Expr.unfold]
      exists 1
      exists ExprF.var n
  case ite c t f ihc iht ihf =>
    apply Iff.intro
    · intro h
      simp_all [Expr.unfold]
      replace ⟨n, h⟩ := h
      cases n <;> simp_all [Expr.unfold_aux]
      case succ n =>
        replace ⟨vf, hvf, h⟩ := h
        cases vf <;> simp_all
        case ite xc xt xf =>
          replace ⟨oc, hc, ot, ht, of_, hf, h⟩ := h
          cases oc <;> simp_all
          case some vc =>
            cases ot <;> simp_all
            case some vt =>
              cases of_ <;> simp_all
              case some vf =>
                exists xc, xt, xf
                apply And.intro hvf
                replace ihc := @ihc xc
                replace iht := @iht xt
                replace ihf := @ihf xf
                rw [Iff.comm] at ihc iht ihf
                rw [ihc, iht, ihf]
                refine ⟨?_, ?_, ?_⟩ <;> exists n
        case and xa xb =>
          replace ⟨ov₁, hv₁, ov₂, hv₂, h⟩ := h
          cases ov₁ <;> simp_all
          cases ov₂ <;> simp_all
    · intro ⟨xc, xt, xf, habc, hc_s, ht_s, hf_s⟩
      replace ihc := @ihc xc
      rw [Iff.comm] at ihc
      rw [ihc] at hc_s
      simp [Expr.unfold] at hc_s |-
      replace ⟨hmc, nc, hc_s⟩ := hc_s
      replace iht := @iht xt
      rw [Iff.comm] at iht
      rw [iht] at ht_s
      simp [Expr.unfold] at ht_s
      replace ⟨hmt, nt, ht_s⟩ := ht_s
      replace ihf := @ihf xf
      rw [Iff.comm] at ihf
      rw [ihf] at hf_s
      simp [Expr.unfold] at hf_s
      replace ⟨hmf, nf, hf_s⟩ := hf_s
      intros
      simp_all
      exists nc + nt + nf + 1
      exists ExprF.ite xc xt xf
      simp_all
      exists some c
      simp_all [Expr.unfold_aux_monotonic]
      exists some t
      rw [show nc + nt + nf = nt + (nc + nf) from by omega]
      simp_all [Expr.unfold_aux_monotonic]
      exists some f
      rw [show nt + (nc + nf) = nf + (nc + nt) from by omega]
      simp_all [Expr.unfold_aux_monotonic]
  case and a b iha ihb =>
    apply Iff.intro
    · intro h
      simp_all [Expr.unfold]
      replace ⟨n, h⟩ := h
      cases n <;> simp_all [Expr.unfold_aux]
      case succ n =>
        replace ⟨vf, hvf, h⟩ := h
        cases vf <;> simp_all
        case ite xc xt xf =>
          replace ⟨oc, hc, ot, ht, of_, hf, h⟩ := h
          cases oc <;> simp_all
          cases ot <;> simp_all
          cases of_ <;> simp_all
        case and xa xb =>
          replace ⟨ov₁, hv₁, ov₂, hv₂, h⟩ := h
          cases ov₁ <;> simp_all
          case some va =>
            cases ov₂ <;> simp_all
            case some vb =>
              exists xa, xb
              apply And.intro hvf
              replace iha := @iha xa
              replace ihb := @ihb xb
              rw [Iff.comm] at iha ihb
              rw [iha, ihb]
              apply And.intro <;> exists n
    · intro ⟨xa, xb, hab, ha, hb⟩
      replace iha := @iha xa
      rw [Iff.comm] at iha
      rw [iha] at ha
      simp [Expr.unfold] at ha |-
      replace ⟨hma, na, ha⟩ := ha
      replace ihb := @ihb xb
      rw [Iff.comm] at ihb
      rw [ihb] at hb
      simp [Expr.unfold] at hb
      replace ⟨hmb, nb, hb⟩ := hb
      intros
      simp_all
      exists na + nb + 1
      exists ExprF.and xa xb
      simp_all
      exists some a
      simp_all [Expr.unfold_aux_monotonic]
      exists some b
      rw [Nat.add_comm]
      simp_all [Expr.unfold_aux_monotonic]

theorem Expr.support_unfold_congr
    {α : Type} {f f' : α → Gen (ExprF α)} {b : α}
    (hf : ∀ {b}, _root_.Gen.support (f b) = _root_.Gen.support (f' b)) :
    _root_.Gen.support (Expr.unfold f b) = _root_.Gen.support (Expr.unfold f' b) := by
  rw [Expr.support_unfold, Expr.support_unfold]
  congr
  funext x' e
  rw [hf]

-- ── Total / Aesop registration ──────────────────────────────────────

namespace Gen

namespace Total

@[simp, aesop safe (rule_sets := [totality])]
def Expr.total_unfold
    (h : ∀ b, _root_.Gen.total (g b)) :
    _root_.Gen.total (Expr.unfold g b) := by
  simp [Expr.unfold]
  apply _root_.Gen.Total.total_indexed
  intro n
  induction n generalizing b with
  | zero => simp [Expr.unfold_aux]
  | succ n' ih =>
    simp [Expr.unfold_aux]
    apply _root_.Gen.Total.total_bind <;> try apply h
    intro t _
    cases t <;> (simp [ih] ; try {
      -- recursive arms (ite / and) chain multiple binds; unfold each
      repeat (apply _root_.Gen.Total.total_bind <;> try apply ih)
      intro _ _
      cases ‹Option _› <;> simp [ih]
    })

end Total

end Gen

-- ── as_or / deforest_eq in .rec form ────────────────────────────────

theorem Expr.deforest_eq
    {b bI bB bV : β}
    {bIte : Expr → Expr → Expr → β}
    {bAnd : Expr → Expr → β} :
    Expr.rec
      (fun _ => bI) (fun _ => bB) (fun _ => bV)
      (fun c t f _ _ _ => bIte c t f)
      (fun a b_ _ _ => bAnd a b_) e = b ↔
    Expr.rec
      (fun _ => bI = b) (fun _ => bB = b) (fun _ => bV = b)
      (fun c t f _ _ _ => bIte c t f = b)
      (fun a b_ _ _ => bAnd a b_ = b) e := by
  induction e <;> aesop

theorem Expr.as_or
    {PlitI : Int → Prop}
    {PlitB : Bool → Prop}
    {Pvar : Nat → Prop}
    {Pite : Expr → Expr → Expr → Prop}
    {Pand : Expr → Expr → Prop} :
    Expr.rec
      PlitI PlitB Pvar
      (fun c t f _ _ _ => Pite c t f)
      (fun a b_ _ _ => Pand a b_) e ↔
    (∃ n, e = .litInt n ∧ PlitI n) ∨
    (∃ b, e = .litBool b ∧ PlitB b) ∨
    (∃ n, e = .var n ∧ Pvar n) ∨
    (∃ c t f, e = .ite c t f ∧ Pite c t f) ∨
    (∃ a b, e = .and a b ∧ Pand a b) := by
  induction e <;> aesop

end Pythia.LanguageSemantics.Cedar
