import Pythia.LanguageSemantics.Palamedes.Gen
import Pythia.LanguageSemantics.Palamedes.CorrectGen
import Pythia.LanguageSemantics.Palamedes.Total

section TypeDef

inductive Ty : Type where
  | unit
  | arrow (τ₁ τ₂ : Ty)
  deriving DecidableEq, Repr

end TypeDef

section BaseFunctor

inductive TyF (α : Type) where
  | unit : TyF α
  | arrow : (τ₁ : α) → (τ₂ : α) → TyF α

theorem TyF_or
    {α : Type}
    {P : Prop}
    {Q : α → α → Prop}
    {τ : TyF α} :
    TyF.rec P Q τ ↔ (P ∧ τ = .unit) ∨ (∃ b₁ b₂, τ = .arrow b₁ b₂ ∧ Q b₁ b₂) := by
  match τ with
  | .unit => simp
  | .arrow _ _ => aesop

end BaseFunctor

section RecursionSchemes

def Ty.fold
    {α : Type}
    (f : α → α → α)
    (z : α)
    (τ : Ty) :
    α :=
  match τ with
  | .unit => z
  | .arrow τ₁ τ₂ => f (Ty.fold f z τ₁) (Ty.fold f z τ₂)

@[simp] theorem Ty.fold_unit : Ty.fold f z .unit = z := rfl
@[simp] theorem Ty.fold_arrow {τ₁ τ₂ : Ty} {f : α → α → α} {z} :
    Ty.fold f z (.arrow τ₁ τ₂) = f (Ty.fold f z τ₁) (Ty.fold f z τ₂) := rfl

def Ty.accuM
    [Monad m]
    {α σ : Type}
    (st : σ → σ × σ)
    (f : α → α → σ → m α)
    (z : σ → m α)
    (t : Ty)
    (i : σ) :
    m α :=
  match t with
  | .unit => z i
  | .arrow τ₁ τ₂ => do
    let (s₁, s₂) := st i
    f (← Ty.accuM st f z τ₁ s₁) (← Ty.accuM st f z τ₂ s₂) i

@[simp] theorem Ty.accuM_unit
  [Monad m] {α σ} {st : σ → σ × σ} {f : α → α → σ → m α} {z : σ → m α} {i : σ} :
  Ty.accuM st f z (.unit : Ty) i = z i := rfl
@[simp] theorem Ty.accuM_arrow
  [Monad m] {α σ} {st : σ → σ × σ} {f : α → α → σ → m α} {z : σ → m α}
      {i : σ} {τ₁ τ₂ : Ty} :
  Ty.accuM st f z (.arrow τ₁ τ₂) i =
   (do
    let (s₁, s₂) := st i
    f (← Ty.accuM st f z τ₁ s₁) (← Ty.accuM st f z τ₂ s₂) i) := by rfl

end RecursionSchemes

section Unfold

open Gen

private def Ty.unfold_aux (n : Nat) (f : α → Gen (TyF α)) (x : α) : Gen (Option Ty) :=
  match n with
  | 0 => pure none
  | n + 1 => do
    match (← f x) with
    | .unit => pure (some .unit)
    | .arrow b₁ b₂ => do
      let τ₁ ← Ty.unfold_aux n f b₁
      let τ₂ ← Ty.unfold_aux n f b₂
      pure (do pure (.arrow (← τ₁) (← τ₂)))

@[simp]
theorem Ty.unfold_aux_monotonic :
    some v ∈ 〚Ty.unfold_aux n f b〛 →
    some v ∈ 〚Ty.unfold_aux (n + m) f b〛 := by
  induction n generalizing v f b
  case zero =>
    simp [Ty.unfold_aux]
  case succ n' ih =>
    unfold Ty.unfold_aux
    simp
    intro τ hτ h
    cases τ <;> simp_all +arith
    case unit =>
      exists TyF.unit
    case arrow τ₁ τ₂ =>
      replace ⟨ ov₁, h₁, ov₂, h₂, h ⟩ := h
      cases ov₁ <;> simp_all
      case some v₁ =>
        cases ov₂ <;> simp_all
        case some v₂ =>
        exists (TyF.arrow τ₁ τ₂)
        simp_all
        exists v₁
        simp_all
        exists v₂
        simp_all

@[irreducible]
def Ty.unfold (f : α → Gen (TyF α)) (x : α) : Gen Ty :=
  .indexed (fun n => Ty.unfold_aux n f x)

@[simp]
def Ty.unfold_support (P : α → TyF α → Prop) (x : α) (τ : Ty) : Prop :=
  match τ with
  | .unit => P x .unit
  | .arrow τ₁ τ₂ => ∃ b₁ b₂,
    P x (.arrow b₁ b₂) ∧
    Ty.unfold_support P b₁ τ₁ ∧
    Ty.unfold_support P b₂ τ₂

@[simp]
theorem Ty.support_unfold :
    support (Ty.unfold f x) = Ty.unfold_support (fun x' => support (f x')) x := by
  funext τ
  simp_all
  induction τ generalizing x with
  | unit =>
    apply Iff.intro
    . intro h
      simp_all [unfold]
      replace ⟨n, h⟩ := h
      cases n <;> simp_all [Ty.unfold_aux]
      case succ n' =>
        replace ⟨v', hv', h⟩ := h
        cases v' <;> simp_all
        case arrow τ₁ τ₂ =>
          replace ⟨ov₁, h₁, ov₂, h₂, h⟩ := h
          cases ov₁ <;> simp_all
          cases ov₂ <;> simp_all
    . intros h
      simp_all [unfold]
      exists 1
      exists TyF.unit
  | arrow τ₁ τ₂ ih₁ ih₂ =>
    apply Iff.intro
    . intro h
      simp_all [unfold]
      replace ⟨n, h⟩ := h
      cases n <;> simp_all [Ty.unfold_aux]
      case succ n =>
        replace ⟨v', hv', h⟩ := h
        cases v' <;> simp_all
        case arrow b₁ b₂ =>
          replace ⟨ov₁, hv₁, ov₂, hv₂, h⟩ := h
          cases ov₁ <;> simp_all
          case some v₁ =>
            cases ov₂ <;> simp_all
            case some v₂ =>
              exists b₁, b₂
              apply And.intro hv'
              rw [← @ih₁ b₁, ← @ih₂ b₂]
              apply And.intro <;> exists n
    . intro ⟨b₁, b₂, hx, h₁, h₂⟩
      rw [← @ih₁ b₁] at h₁
      simp [unfold] at h₁ ⊢
      replace ⟨hm₁, n₁, h₁⟩ := h₁
      rw [← @ih₂ b₂] at h₂
      simp [unfold] at h₂
      replace ⟨hm₂, n₂, h₂⟩ := h₂
      simp_all
      exists (n₁ + n₂ + 1)
      exists TyF.arrow b₁ b₂
      simp_all
      exists (some τ₁)
      simp_all [Ty.unfold_aux_monotonic]
      exists (some τ₂)
      rw [Nat.add_comm]
      simp_all [Ty.unfold_aux_monotonic]

theorem Ty.support_unfold_congr
    {hf : ∀ {b}, support (f b) = support (f' b)} :
    support (Ty.unfold f b) = support (Ty.unfold f' b) := by
  aesop

end Unfold

section FoldConversions

theorem Ty.fold_accu_Option_basic
    {α : Type}
    {v : α}
    {τ : Ty}
    {z : α}
    {f : α → α → α} :
    Ty.fold f z τ = v ↔
    Ty.accuM
      (fun _ => ((), ()))
      (fun τ₁ τ₂ _ => some (f τ₁ τ₂))
      (fun _ => some z)
      τ
      () = some v := by
    induction τ generalizing v <;> simp_all [Ty.fold, Ty.accuM]
    case arrow τ₁ τ₂ ih₁ ih₂ =>
        replace ih₁ := @ih₁ (Ty.fold f z τ₁)
        replace ih₂ := @ih₂ (Ty.fold f z τ₂)
        simp_all

theorem Ty.fold_accu_Option_true
    {τ : Ty}
    {f : Bool → Bool → Bool}
    (h : ∀ acc₁ acc₂, f acc₁ acc₂ = (acc₁ && acc₂)) :
    Ty.fold f true τ = true ↔
    Ty.accuM
      (fun _ => ((), ()))
      (fun _ _ _ => some ())
      (fun _ => some ())
      τ
      () = some () := by
    induction τ <;> simp_all [Ty.fold, Ty.accuM]
    case arrow τ₁ τ₂ ih₁ ih₂ =>
        apply Iff.intro <;> intro hf
        . -- (->)
          generalize hv₁ : fold f true τ₁ = v₁
          generalize hv₂ : fold f true τ₂ = v₂
          cases v₁ <;> cases v₂ <;>
            simp_all
        . -- (<-)
          rw [Option.bind_eq_some_iff] at hf
          replace ⟨ v₁, hf ⟩ := hf
          rw [Option.bind_eq_some_iff] at hf
          replace ⟨ h₁, ⟨ v₂, h₂ ⟩ ⟩ := hf
          simp_all

theorem Ty.fold_accu_Option_function
    {α σ : Type}
    {i : σ}
    {v : α}
    {τ : Ty}
    {z : (σ → α)}
    {f : (σ → α) → (σ → α) → (σ → α)}
    {g : α → α → σ → Option α}
    {st₁ st₂ : σ → σ}
    (h : ∀ acc₁ acc₂ s w,
      f acc₁ acc₂ s = w ↔ (do g (← acc₁ (st₁ s)) (← acc₂ (st₂ s)) s) = some w)
    :
    Ty.fold f z τ i = v ↔
    Ty.accuM
      (fun s => (st₁ s, st₂ s))
      g
      (fun s => some (z s))
      τ
      i = some v := by
    induction τ generalizing v i <;> simp_all [Ty.fold, Ty.accuM, Option.bind_eq_some_iff]
    case arrow τ₁ τ₂ ih₁ ih₂ =>
      apply Iff.intro <;> intro hg
      . -- (->)
        exists (Ty.fold f z τ₁ (st₁ i))
        rw [← ih₁]; simp_all
        exists (Ty.fold f z τ₂ (st₂ i))
        rw [← ih₂]; simp_all
      . -- (<-)
        replace ⟨ v₁, h₁, v₂, h₂, hg ⟩ := hg
        rw [← ih₁] at h₁
        rw [← ih₂] at h₂
        rw [h₁, h₂]
        apply hg

theorem Ty.fold_accu_Option_function_true
    {σ : Type}
    {i : σ}
    {τ : Ty}
    {f : (σ → Bool) → (σ → Bool) → (σ → Bool)}
    {g : σ → Bool}
    {st₁ st₂ : σ → σ}
    (h : ∀ acc₁ acc₂ s,
      f acc₁ acc₂ s = true ↔ (do (return (g s) && (← acc₁ (st₁ s)) && (← acc₂ (st₂ s)))) = some true)
    :
    Ty.fold f (fun _ => true) τ i = true ↔
    Ty.accuM
      (fun s => (st₁ s, st₂ s))
      (fun _ _ s => guard $ g s)
      (fun _ => some ())
      τ
      i = some () := by
    induction τ generalizing i <;> simp_all [Ty.fold, Ty.accuM, Option.bind_eq_some_iff, guard]
    case arrow τ₁ τ₂ ih₁ ih₂ =>
      apply Iff.intro <;> intro hg <;> simp_all
      replace ⟨⟨ v₁, h₁ ⟩, ⟨ v₂, h₂ ⟩ , hg⟩ := hg; simp_all

end FoldConversions

section FoldCoercion

theorem Ty.coerce_to_fold
    {τ : Ty}
    {f : Ty → α} -- function to be coerced
    {z : α}
    {g : α → α → α}
    (h₁ : f .unit = z := by rfl)
    (h₂ : ∀ τ₁ τ₂, f (.arrow τ₁ τ₂) = g (f τ₁) (f τ₂) := by intros; simp_all; rfl) :
    f τ = τ.fold g z := by
  induction τ <;> simp_all

theorem Ty.coerce_match
  {τ : Ty}
  {f : Ty → α}
  {z : α}
  {g : Ty → Ty → α}
  (h₁ : f .unit = z)
  (h₂ : ∀ τ₁ τ₂, f (.arrow τ₁ τ₂) = g τ₁ τ₂) :
  f τ = Ty.rec z (fun τ₁ τ₂ _ _ => g τ₁ τ₂) τ := by
  induction τ <;> simp_all

end FoldCoercion

section FoldMerging

theorem Ty.merge_accuM
    {τ : Ty}
    {st₁ : σ₁ → σ₁ × σ₁}
    {st₂ : σ₂ → σ₂ × σ₂}
    {f₁ : α₁ → α₁ → σ₁ → Option α₁}
    {f₂ : α₂ → α₂ → σ₂ → Option α₂}
    {z₁ : σ₁ → Option α₁} {z₂ : σ₂ → Option α₂}
    {i₁ : σ₁} {i₂ : σ₂}
    {x₁ : α₁} {x₂ : α₂}
    :
    (τ.accuM st₁ f₁ z₁ i₁ = some x₁ ∧ τ.accuM st₂ f₂ z₂ i₂ = some x₂)
    ↔
    (τ.accuM
      (fun (s₁, s₂) => (((st₁ s₁).1, (st₂ s₂).1), ((st₁ s₁).2, (st₂ s₂).2)))
      (fun (x₁₁, x₁₂) (x₂₁, x₂₂) (s₁, s₂) => do (← f₁ x₁₁ x₂₁ s₁, ← f₂ x₁₂ x₂₂ s₂))
      (fun (s₁, s₂) => do (← z₁ s₁, ← z₂ s₂))
      (i₁, i₂) = some (x₁, x₂)) := by
  induction τ generalizing i₁ i₂ x₁ x₂ <;> simp_all
  case unit =>
    apply Iff.intro <;> intro h
    . -- (->)
      rw [h.left, h.right]
      simp
    . -- (<-)
      generalize hx₁ : (z₁ i₁) = x₁
      generalize hx₂ : (z₂ i₂) = x₂
      cases x₁ <;> cases x₂ <;> simp_all
  case arrow τ₁ τ₂ ih₁ ih₂ =>
    apply Iff.intro
    . -- (->)
      intro ⟨ h₁, h₂ ⟩
      rw [Option.bind_eq_some_iff] at h₁ h₂
      replace ⟨ v₁₁, ⟨ hv₁₁, h₁ ⟩  ⟩ := @h₁
      replace ⟨ v₁₂, ⟨ hv₁₂, h₂ ⟩  ⟩ := @h₂
      rw [Option.bind_eq_some_iff] at h₁ h₂
      replace ⟨ v₂₁, ⟨ hv₂₁, h₁ ⟩  ⟩ := @h₁
      replace ⟨ v₂₂, ⟨ hv₂₂, h₂ ⟩  ⟩ := @h₂
      replace ih₁ := @ih₁ (st₁ i₁).1 (st₂ i₂).1 v₁₁ v₁₂
      replace ih₂ := @ih₂ (st₁ i₁).2 (st₂ i₂).2 v₂₁ v₂₂
      simp_all
    . -- (<-)
      intro h
      rw [Option.bind_eq_some_iff] at h
      replace ⟨ ⟨ v₁₁, v₁₂ ⟩ , ⟨ h₁, h ⟩ ⟩ := @h
      rw [Option.bind_eq_some_iff] at h
      replace ⟨ ⟨ v₂₁, v₂₂ ⟩ , ⟨ h₂, h ⟩ ⟩ := @h
      rw [Option.bind_eq_some_iff] at h
      replace ⟨ v₁, ⟨ hv₁ , h ⟩ ⟩ := @h
      rw [Option.bind_eq_some_iff] at h
      replace ⟨ v₂, ⟨ hv₂ , h ⟩ ⟩ := @h
      replace ih₁ := @ih₁ (st₁ i₁).1 (st₂ i₂).1 v₁₁ v₁₂
      replace ih₂ := @ih₂ (st₁ i₁).2 (st₂ i₂).2 v₂₁ v₂₂
      simp_all

end FoldMerging

namespace Gen

namespace CorrectGen

@[reducible]
def Ty.s_unfold
    {α σ : Type}
    {st : σ → σ × σ}
    {f : α → α → σ → Option α}
    {z : σ → Option α}
    {s : σ}
    {b : α}
    (g : (b : α) → (s : σ) → CorrectGen
      (fun (τ : TyF α) =>
        (z s = some b ∧ τ = .unit) ∨
        (∃ b₁ b₂, f b₁ b₂ s = some b ∧ τ = .arrow b₁ b₂))) :
    CorrectGen (fun v => Ty.accuM st f z v s = some b) :=
  Subtype.mk
    (Ty.unfold (fun (b, s) => do
      match (← (g b s).val) with
      | .unit => pure .unit
      | .arrow b₁ b₂ => pure (.arrow (b₁, (st s).1) (b₂, (st s).2))) (b, s)) <| by
    rw [Ty.support_unfold]
    funext τ
    induction τ generalizing b s <;> simp_all
    case unit =>
      apply Iff.intro <;> intro h
      . replace ⟨ τ', ⟨ hτ', h ⟩ ⟩ := h
        cases τ' <;> simp_all [(g b s).property]
      . exists TyF.unit
        simp_all [(g b s).property]
    case arrow τ₁ τ₂ ih₁ ih₂ =>
      apply Iff.intro <;> intro h
      . replace ⟨ b₁, s₁, b₂, s₂, ⟨ ⟨ τ', ⟨ hτ' , h ⟩  ⟩, ⟨ hτ₁, hτ₂ ⟩ ⟩ ⟩ := h
        cases τ' <;> simp_all [(g b s).property]
      . rw [Option.bind_eq_some_iff] at h
        replace ⟨ b₁, ⟨ h₁, h ⟩ ⟩ := h
        rw [Option.bind_eq_some_iff] at h
        replace ⟨ b₂, ⟨ h₂, h ⟩ ⟩ := h
        exists b₁, (st s).fst, b₂, (st s).snd
        apply And.intro
        . exists TyF.arrow b₁ b₂
          simp_all [(g b s).property]
        . simp_all

end CorrectGen

namespace Total

@[simp]
def Ty.total_unfold
    (h : ∀ b, total (g b)) :
    total (Ty.unfold g b) := by
  simp [Ty.unfold]
  apply total_indexed
  intro n
  induction n generalizing b with
  | zero => simp [Ty.unfold_aux]
  | succ n' ih =>
    simp [Ty.unfold_aux]
    apply total_bind <;> try apply h
    intro τ h
    cases τ <;> simp [ih]

end Total

end Gen

namespace Gen

@[irreducible]
def arbTy : Gen Ty := Ty.unfold
  (fun _ => pick
    (pure TyF.unit)
    (pure (TyF.arrow PUnit.unit PUnit.unit)))
  PUnit.unit

def caseTy
    (τ : Ty)
    (gu : (τ = Ty.unit) → Gen α)
    (ga : (τ₁ τ₂ : Ty) → (τ = Ty.arrow τ₁ τ₂) → Gen α) :
    Gen α :=
  match τ with
  | .unit => gu rfl
  | .arrow τ₁ τ₂ => (ga τ₁ τ₂ rfl)

@[simp]
theorem support_arbTy :
    support arbTy = fun _ => True := by
  simp [arbTy]
  funext v
  induction v <;> simp_all

@[simp]
def support_Ty_caseTy
    {gu : (τ = Ty.unit) → Gen α}
    {ga : (τ₁ τ₂ : Ty) → (τ = Ty.arrow τ₁ τ₂) → Gen α} :
    support (caseTy
            τ
            (fun h => gu h)
            (fun τ₁ τ₂ h => ga τ₁ τ₂ h)) =
    (fun a =>
      (∃ h : τ = Ty.unit, a ∈ 〚gu h〛) ∨
      (∃ (τ₁ τ₂ : Ty) (h : τ = Ty.arrow τ₁ τ₂), a ∈ 〚ga τ₁ τ₂ h〛)) := by
  funext
  simp
  apply Iff.intro
  . intro h
    cases τ <;> aesop
  . intro h
    cases h <;> aesop

theorem support_caseTy_congr
    {unitCase : (τ = .unit) → Gen α}
    {h_unitCase : ∀ {h}, support (unitCase h) = support (unitCase' h)}
    {h_arrowCase : ∀ {τ₁ τ₂ h}, support (arrowCase τ₁ τ₂ h) = support (arrowCase' τ₁ τ₂ h)} :
    support (caseTy τ unitCase arrowCase) = support (caseTy τ unitCase' arrowCase') := by
  aesop

namespace CorrectGen

@[reducible]
def s_arbTy : @CorrectGen Ty (fun _ => True) :=
  Subtype.mk arbTy <| by
    funext v
    simp

@[reducible]
def s_caseTy
    {Q : α → Prop}
    {P : α → Ty → Prop}
    (τ : Ty)
    (h : ∀ {a}, P a τ = Q a)
    (gu : CorrectGen (fun a => P a .unit))
    (ga : (τ₁ τ₂ : Ty) → CorrectGen (fun a => P a (.arrow τ₁ τ₂))) :
    CorrectGen Q :=
    Subtype.mk
      (caseTy
        τ
        (fun _ => gu.val)
        (fun τ₁ τ₂ _ => (ga τ₁ τ₂).val)) <| by
    match τ with
    | .unit => simp [gu.property, h]
    | .arrow τ₁ τ₂ => simp [(ga τ₁ τ₂).property, h, caseTy]

end CorrectGen

namespace Total

@[simp, aesop safe (rule_sets := [totality])]
theorem total_arbTy : total arbTy := by
  simp [Gen.arbTy]

@[simp, aesop safe (rule_sets := [totality])]
theorem total_Ty_caseTy
    {gu : (τ = Ty.unit) → Gen α}
    {ga : (τ₁ τ₂ : Ty) → (τ = Ty.arrow τ₁ τ₂) → Gen α}
    (hu : ∀ h, total (gu h))
    (ha : ∀ τ₁ τ₂ h, total (ga τ₁ τ₂ h)) :
    total (Gen.caseTy τ (fun h => gu h) (fun τ₁ τ₂ h => ga τ₁ τ₂ h))
  := by
  cases τ
  case unit => exact hu rfl
  case arrow τ₁ τ₂ => simp_all only [Gen.caseTy]

end Total

end Gen

namespace PrettyPrint

def Ty.toString : Ty → String
  | .unit => "()"
  | .arrow τ₁ τ₂ => s!"({Ty.toString τ₁} → {Ty.toString τ₂})"

instance : ToString Ty where
  toString := Ty.toString

end PrettyPrint

theorem Ty.deforest_eq
    {b b_unit : β}
    {b_arrow : Ty → Ty → β} :
    Ty.rec b_unit (fun τ₁ τ₂ _ _ => b_arrow τ₁ τ₂) τ = b ↔
    Ty.rec (b_unit = b) (fun τ₁ τ₂ _ _ => b_arrow τ₁ τ₂ = b) τ := by
  induction τ <;> aesop

theorem Ty.as_or
  {P_unit : Prop}
  {P_arrow : Ty → Ty → Prop} :
  Ty.rec P_unit (fun τ₁ τ₂ _ _ => P_arrow τ₁ τ₂) τ ↔
  (τ = .unit ∧ P_unit) ∨ (∃ τ₁ τ₂, τ = .arrow τ₁ τ₂ ∧ P_arrow τ₁ τ₂) := by
  induction τ <;> aesop
