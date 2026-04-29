import Pythia.LanguageSemantics.Palamedes.Gen
import Pythia.LanguageSemantics.Palamedes.CorrectGen
import Pythia.LanguageSemantics.Palamedes.Total

section TypeDef

inductive Tree (α : Type) where
  | leaf : Tree α
  | node : (l : Tree α) → (x : α) → (r : Tree α) → Tree α

end TypeDef

section BaseFunctor

inductive TreeF (α β : Type) where
  | leaf : TreeF α β
  | node : (l : β) → (x : α) → (r : β) → TreeF α β

theorem TreeF_or
    {α β : Type}
    {P : Prop}
    {Q : β → α → β → Prop}
    {t : TreeF α β} :
    TreeF.rec P Q t ↔ (P ∧ t = .leaf) ∨ (∃ bl x br, t = .node bl x br ∧ Q bl x br) := by
  match t with
  | .leaf => simp
  | .node _ _ _ => aesop

end BaseFunctor

section RecursionSchemes

def Tree.fold
    {α β : Type}
    (f : β → α → β → β)
    (z : β)
    (t : Tree α) :
    β :=
  match t with
  | .leaf => z
  | .node l x r => f (Tree.fold f z l) x (Tree.fold f z r)

@[simp] theorem Tree.fold_leaf : Tree.fold f z .leaf = z := rfl
@[simp] theorem Tree.fold_node {x} {l r : Tree α} {f : β → α → β → β} {z} :
    Tree.fold f z (.node l x r) = f (Tree.fold f z l) x (Tree.fold f z r) := rfl

def Tree.accuM
    [Monad m]
    {α β σ : Type}
    (st : α → σ → σ × σ)
    (f : β → α → β → σ → m β)
    (z : σ → m β)
    (t : Tree α)
    (i : σ) :
    m β :=
  match t with
  | .leaf => z i
  | .node l x r => do
    let (sl, sr) := st x i
    f (← Tree.accuM st f z l sl) x (← Tree.accuM st f z r sr) i

@[simp] theorem Tree.accuM_leaf
  [Monad m] {α σ} {st : α → σ → σ × σ} {f : β → α → β → σ → m β} {z : σ → m β} {i : σ} :
  Tree.accuM st f z (.leaf : Tree α) i = z i := rfl
@[simp] theorem Tree.accuM_node
  [Monad m] {α σ} {st : α → σ → σ × σ} {f : β → α → β → σ → m β} {z : σ → m β} {i : σ} {x} {l r : Tree α} :
  Tree.accuM st f z (.node l x r) i =
   (do
    let (sl, sr) := st x i
    f (← Tree.accuM st f z l sl) x (← Tree.accuM st f z r sr) i) := by rfl

end RecursionSchemes

section Unfold

open Gen

private def Tree.unfold_aux (n : Nat) (f : β → Gen (TreeF α β)) (b : β) : Gen (Option (Tree α)) :=
  match n with
  | 0 => pure none
  | n + 1 => do
    match (← f b) with
    | .leaf => pure (some .leaf)
    | .node bl x br => do
      let l ← Tree.unfold_aux n f bl
      let r ← Tree.unfold_aux n f br
      pure (do pure (.node (← l) x (← r)))

@[simp]
theorem Tree.unfold_aux_monotonic :
    some v ∈ 〚Tree.unfold_aux n f b〛 →
    some v ∈ 〚Tree.unfold_aux (n + m) f b〛 := by
  induction n generalizing v f b
  case zero =>
    simp [Tree.unfold_aux]
  case succ n' ih =>
    unfold Tree.unfold_aux
    simp
    intro t ht h
    cases t <;> simp_all +arith
    case leaf =>
      exists TreeF.leaf
    case node l x r =>
      replace ⟨ ovl, hl, ovr, hr, h ⟩ := h
      cases ovl <;> simp_all
      case some vl =>
        cases ovr <;> simp_all
        case some vr =>
        exists (TreeF.node l x r)
        simp_all
        exists vl
        simp_all
        exists vr
        simp_all

@[irreducible]
def Tree.unfold (f : β → Gen (TreeF α β)) (v : β) : Gen (Tree α) :=
  .indexed (fun n => Tree.unfold_aux n f v)

@[simp]
def Tree.unfold_support (P : β → TreeF α β → Prop) (b : β) (t : Tree α) : Prop :=
  match t with
  | .leaf => P b .leaf
  | .node l x r => ∃ bl br,
    P b (.node bl x br) ∧
    Tree.unfold_support P bl l ∧
    Tree.unfold_support P br r

@[simp]
theorem Tree.support_unfold :
    support (Tree.unfold f b) = Tree.unfold_support (fun b' => support (f b')) b := by
  funext s
  simp_all
  induction s generalizing b with
  | leaf =>
    apply Iff.intro
    . simp_all [Tree.unfold]
      intro n h
      cases n <;> simp_all [Tree.unfold_aux]
      case succ n' =>
        replace ⟨v', hv', h⟩ := h
        cases v' <;> simp_all
        case node l x r =>
          replace ⟨ovl, hl, ovr, hr, h⟩ := h
          cases ovl <;> simp_all
          cases ovr <;> simp_all
    . intros h
      simp_all [Tree.unfold]
      intros
      exists 1
      simp [Tree.unfold_aux]
      exists .leaf
  | node l x r ihl ihr =>
    apply Iff.intro
    . simp_all [Tree.unfold]
      intro n h
      cases n <;> simp_all [Tree.unfold_aux]; case succ n =>
      replace ⟨v', hv', h⟩ := h
      cases v' <;> simp_all
      case node bl x br =>
        replace ⟨ovl, hvl, ovr, hvr, h⟩ := h
        cases ovl <;> simp_all
        case some vl =>
          cases ovr <;> simp_all
          case some vr =>
            exists bl, br
            apply And.intro hv'
            rw [← @ihl bl, ← @ihr br]
            apply And.intro <;> exists n
    . intro ⟨bl, br, hx, hl, hr⟩
      rw [← @ihl bl] at hl
      simp [Tree.unfold] at hl
      replace ⟨hml, nl, hl⟩ := hl
      rw [← @ihr br] at hr
      simp [Tree.unfold] at hr
      replace ⟨hmr, nr, hr⟩ := hr
      simp [Tree.unfold]
      simp_all
      exists (nl + nr + 1)
      exists TreeF.node bl x br
      simp_all
      exists (some l)
      simp_all [Tree.unfold_aux_monotonic]
      exists (some r)
      rw [Nat.add_comm]
      simp_all [Tree.unfold_aux_monotonic]

theorem Tree.support_unfold_congr
    {hf : ∀ {b}, support (f b) = support (f' b)} :
    support (Tree.unfold f b) = support (Tree.unfold f' b) := by
  aesop

end Unfold

section FoldConversions

theorem Tree.fold_accu_Option_basic
    {α β : Type}
    {v : β}
    {t : Tree α}
    {z : β}
    {f : β → α → β → β} :
    Tree.fold f z t = v ↔
    Tree.accuM
      (fun _ _ => ((), ()))
      (fun l x r _ => some (f l x r))
      (fun _ => some z)
      t
      () = some v := by
    induction t generalizing v <;> simp_all [Tree.fold, Tree.accuM]
    case node l x r ihl ihr =>
        replace ihl := @ihl (Tree.fold f z l)
        replace ihr := @ihr (Tree.fold f z r)
        simp_all

theorem Tree.fold_accu_Option_true
    {α : Type}
    {t : Tree α}
    {g : α → Bool}
    {f : Bool → α → Bool → Bool}
    (h : ∀ accL x accR, f accL x accR = (g x && accL && accR)) :
    Tree.fold f true t = true ↔
    Tree.accuM
      (fun _ _ => ((), ()))
      (fun _ x _ _ => guard (g x))
      (fun _ => some ())
      t
      () = some () := by
    induction t <;> simp_all [Tree.fold, Tree.accuM]
    case node l x r ihl ihr =>
        apply Iff.intro <;> intro hf
        . -- (->)
          generalize hvl : fold f true l = vl
          generalize hvr : fold f true r = vr
          cases vl <;> cases vr <;>
            simp_all [guard]
        . -- (<-)
          rw [Option.bind_eq_some_iff] at hf
          replace ⟨ vl, hf ⟩ := hf
          rw [Option.bind_eq_some_iff] at hf
          replace ⟨ h1, ⟨ v, h2 ⟩ ⟩ := hf
          simp_all [guard]

theorem Tree.fold_accu_Option_function
    {α β σ : Type}
    {i : σ}
    {v : β}
    {t : Tree α}
    {z : (σ → β)}
    {f : (σ → β) → α → (σ → β) → (σ → β)}
    {g : β → α → β → σ → Option β}
    {stl str :  α → σ → σ}
    (h : ∀ accL x accR s w,
      f accL x accR s = w ↔ (do g (← accL (stl x s)) x (← accR (str x s)) s) = some w)
    :
    Tree.fold f z t i = v ↔
    Tree.accuM
      (fun x s => (stl x s, str x s))
      g
      (fun s => some (z s))
      t
      i = some v := by
    induction t generalizing v i <;> simp_all [Tree.fold, Tree.accuM, Option.bind_eq_some_iff]
    case node l x r ihl ihr =>
      apply Iff.intro <;> intro hg
      . -- (->)
        exists (Tree.fold f z l (stl x i))
        rw [← ihl]
        simp_all
        exists (Tree.fold f z r (str x i))
        rw [← ihr]
        simp_all
      . -- (<-)
        replace ⟨ vl, hl, vR, hr, hg ⟩ := hg
        rw [← ihl] at hl
        rw [← ihr] at hr
        rw [hl, hr]
        apply hg

theorem Tree.fold_accu_Option_function_true
    {α σ : Type}
    {i : σ}
    {t : Tree α}
    {z : σ → Bool}
    {f : (σ → Bool) → α → (σ → Bool) → (σ → Bool)}
    {g : α → σ → Bool}
    {stL stR :  α → σ → σ}
    (h : ∀ accL x accR s,
      f accL x accR s = true ↔ (do (return (g x s) && (← accL (stL x s)) && (← accR (stR x s)))) = some true)
    :
    Tree.fold f z t i = true ↔
    Tree.accuM
      (fun x s => (stL x s, stR x s))
      (fun _ x _ s => guard $ g x s)
      (fun s => guard (z s))
      t
      i = some () := by
    induction t generalizing i <;> simp_all [Tree.fold, Tree.accuM, Option.bind_eq_some_iff, guard]
    case node l x r ihl ihr =>
      apply Iff.intro <;> intro hg <;> simp_all
      replace ⟨⟨ vl, hl ⟩, ⟨ vr, hr ⟩ , hg⟩ := hg; simp_all

theorem Tree.fold_accu_cond
  {α σ : Type}
  {i : σ}
  {stTrue stFalse : α -> σ -> σ}
  {condTrue condFalse initCond : σ -> Bool}
  {t : Tree α}
  {condGuard : α -> σ -> Bool} :
  Tree.fold
    (fun accL x accR s => if condGuard x s then
                      condTrue s && accL (stTrue x s) && accR (stTrue x s) else
                      condFalse s && accL (stFalse x s) && accR (stFalse x s))
    (fun s => initCond s)
    t
    i = true ↔
  Tree.accuM
    (fun x s => if condGuard x s then (stTrue x s, stTrue x s) else (stFalse x s, stFalse x s))
    (fun _ x _ s =>
      if condGuard x s then guard $ condTrue s else guard $ condFalse s)
    (fun s => guard $ initCond s)
    t
    i = some () := by
    induction t generalizing i <;> simp_all [Tree.fold, Tree.accuM, Option.bind_eq_some_iff, guard]
    case node l v r ihl ihr =>
      cases (condGuard v i) <;> aesop

end FoldConversions

section FoldCoercion

theorem Tree.coerce_to_fold
    {t : Tree α}
    {f : Tree α → β} -- function to be coerced
    {z : β}
    {g : β → α → β → β}
    (h1 : f .leaf = z := by aesop)
    (h2 : ∀ l x r, f (.node l x r) = g (f l) x (f r)
      := by intros; simp_all; rfl) :
    f t = t.fold g z := by
  induction t <;> simp_all

end FoldCoercion

section FoldMerging

theorem Tree.merge_accuM
    {t : Tree α}
    {st₁ : α → σ₁ → σ₁ × σ₁}
    {st₂ : α → σ₂ → σ₂ × σ₂}
    {f₁ : β₁ → α → β₁ → σ₁ → Option β₁}
    {f₂ : β₂ → α → β₂ → σ₂ → Option β₂}
    {s₁ : σ₁} {s₂ : σ₂}
    {z₁ : σ₁ → Option β₁} {z₂ : σ₂ → Option β₂}
    {b₁ : β₁} {b₂ : β₂}
    :
    (t.accuM st₁ f₁ z₁ s₁ = some b₁ ∧ t.accuM st₂ f₂ z₂ s₂ = some b₂)
    ↔
    (t.accuM
      (fun x (s₁, s₂) => (((st₁ x s₁).1, (st₂ x s₂).1), ((st₁ x s₁).2, (st₂ x s₂).2)))
      (fun (bl₁, bl₂) x (br₁, br₂) (s₁, s₂) => do (← f₁ bl₁ x br₁ s₁, ← f₂ bl₂ x br₂ s₂))
      (fun (s₁, s₂) => do (← z₁ s₁, ← z₂ s₂))
      (s₁, s₂) = some (b₁, b₂)) := by
  induction t generalizing st₁ st₂ f₁ f₂ s₁ s₂ z₁ z₂ b₁ b₂
  case leaf =>
    simp [accuM]
    apply Iff.intro <;> intro H
    . -- (->)
      rw [H.left, H.right]
      simp
    . -- (<-)
      generalize Hx1 : (z₁ s₁) = x1
      generalize Hx2 : (z₂ s₂) = x2
      cases x1 <;> cases x2 <;> simp_all
  case node l x r IHl IHr =>
    apply Iff.intro
    . -- (->)
      intro ⟨ H1, H2 ⟩
      unfold accuM at H1 H2 ⊢
      simp at H1 H2 ⊢
      rw [Option.bind_eq_some_iff] at H1 H2
      replace ⟨ lv₁, ⟨ Hlv₁, H1 ⟩  ⟩ := @H1
      replace ⟨ lv₂, ⟨ Hlv₂, H2 ⟩  ⟩ := @H2
      rw [Option.bind_eq_some_iff] at H1 H2
      replace ⟨ rv₁, ⟨ Hrv₁, H1 ⟩  ⟩ := @H1
      replace ⟨ rv₂, ⟨ Hrv₂, H2 ⟩  ⟩ := @H2
      replace IHl := @IHl st₁ st₂ f₁ f₂ (st₁ x s₁).fst (st₂ x s₂).fst z₁ z₂ lv₁ lv₂
      replace IHr := @IHr st₁ st₂ f₁ f₂ (st₁ x s₁).snd (st₂ x s₂).snd z₁ z₂ rv₁ rv₂
      simp_all
    . -- (<-)
      intro H
      unfold accuM at H ⊢
      simp at H ⊢
      rw [Option.bind_eq_some_iff] at H
      replace ⟨ ⟨ lv₁, lv₂ ⟩ , ⟨ Hlv, H ⟩  ⟩ := @H
      rw [Option.bind_eq_some_iff] at H
      replace ⟨ ⟨ rv₁, rv₂ ⟩ , ⟨ Hrv, H ⟩ ⟩ := @H
      rw [Option.bind_eq_some_iff] at H
      replace ⟨ v₁, ⟨ Hv₁ , H ⟩ ⟩ := @H
      rw [Option.bind_eq_some_iff] at H
      replace ⟨ v₂, ⟨ Hv₂ , H ⟩ ⟩ := @H
      replace IHl := @IHl st₁ st₂ f₁ f₂ (st₁ x s₁).fst (st₂ x s₂).fst z₁ z₂ lv₁ lv₂
      replace IHr := @IHr st₁ st₂ f₁ f₂ (st₁ x s₁).snd (st₂ x s₂).snd z₁ z₂ rv₁ rv₂
      simp_all

end FoldMerging

namespace Gen

namespace CorrectGen

@[reducible]
def Tree.s_unfold
    {α β σ : Type}
    {st : α → σ → σ × σ}
    {f : β → α → β → σ → Option β}
    {z : σ → Option β}
    {s : σ}
    {b : β}
    (g : (b : β) → (s : σ) → CorrectGen
      (fun (t : TreeF α β) =>
        (z s = some b ∧ t = .leaf) ∨
        (∃ a bl br, f bl a br s = some b ∧ t = .node bl a br))) :
    CorrectGen (fun v => Tree.accuM st f z v s = some b) :=
  Subtype.mk
    (Tree.unfold (fun (b, s) => do
      match (← (g b s).val) with
      | .leaf => pure .leaf
      | .node bl x br => pure (.node (bl, (st x s).1) x (br, (st x s).2))) (b, s)) <| by
    rw [Tree.support_unfold]
    funext t
    induction t generalizing b s <;> simp_all
    case leaf =>
      apply Iff.intro <;> intro h
      . replace ⟨ t', ⟨ ht', h ⟩ ⟩ := h
        cases t' <;> simp_all [(g b s).property]
      . exists TreeF.leaf
        simp_all [(g b s).property]
    case node l x r ihl ihr =>
      apply Iff.intro <;> intro h
      . replace ⟨ bl, sl, br, sr, ⟨ ⟨ t', ⟨ ht' , h ⟩  ⟩, ⟨ hl, hr ⟩ ⟩ ⟩ := h
        cases t' <;> simp_all [(g b s).property]
        case mp.node bl' x' br' =>
          replace ⟨ x'', l'', r'', ht', hx, hr, hl ⟩ := ht'
          simp_all
      . rw [Option.bind_eq_some_iff] at h
        replace ⟨ bl, ⟨ hl, h ⟩ ⟩ := h
        rw [Option.bind_eq_some_iff] at h
        replace ⟨ br, ⟨ hr, h ⟩ ⟩ := h
        exists bl, (st x s).fst, br, (st x s).snd
        apply And.intro
        . exists TreeF.node bl x br
          simp_all [(g b s).property]
          exists x, bl, br
        . simp_all

end CorrectGen

namespace Total

@[simp, aesop safe (rule_sets := [totality])]
def Tree.total_unfold
    (h : ∀ b, total (g b)) :
    total (Tree.unfold g b) := by
  simp [Tree.unfold]
  apply total_indexed
  intro n
  induction n generalizing b with
  | zero => simp [Tree.unfold_aux]
  | succ n' ih =>
    simp [Tree.unfold_aux]
    apply total_bind <;> try apply h
    intro t h
    cases t <;> simp [ih]

end Total

end Gen

namespace PrettyPrint

def Tree.toString [ToString α] : Tree α → String
  | .leaf => "(leaf)"
  | .node l x r => s!"(node {Tree.toString l} {x} {Tree.toString r})"

instance [ToString α] : ToString (Tree α) where
  toString := Tree.toString

end PrettyPrint
