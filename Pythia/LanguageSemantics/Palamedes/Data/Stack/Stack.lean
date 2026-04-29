import Pythia.LanguageSemantics.Palamedes.Gen
import Pythia.LanguageSemantics.Palamedes.CorrectGen
import Pythia.LanguageSemantics.Palamedes.Total
import Pythia.LanguageSemantics.Palamedes.Data.Stack.Atom

section TypeDef
/- adapted from https://github.com/QuickChick/QuickChick/tree/master/examples/ifc-basic -/

inductive Stack where
  | mty
  | cons (a : Atom) (s : Stack)
  | ret_cons (pc : Atom) (s : Stack)

end TypeDef

section BaseFunctor

inductive StackF (α : Type) where
  | mty : StackF α
  | cons : (z : Atom) → (s : α) → StackF α
  | ret_cons : (pc : Atom) → (s : α) → StackF α

theorem StackF_or
  {α : Type}
  {P : Prop}
  {Q : Atom → α → Prop}
  {R : Atom → α → Prop}
  {s : StackF α} :
  StackF.rec P Q R s ↔
    (P ∧ s = .mty)
    ∨ (∃ z s', s = .cons z s' ∧ Q z s')
    ∨ (∃ pc s', s = .ret_cons pc s' ∧ R pc s') := by
  match s with
  | .mty => simp
  | .cons _ _ => aesop
  | .ret_cons _ _ => aesop

end BaseFunctor

section RecursionSchemes

def Stack.fold
  {α : Type}
  (z : α)
  (f_c : Atom → α → α)
  (f_rc : Atom → α → α)
  (s : Stack) : α :=
  match s with
  | .mty => z
  | .cons x s' => f_c x (Stack.fold z f_c f_rc s')
  | .ret_cons pc s' => f_rc pc (Stack.fold z f_c f_rc s')

@[simp] theorem Stack.fold_mty :
  Stack.fold z f_c f_rc .mty = z := rfl
@[simp] theorem Stack.fold_cons
  {x} {s : Stack} {z} {f_c : Atom → α → α} {f_rc : Atom → α → α} :
  Stack.fold z f_c f_rc (.cons x s) = f_c x (Stack.fold z f_c f_rc s) := rfl
@[simp] theorem Stack.fold_ret_cons
  {x} {s : Stack} {z} {f_c : Atom → α → α} {f_rc : Atom → α → α} :
    Stack.fold z f_c f_rc (.ret_cons x s) = f_rc x (Stack.fold z f_c f_rc s) := rfl

def Stack.accuM
  [Monad m]
  {α σ : Type}
  (st_c : Atom→ σ → σ)
  (st_rc : Atom → σ → σ)
  (z : σ → m α)
  (f_c : Atom → α → σ → m α)
  (f_rc : Atom → α → σ → m α)
  (s : Stack)
  (i : σ) : m α :=
  match s with
  | .mty => z i
  | .cons x s' => do
     f_c x (← Stack.accuM st_c st_rc z f_c f_rc s' (st_c x i)) i
  | .ret_cons pc s' => do
     f_rc pc (← Stack.accuM st_c st_rc z f_c f_rc s' (st_rc pc i)) i

@[simp] theorem Stack.accuM_nil [Monad m]
  {st_c : Atom → σ → σ} {st_rc : Atom → σ → σ} {z : σ → m α}
  {f_c : Atom → α → σ → m α} {f_rc : Atom → α → σ → m α} {i : σ} :
  Stack.accuM st_c st_rc z f_c f_rc .mty i = z i := rfl
@[simp] theorem Stack.accuM_cons  [Monad m]
  {st_c : Atom → σ → σ} {st_rc : Atom → σ → σ} {z : σ → m α}
  {f_c : Atom → α → σ → m α} {f_rc : Atom → α → σ → m α} {i : σ}
  {x} {s : Stack} :
  Stack.accuM st_c st_rc z f_c f_rc (.cons x s) i
    = (do f_c x (← Stack.accuM st_c st_rc z f_c f_rc s (st_c x i)) i) := rfl
@[simp] theorem Stack.accuM_ret_cons [Monad m]
  {st_c : Atom → σ → σ} {st_rc : Atom → σ → σ} {z : σ → m α}
  {f_c : Atom → α → σ → m α} {f_rc : Atom → α → σ → m α} {i : σ}
  {pc} {s : Stack} :
  Stack.accuM st_c st_rc z f_c f_rc (.ret_cons pc s) i
    = (do f_rc pc (← Stack.accuM st_c st_rc z f_c f_rc s (st_rc pc i)) i) := rfl

end RecursionSchemes

section Unfold

open Gen

private def Stack.unfold_aux (n : Nat) (f : α → Gen (StackF α)) (x : α)
  : Gen (Option Stack) :=
  match n with
  | 0 => pure none
  | n' + 1 => do
    match (← f x) with
    | .mty => pure (some .mty)
    | .cons x vs => do
      let s ← Stack.unfold_aux n' f vs
      pure (do pure (.cons x (← s)))
    | .ret_cons pc vs => do
      let s ← Stack.unfold_aux n' f vs
      pure (do pure (.ret_cons pc (← s)))

@[simp]
theorem Stack.unfold_aux_monotonic :
    some v ∈ 〚Stack.unfold_aux n f b〛 →
    some v ∈ 〚Stack.unfold_aux (n + m) f b〛 := by
  induction n generalizing v f b
  case zero =>
    simp [Stack.unfold_aux]
  case succ n' ih =>
    unfold Stack.unfold_aux
    simp [bind]
    intro h
    replace ⟨ s, hs, h ⟩ := h
    simp_all [Nat.add_comm]
    exists s
    apply And.intro hs
    cases s <;> simp_all
    all_goals
      replace ⟨ v', h ⟩ := h
      exists v'
      cases v' <;> simp_all

@[irreducible]
def Stack.unfold (f : α → Gen (StackF α)) (x : α) : Gen Stack :=
  .indexed (fun n => Stack.unfold_aux n f x)

@[simp]
def Stack.unfold_support (P : α → StackF α → Prop) (v : α) (s : Stack) : Prop :=
  match s with
  | .mty => P v .mty
  | .cons x s' => ∃ v', P v (.cons x v') ∧ Stack.unfold_support P v' s'
  | .ret_cons pc s' => ∃ v', P v (.ret_cons pc v') ∧ Stack.unfold_support P v' s'

@[simp]
theorem Stack.support_unfold :
    support (Stack.unfold f b) = Stack.unfold_support (fun b' => support (f b')) b := by
  funext s
  simp_all
  induction s generalizing b with
  | mty =>
    apply Iff.intro
    . intro h
      simp [unfold] at h
      replace ⟨hm, n, h⟩ := h
      cases n <;> simp_all [Stack.unfold_aux]
      case succ n' =>
        have ⟨v', hv'1, hv'2⟩ := h
        cases v' <;> simp_all
        all_goals
          have ⟨v'', hv''⟩ := hv'2
          cases v'' <;> simp_all
    . intros h
      simp_all [unfold]
      exists 1
      exists StackF.mty
  | cons x s' ih =>
    apply Iff.intro
    . intro h
      simp [unfold] at h
      replace ⟨hm, n, h⟩ := h
      cases n <;> simp_all [Stack.unfold_aux]
      case succ n =>
        have ⟨v', hv'1, hv'2⟩ := h; clear h
        cases v' <;> simp_all
        case cons _ b'' =>
          have ⟨v'', hv''⟩ := hv'2; clear hv'2
          cases v'' <;> simp_all
          obtain ⟨hv'', rfl, rfl⟩ := hv''
          exists b''
          apply And.intro hv'1
          apply (@ih b'').mp
          simp [unfold]
          simp_all
          exists n
        case ret_cons _ b'' =>
          have ⟨v'', hv''⟩ := hv'2
          cases v'' <;> simp_all
    . intro ⟨b', hx, hs⟩
      simp_all [unfold]
      have ⟨n, h⟩ := ih.mpr hs
      exists n + 1
      exists StackF.cons x b'
      simp_all
      exists (some s')
  | ret_cons pc s' ih =>
    apply Iff.intro
    . intro h
      simp [unfold] at h
      replace ⟨hm, n, h⟩ := h
      cases n <;> simp_all [Stack.unfold_aux]
      case succ n =>
        replace ⟨v', hv', h⟩ := h
        cases v' <;> simp_all
        case cons _ b'' =>
          have ⟨v'', hv''⟩ := h
          cases v'' <;> simp_all
        case ret_cons _ b'' =>
          have ⟨v'', hv''⟩ := h
          cases v'' <;> simp_all
          obtain ⟨hv'', rfl, rfl⟩ := hv''
          exists b''
          apply And.intro hv'
          apply (@ih b'').mp
          simp [unfold]
          simp_all
          exists n
    . intro ⟨b', hx, hs⟩
      simp_all [unfold]
      have ⟨n, h⟩ := ih.mpr hs
      exists (n + 1)
      exists (StackF.ret_cons pc b')
      simp_all
      exists (some s')

theorem Stack.support_unfold_congr
    {hf : ∀ {b}, support (f b) = support (f' b)} :
    support (Stack.unfold f b) = support (Stack.unfold f' b) := by
  aesop

end Unfold

section FoldConversions

theorem Stack.fold_accu_Option_basic
    {α : Type}
    {v : α}
    {s : Stack}
    {z : α}
    {f_c : Atom → α → α}
    {f_rc : Atom → α → α} :
    Stack.fold z f_c f_rc s = v ↔
    Stack.accuM
      (fun _ _ => ())
      (fun _ _ => ())
      (fun _ => some z)
      (fun x s' _ => some (f_c x s'))
      (fun pc s' _ => some (f_rc pc s'))
      s
      () = some v := by
    induction s generalizing v <;> simp_all [Stack.fold, Stack.accuM]
    case cons x s' ih =>
      replace ih := @ih (Stack.fold z f_c f_rc s')
      simp_all
    case ret_cons pc s' ih =>
      replace ih := @ih (Stack.fold z f_c f_rc s')
      simp_all

theorem Stack.fold_accu_Option_true
    {f_c : Atom → Bool → Bool}
    {f_rc : Atom → Bool → Bool}
    {g_c : Atom → Bool}
    {g_rc : Atom → Bool}
    (h_c : ∀ x acc, f_c x acc = (g_c x && acc))
    (h_rc : ∀ pc acc, f_rc pc acc = (g_rc pc && acc)) :
    Stack.fold true f_c f_rc s = true ↔
    Stack.accuM
      (fun _ _ => ())
      (fun _ _ => ())
      (fun _ => some ())
      (fun x _ _ => guard (g_c x))
      (fun x _ _ => guard (g_rc x))
      s
      () = some () := by
    induction s <;> simp_all [Stack.fold, Stack.accuM]
    case cons x s' ih =>
        apply Iff.intro <;> intro hf
        . -- (->)
          generalize hv : Stack.fold true f_c f_rc s' = v
          cases v <;>
            simp_all [guard]
        . -- (<-)
          rw [Option.bind_eq_some_iff] at hf
          replace ⟨ v, hf ⟩ := hf
          simp_all [guard]
    case ret_cons pc s' ih =>
        apply Iff.intro <;> intro hf
        . -- (->)
          generalize hv : Stack.fold true f_c f_rc s' = v
          cases v <;>
            simp_all [guard]
        . -- (<-)
          rw [Option.bind_eq_some_iff] at hf
          replace ⟨ v, hf ⟩ := hf
          simp_all [guard]

theorem Stack.fold_accu_Option_function
    {β σ : Type}
    {i : σ}
    {v : β}
    {s : Stack}
    {z : (σ → β)}
    {f_c : Atom → (σ → β) → (σ → β)}
    {f_rc : Atom → (σ → β) → (σ → β)}
    {g_c : Atom → β → σ → Option β}
    {g_rc : Atom → β → σ → Option β}
    {st_c : Atom → σ → σ}
    {st_rc : Atom → σ → σ}
    (h_c : ∀ x acc s w,
      f_c x acc s = w ↔ (do g_c x (← acc (st_c x s)) s) = some w)
    (h_rc : ∀ x acc s w,
      f_rc x acc s = w ↔ (do g_rc x (← acc (st_rc x s)) s) = some w)
    :
    Stack.fold z f_c f_rc s i = v ↔
    Stack.accuM
      st_c
      st_rc
      (fun s => some (z s))
      g_c
      g_rc
      s
      i = some v := by
    induction s generalizing v i <;> simp_all [Stack.fold, Stack.accuM, Option.bind_eq_some_iff]
    case cons x s' ih =>
      apply Iff.intro <;> intro hg
      . -- (->)
        exists (Stack.fold z f_c f_rc s' (st_c x i))
        simp_all
        rw [← ih]
      . -- (<-)
        replace ⟨w, ⟨hgw, hg⟩⟩ := hg
        rw [← ih] at hgw
        rw [hgw]
        apply hg
    case ret_cons pc s' ih =>
      apply Iff.intro <;> intro hg
      . -- (->)
        exists (Stack.fold z f_c f_rc s' (st_rc pc i))
        simp_all
        rw [← ih]
      . -- (<-)
        replace ⟨w, ⟨hgw, hg⟩⟩ := hg
        rw [← ih] at hgw
        rw [hgw]
        apply hg

theorem Stack.fold_accu_Option_function_true
    {σ : Type}
    {i : σ}
    {s : Stack}
    {z : σ → Bool}
    {f_c : Atom → (σ → Bool) → (σ → Bool)}
    {f_rc : Atom → (σ → Bool) → (σ → Bool)}
    {g_c : Atom → σ → Bool}
    {g_rc : Atom → σ → Bool}
    {st_c : Atom → σ → σ}
    {st_rc : Atom → σ → σ}
    (h_c : ∀ x acc s', f_c x acc s' = true ↔
      (do (return (g_c x s') && (← acc (st_c x s')))) = some true)
    (h_rc : ∀ x acc s', f_rc x acc s' = true ↔
      (do (return (g_rc x s') && (← acc (st_rc x s')))) = some true)
    :
    Stack.fold z f_c f_rc s i = true ↔
    Stack.accuM
      st_c
      st_rc
      (fun s => guard (z s))
      (fun x _ s => guard $ g_c x s)
      (fun x _ s => guard $ g_rc x s)
      s
      i = some () := by
    induction s generalizing i <;> simp_all [Stack.fold, Stack.accuM, Option.bind_eq_some_iff, guard]
    all_goals
      (apply Iff.intro <;> intro hg <;> simp_all
       replace ⟨ ⟨ v, hv ⟩ , hg⟩ := hg
       simp_all)


end FoldConversions

section FoldCoercion

theorem Stack.coerce_to_fold
    {s : Stack}
    {f : Stack → α} -- function to be coerced
    {z : α}
    {g_c : Atom → α → α}
    {g_rc : Atom → α → α}
    (hm : f .mty = z)
    (h_c : ∀ x s', f (.cons x s') = g_c x (f s'))
    (h_rc : ∀ pc s', f (.ret_cons pc s') = g_rc pc (f s')) :
    f s = Stack.fold z g_c g_rc s := by
  induction s <;> simp_all

end FoldCoercion

section FoldMerging

theorem Stack.merge_accuM
    {s : Stack}
    {st_c₁ : Atom → σ₁ → σ₁}
    {st_c₂ : Atom → σ₂ → σ₂}
    {st_rc₁ : Atom → σ₁ → σ₁}
    {st_rc₂ : Atom → σ₂ → σ₂}
    {f_c₁ : Atom → α₁ → σ₁ → Option α₁}
    {f_c₂ : Atom → α₂ → σ₂ → Option α₂}
    {f_rc₁ : Atom → α₁ → σ₁ → Option α₁}
    {f_rc₂ : Atom → α₂ → σ₂ → Option α₂}
    {s₁ : σ₁} {s₂ : σ₂}
    {z₁ : σ₁ → Option α₁} {z₂ : σ₂ → Option α₂}
    {v₁ : α₁} {v₂ : α₂}
    :
    (s.accuM st_c₁ st_rc₁ z₁ f_c₁ f_rc₁ s₁ = some v₁
      ∧ s.accuM st_c₂ st_rc₂ z₂ f_c₂ f_rc₂ s₂ = some v₂)
    ↔
    (s.accuM
      (fun x (s₁, s₂) => (st_c₁ x s₁, st_c₂ x s₂))
      (fun pc (s₁, s₂) => (st_rc₁ pc s₁, st_rc₂ pc s₂))
      (fun (s₁, s₂) => do (← z₁ s₁, ← z₂ s₂))
      (fun x (v₁, v₂) (s₁, s₂) => do (← f_c₁ x v₁ s₁, ← f_c₂ x v₂ s₂))
      (fun pc (v₁, v₂) (s₁, s₂) => do (← f_rc₁ pc v₁ s₁, ← f_rc₂ pc v₂ s₂))
      (s₁, s₂) = some (v₁, v₂)) := by
    induction s generalizing s₁ s₂ v₁ v₂
    case mty => simp_all [Stack.accuM, Option.bind_eq_some_iff]
    case cons y s' ih =>
      simp_all [Stack.accuM, Option.bind_eq_some_iff]
      apply Iff.intro
      . -- (->)
        intro ⟨ ⟨ v₁', ⟨ hv1h, hv1tl ⟩ ⟩ , ⟨ v₂', ⟨ hv2h, hv2tl ⟩ ⟩ ⟩
        exists v₁', v₂'
        replace ih := @ih (st_c₁ y s₁) (st_c₂ y s₂) v₁' v₂'
        simp_all
      . -- (<-)
        intro ⟨ v₁', v₂', h, h1, h2 ⟩
        replace ih := @ih (st_c₁ y s₁) (st_c₂ y s₂) v₁' v₂'
        apply And.intro
        . exists v₁'
          simp_all
        . exists v₂'
          simp_all
    case ret_cons pc s' ih =>
      simp_all [Stack.accuM, Option.bind_eq_some_iff]
      apply Iff.intro
      . -- (->)
        intro ⟨ ⟨ v₁', ⟨ hv1h, hv1tl ⟩ ⟩ , ⟨ v₂', ⟨ hv2h, hv2tl ⟩ ⟩ ⟩
        exists v₁', v₂'
        replace ih := @ih (st_rc₁ pc s₁) (st_rc₂ pc s₂) v₁' v₂'
        simp_all
      . -- (<-)
        intro ⟨ v₁', v₂', h, h1, h2 ⟩
        replace ih := @ih (st_rc₁ pc s₁) (st_rc₂ pc s₂) v₁' v₂'
        apply And.intro
        . exists v₁'
          simp_all
        . exists v₂'
          simp_all

end FoldMerging

namespace Gen

namespace CorrectGen

@[reducible]
def Stack.s_unfold
    {α σ : Type}
    {st_c : Atom → σ → σ}
    {st_rc : Atom → σ → σ}
    {z : σ → Option α}
    {f_c : Atom → α → σ → Option α}
    {f_rc : Atom → α → σ → Option α}
    {s : σ}
    {b : α}
    (g : (b : α) → (s : σ) → CorrectGen
      (fun (x : StackF α) =>
        (z s = some b ∧ x = .mty) ∨
        (∃ a b', f_c a b' s = some b ∧ x = .cons a b') ∨
        (∃ pc b', f_rc pc b' s = some b ∧ x = .ret_cons pc b'))) :
    CorrectGen (fun v => Stack.accuM st_c st_rc z f_c f_rc v s = some b) :=
  Subtype.mk
    (Stack.unfold (fun (b, s) => do
      match (← (g b s).val) with
      | .mty => pure .mty
      | .cons a b' => pure (.cons a (b', (st_c a s)))
      | .ret_cons pc b' => pure (.ret_cons pc (b', (st_rc pc s)))) (b, s)) <| by
    rw [Stack.support_unfold]
    funext x
    induction x generalizing b s <;> simp_all
    case mty =>
      apply Iff.intro <;> intro h
      . replace ⟨ x, ⟨ hs, h ⟩ ⟩ := h
        cases x <;> simp_all [(g b s).property]
      . exists StackF.mty
        simp_all [(g b s).property]
    case cons a x' ih =>
      apply Iff.intro <;> intro h
      . replace ⟨ b', s', ⟨ ⟨ x'', ⟨ hx'', h ⟩ ⟩ , hx'⟩ ⟩ := h
        cases x'' <;> simp_all [(g b s).property]
      . rw [Option.bind_eq_some_iff] at h
        replace ⟨ b', hb', h ⟩ := h
        exists b', st_c a s
        apply And.intro
        . exists StackF.cons a b'
          simp_all [(g b s).property]
        . simp_all
    case ret_cons pc s' ih =>
      apply Iff.intro <;> intro h
      . replace ⟨ b', s', ⟨ ⟨ x'', ⟨ hx'', h ⟩ ⟩ , hx'⟩ ⟩ := h
        cases x'' <;> simp_all [(g b s).property]
      . rw [Option.bind_eq_some_iff] at h
        replace ⟨ b', hb', h ⟩ := h
        exists b', st_rc pc s
        apply And.intro
        . exists StackF.ret_cons pc b'
          simp_all [(g b s).property]
        . simp_all

end CorrectGen

namespace Total

@[simp, aesop safe (rule_sets := [totality])]
def Stack.total_unfold
    (h : ∀ b, total (g b)) :
    total (Stack.unfold g b) := by
  simp [Stack.unfold]
  apply total_indexed
  intro n
  induction n generalizing b with
  | zero => simp [Stack.unfold_aux]
  | succ n' ih =>
    simp [Stack.unfold_aux]
    apply total_bind <;> try apply h
    intro x h
    cases x <;> simp [ih]

end Total

end Gen

namespace PrettyPrint

def Stack.toString : Stack → String
  | .mty => "(empty)"
  | .cons a s  => s!"(cons {Atom.toString a} {Stack.toString s})"
  | .ret_cons pc s => s!"(ret_cons {Atom.toString pc} {Stack.toString s})"

instance : ToString Stack where
  toString := Stack.toString

end PrettyPrint
