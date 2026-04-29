/-
  CedarMicro.Soundness: soundness theorem for the hand-authored
  type-directed generator `genWellTyped`.

  The paper's §5.1 headline claim:

    ∀ Γ τ e, e ∈ support (genWellTyped Γ τ) → wellTypedAt Γ τ e = true

  Proof outline:

    Step 1. `varsOfType_sound`: if `n ∈ varsOfType Γ τ`, then
            `Γ[n]? = some τ`.
    Step 2. `genLeaf_sound`: every `e` in `support (genLeaf Γ τ)`
            satisfies `wellTypedAt Γ τ e`. Uses Step 1 + the
            Palamedes support lemmas for `pick` and `pure`.
    Step 3. `genSize_sound`: induction on fuel. At fuel 0 reduces
            to Step 2. At fuel n+1, case-split on τ; each arm is
            a `pick` of `genLeaf` with a `bind` over recursive
            calls; the recursive hypothesis plus the typing
            rules of `ite` and `and` discharge the recursive
            arms.
    Step 4. `genWellTyped_sound`: Step 3 specialised to fuel = 2.
-/

import Pythia.LanguageSemantics.Cedar.WellTyped
import Mathlib.Tactic.SplitIfs

namespace Pythia.LanguageSemantics.Cedar

open Gen

@[simp] theorem guard_true_bind {f : Unit → Option α} :
    (guard True : Option Unit).bind f = f () := by simp [guard]

@[simp] theorem guard_false_bind {f : Unit → Option α} :
    (guard False : Option Unit).bind f = none := by simp [guard]

-- ────────────────────────────────────────────────────────────────────
-- Step 1: varsOfType lookup soundness.
-- ────────────────────────────────────────────────────────────────────

theorem varsOfType_sound (Γ : List Ty) (τ : Ty) (n : Nat) :
    n ∈ varsOfType Γ τ → Γ[n]? = some τ := by
  induction Γ generalizing n with
  | nil => intro h; simp [varsOfType] at h
  | cons τ' rest ih =>
    intro h
    unfold varsOfType at h
    simp only at h
    split_ifs at h with hτ
    · simp only [List.mem_cons, List.mem_map] at h
      rcases h with h0 | ⟨m, hm, hn⟩
      · subst h0; subst hτ; rfl
      · subst hn
        simp [List.getElem?_cons_succ]
        exact ih m hm
    · simp only [List.mem_map] at h
      obtain ⟨m, hm, hn⟩ := h
      subst hn
      simp [List.getElem?_cons_succ]
      exact ih m hm

-- ────────────────────────────────────────────────────────────────────
-- Step 2: `genLeaf` produces only well-typed expressions.
-- ────────────────────────────────────────────────────────────────────

/-- Helper: the support of a `foldr (pick (pure .var i)) fallback` is
    the union of the var-indexed singletons with the fallback's support. -/
private theorem support_varGen_foldr (xs : List Nat) (g : Gen Expr) (e : Expr) :
    _root_.Gen.support (xs.foldr (fun i acc => Gen.pick (pure (Expr.var i)) acc) g) e ↔
      (∃ i ∈ xs, e = Expr.var i) ∨ _root_.Gen.support g e := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    simp only [List.foldr_cons, Gen.Support.support_pick,
               Gen.Support.support_pure, ih, List.mem_cons]
    constructor
    · rintro (rfl | ⟨j, hj, hje⟩ | hg)
      · exact Or.inl ⟨i, Or.inl rfl, rfl⟩
      · exact Or.inl ⟨j, Or.inr hj, hje⟩
      · exact Or.inr hg
    · rintro (⟨j, hj, hje⟩ | hg)
      · rcases hj with rfl | hj
        · exact Or.inl hje
        · exact Or.inr (Or.inl ⟨j, hj, hje⟩)
      · exact Or.inr (Or.inr hg)

/-- Helper (bool case): every element of `litGen .bool` is a bool literal. -/
private theorem litGen_bool_sound (Γ : List Ty) (e : Expr)
    (h : _root_.Gen.support (litGen .bool) e) : wellTypedAt Γ .bool e = true := by
  simp only [litGen, Gen.Support.support_pick, Gen.Support.support_pure] at h
  rcases h with rfl | rfl <;> rfl

/-- Helper (int case): every element of `litGen .int` is an int literal. -/
private theorem litGen_int_sound (Γ : List Ty) (e : Expr)
    (h : _root_.Gen.support (litGen .int) e) : wellTypedAt Γ .int e = true := by
  simp only [litGen, Gen.Support.support_pick, Gen.Support.support_pure] at h
  rcases h with rfl | rfl | rfl <;> rfl

/-- Every element of `litGen τ` type-checks at τ (both type cases). -/
private theorem litGen_sound (Γ : List Ty) (τ : Ty) (e : Expr)
    (h : _root_.Gen.support (litGen τ) e) : wellTypedAt Γ τ e = true := by
  cases τ
  · exact litGen_bool_sound Γ e h
  · exact litGen_int_sound Γ e h

theorem genLeaf_sound (Γ : List Ty) (τ : Ty) (e : Expr) :
    _root_.Gen.support (genLeaf Γ τ) e → wellTypedAt Γ τ e = true := by
  intro h
  unfold genLeaf at h
  split at h
  case _ hvars =>
    exact litGen_sound Γ τ e h
  case _ n rest hvars =>
    simp only [Gen.Support.support_pick, support_varGen_foldr] at h
    rcases h with (⟨i, hi, rfl⟩ | hlit) | hlit
    · have hmem : i ∈ varsOfType Γ τ := by rw [hvars]; exact hi
      have hty := varsOfType_sound Γ τ i hmem
      simp [wellTypedAt, hty]
    · exact litGen_sound Γ τ e hlit
    · exact litGen_sound Γ τ e hlit

-- ────────────────────────────────────────────────────────────────────
-- Step 3: `genSize` soundness by induction on fuel.
-- ────────────────────────────────────────────────────────────────────

/-- Helper: if every component of an `.ite` type-checks at the
    expected position, the whole `.ite` type-checks at the result
    type. Used to discharge the `.ite` arm of `genSize_sound`. -/
private theorem wellTypedAt_ite (Γ : List Ty) (τ : Ty) (c t f : Expr)
    (hc : wellTypedAt Γ .bool c = true)
    (ht : wellTypedAt Γ τ t = true)
    (hf : wellTypedAt Γ τ f = true) :
    wellTypedAt Γ τ (.ite c t f) = true := by
  simp only [wellTypedAt] at hc ht hf ⊢
  cases hgc : getType c Γ with
  | none => simp [hgc] at hc
  | some τc =>
    cases hgt : getType t Γ with
    | none => simp [hgt] at ht
    | some τt =>
      cases hgf : getType f Γ with
      | none => simp [hgf] at hf
      | some τf =>
        simp [hgc, hgt, hgf] at hc ht hf
        cases hc  -- τc = .bool
        cases ht  -- τt = τ
        cases hf  -- τf = τ
        simp [getType, hgc, hgt, hgf]

/-- Helper: both components of an `.and` at `.bool` yield a well-typed
    `.and` at `.bool`. -/
private theorem wellTypedAt_and (Γ : List Ty) (a b : Expr)
    (ha : wellTypedAt Γ .bool a = true)
    (hb : wellTypedAt Γ .bool b = true) :
    wellTypedAt Γ .bool (.and a b) = true := by
  simp only [wellTypedAt] at ha hb ⊢
  cases hga : getType a Γ with
  | none => simp [hga] at ha
  | some τa =>
    cases hgb : getType b Γ with
    | none => simp [hgb] at hb
    | some τb =>
      simp [hga, hgb] at ha hb
      cases ha
      cases hb
      simp [getType, hga, hgb]

theorem genSize_sound :
    ∀ (Γ : List Ty) (n : Nat) (τ : Ty) (e : Expr),
      _root_.Gen.support (genSize Γ n τ) e → wellTypedAt Γ τ e = true := by
  intro Γ n
  induction n with
  | zero =>
    intro τ e hmem
    simp [genSize] at hmem
    exact genLeaf_sound Γ τ e hmem
  | succ n _ih =>
    -- The succ arms only recurse at fuel 0 (genSize Γ 0 _ = genLeaf Γ _),
    -- so the ih is not needed. Each arm is a `pick` of `genLeaf` with a
    -- bind-chain producing a compound form. Dispatch via genLeaf_sound +
    -- the wellTypedAt_ite / wellTypedAt_and helpers.
    intro τ e hmem
    cases τ with
    | int =>
      simp only [genSize, Gen.Support.support_pick, Gen.Support.support_bind,
                 Gen.Support.support_pure] at hmem
      rcases hmem with hleaf | ⟨c, hc, t, ht, f, hf, rfl⟩
      · exact genLeaf_sound Γ .int e hleaf
      · have hc' := genLeaf_sound Γ .bool c (by simpa [genSize] using hc)
        have ht' := genLeaf_sound Γ .int t (by simpa [genSize] using ht)
        have hf' := genLeaf_sound Γ .int f (by simpa [genSize] using hf)
        exact wellTypedAt_ite Γ .int c t f hc' ht' hf'
    | bool =>
      simp only [genSize, Gen.Support.support_pick, Gen.Support.support_bind,
                 Gen.Support.support_pure] at hmem
      rcases hmem with hleaf | hand | hite
      · exact genLeaf_sound Γ .bool e hleaf
      · obtain ⟨a, ha, b, hb, rfl⟩ := hand
        have ha' := genLeaf_sound Γ .bool a (by simpa [genSize] using ha)
        have hb' := genLeaf_sound Γ .bool b (by simpa [genSize] using hb)
        exact wellTypedAt_and Γ a b ha' hb'
      · obtain ⟨c, hc, t, ht, f, hf, rfl⟩ := hite
        have hc' := genLeaf_sound Γ .bool c (by simpa [genSize] using hc)
        have ht' := genLeaf_sound Γ .bool t (by simpa [genSize] using ht)
        have hf' := genLeaf_sound Γ .bool f (by simpa [genSize] using hf)
        exact wellTypedAt_ite Γ .bool c t f hc' ht' hf'

-- ────────────────────────────────────────────────────────────────────
-- Step 4: the paper's main soundness theorem.
-- ────────────────────────────────────────────────────────────────────

/-- Every expression in the support of the hand-authored
    type-directed generator satisfies the Lean typechecker
    predicate at the requested target type. -/
theorem genWellTyped_sound (Γ : List Ty) (τ : Ty) (e : Expr) :
    _root_.Gen.support (genWellTyped Γ τ) e → wellTypedAt Γ τ e = true := by
  unfold genWellTyped
  exact genSize_sound Γ 2 τ e

end Pythia.LanguageSemantics.Cedar
