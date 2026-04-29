/-
  CedarMicro.Coverage: coverage-completeness theorems for the
  hand-authored type-directed generator `genWellTyped`.

  Companion to CedarMicro.Soundness. The pair gives the strongest
  available statement about the generator's image:

    Soundness:    e ∈ support (genWellTyped Γ τ) → wellTypedAt Γ τ e
    Completeness: e ∈ palette ∧ depth e ≤ k → wellTypedAt Γ τ e →
                  e ∈ support (genSize Γ (k+1) τ)

  The completeness side is conditioned on a `palette` predicate:
  `litGen .int` only emits {0, 1, -1}, so coverage cannot extend to
  arbitrary `Int` literals. The palette captures exactly the
  literals the generator can emit.

  The depth bound is necessary because `genSize` recurses at fuel
  zero only (a property of the V1 generator); deeper expressions
  are reachable only by widening the recursion arm. The k=1 case is
  what the V1 sampler produces in practice.
-/

import Pythia.LanguageSemantics.Cedar.WellTyped
import Pythia.LanguageSemantics.Cedar.Soundness
import Mathlib.Tactic.SplitIfs

namespace Pythia.LanguageSemantics.Cedar

open Gen

-- ────────────────────────────────────────────────────────────────────
-- The literal palette: exactly the literals `litGen` can emit.
-- ────────────────────────────────────────────────────────────────────

/-- The literal palette of `litGen`: every Bool, and {0, 1, -1} on Int.
    Lifted point-wise to expressions: every literal occurring in `e`
    must be in the palette. -/
def Expr.inPalette : Expr → Prop
  | .litInt n  => n = 0 ∨ n = 1 ∨ n = -1
  | .litBool _ => True
  | .var _     => True
  | .ite c t f => Expr.inPalette c ∧ Expr.inPalette t ∧ Expr.inPalette f
  | .and a b   => Expr.inPalette a ∧ Expr.inPalette b

/-- Structural depth of an expression. Leaves have depth 0; compound
    forms add 1. Used to state coverage at a given fuel bound. -/
def Expr.depth : Expr → Nat
  | .litInt _  => 0
  | .litBool _ => 0
  | .var _     => 0
  | .ite c t f => 1 + max (Expr.depth c) (max (Expr.depth t) (Expr.depth f))
  | .and a b   => 1 + max (Expr.depth a) (Expr.depth b)

-- ────────────────────────────────────────────────────────────────────
-- Step 1: varsOfType lookup completeness (dual to varsOfType_sound).
-- ────────────────────────────────────────────────────────────────────

theorem varsOfType_complete (Γ : List Ty) (τ : Ty) (n : Nat) :
    Γ[n]? = some τ → n ∈ varsOfType Γ τ := by
  induction Γ generalizing n with
  | nil =>
    intro h
    cases n <;> simp at h
  | cons τ' rest ih =>
    intro h
    cases n with
    | zero =>
      -- Γ[0]? = some τ' = some τ ⇒ τ' = τ
      simp at h
      subst h
      unfold varsOfType
      simp
    | succ m =>
      simp [List.getElem?_cons_succ] at h
      have hm : m ∈ varsOfType rest τ := ih m h
      unfold varsOfType
      split_ifs with hτ
      · simp only [List.mem_cons, List.mem_map]
        refine Or.inr ⟨m, hm, rfl⟩
      · simp only [List.mem_map]
        exact ⟨m, hm, rfl⟩

-- ────────────────────────────────────────────────────────────────────
-- Step 2: litGen completeness on the palette.
-- ────────────────────────────────────────────────────────────────────

/-- Every bool literal lies in the support of `litGen .bool`. -/
theorem litGen_bool_complete (b : Bool) :
    _root_.Gen.support (litGen .bool) (.litBool b) := by
  simp only [litGen, Gen.Support.support_pick, Gen.Support.support_pure]
  cases b
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- Every palette int literal lies in the support of `litGen .int`. -/
theorem litGen_int_complete (n : Int)
    (hp : n = 0 ∨ n = 1 ∨ n = -1) :
    _root_.Gen.support (litGen .int) (.litInt n) := by
  simp only [litGen, Gen.Support.support_pick, Gen.Support.support_pure]
  rcases hp with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

-- ────────────────────────────────────────────────────────────────────
-- Step 3: genLeaf completeness for leaves on the palette.
-- ────────────────────────────────────────────────────────────────────

/-- Helper: from membership in the foldr-of-pick of var generators, the
    `.var i` literal is in the support. -/
private theorem support_varGen_foldr_var
    (xs : List Nat) (g : Gen Expr) (i : Nat) (hi : i ∈ xs) :
    _root_.Gen.support
      (xs.foldr (fun j acc => Gen.pick (pure (Expr.var j)) acc) g)
      (Expr.var i) := by
  induction xs with
  | nil => cases hi
  | cons j xs ih =>
    simp only [List.foldr_cons, Gen.Support.support_pick,
               Gen.Support.support_pure]
    rcases List.mem_cons.mp hi with hij | hi'
    · exact Or.inl (by rw [hij])
    · exact Or.inr (ih hi')

/-- Coverage of `genLeaf` at every well-typed leaf in the palette. -/
theorem genLeaf_complete (Γ : List Ty) (τ : Ty) (e : Expr)
    (hpal : Expr.inPalette e)
    (hleaf : e.depth = 0)
    (htyp : wellTypedAt Γ τ e = true) :
    _root_.Gen.support (genLeaf Γ τ) e := by
  -- Three leaf cases (literal-int, literal-bool, var); compound forms
  -- have depth ≥ 1 and so are excluded by `hleaf`.
  cases e with
  | litInt n =>
    -- e = .litInt n must be in palette, well-typed at τ ⇒ τ = .int.
    have hpal' : n = 0 ∨ n = 1 ∨ n = -1 := hpal
    simp only [wellTypedAt, getType] at htyp
    -- htyp : (Ty.int == τ) = true
    have hτ : τ = .int := by
      cases τ
      · simp at htyp
      · rfl
    subst hτ
    unfold genLeaf
    split
    case _ _ => exact litGen_int_complete n hpal'
    case _ _ _ _ =>
      simp only [Gen.Support.support_pick]
      exact Or.inr (litGen_int_complete n hpal')
  | litBool b =>
    simp only [wellTypedAt, getType] at htyp
    have hτ : τ = .bool := by
      cases τ
      · rfl
      · simp at htyp
    subst hτ
    unfold genLeaf
    split
    case _ _ => exact litGen_bool_complete b
    case _ _ _ _ =>
      simp only [Gen.Support.support_pick]
      exact Or.inr (litGen_bool_complete b)
  | var n =>
    -- e = .var n ; well-typed at τ ⇒ Γ[n]? = some τ.
    simp only [wellTypedAt, getType] at htyp
    have hidx : Γ[n]? = some τ := by
      cases hg : Γ[n]? with
      | none => simp [hg] at htyp
      | some τ' =>
        rw [hg] at htyp
        simp at htyp
        -- htyp : τ = τ'  (after simp)
        rw [htyp]
    have hmem : n ∈ varsOfType Γ τ := varsOfType_complete Γ τ n hidx
    unfold genLeaf
    split
    case _ hvars =>
      rw [hvars] at hmem; cases hmem
    case _ k rest hvars =>
      simp only [Gen.Support.support_pick]
      left
      have hmem_kr : n ∈ k :: rest := by rw [← hvars]; exact hmem
      exact support_varGen_foldr_var (k :: rest) (litGen τ) n hmem_kr
  | ite _ _ _ =>
    simp [Expr.depth] at hleaf
  | and _ _ =>
    simp [Expr.depth] at hleaf

-- ────────────────────────────────────────────────────────────────────
-- Step 4 helpers: converse decomposition lemmas for wellTypedAt on
-- compound forms. Mirror the wellTypedAt_ite / wellTypedAt_and helpers
-- from CedarMicro.Soundness in the `inverse` direction.
-- ────────────────────────────────────────────────────────────────────

private theorem wellTypedAt_ite_inv (Γ : List Ty) (τ : Ty) (c t f : Expr)
    (h : wellTypedAt Γ τ (.ite c t f) = true) :
    wellTypedAt Γ .bool c = true ∧
    wellTypedAt Γ τ t = true ∧
    wellTypedAt Γ τ f = true := by
  -- Decompose getType (.ite c t f) Γ via case analysis on each sub-result.
  unfold wellTypedAt getType at h
  cases hgc : getType c Γ with
  | none => rw [hgc] at h; simp at h
  | some τc =>
    cases hgt : getType t Γ with
    | none => rw [hgc, hgt] at h; simp at h
    | some τt =>
      cases hgf : getType f Γ with
      | none => rw [hgc, hgt, hgf] at h; simp at h
      | some τf =>
        rw [hgc, hgt, hgf] at h
        -- Now h is a guard chain. Case-split on each guard.
        by_cases hτcb : τc = .bool
        · subst hτcb
          by_cases hτtf : τt = τf
          · subst hτtf
            -- Now h : (match some τt with | some τ' => τ == τ' | none => false) = true
            simp at h
            -- h : τ = τt (after Bool decode)
            have hττ : τ = τt := by
              cases τ with
              | int => cases τt <;> simp at h; rfl
              | bool => cases τt <;> simp at h; rfl
            subst hττ
            refine ⟨?_, ?_, ?_⟩
            · unfold wellTypedAt; rw [hgc]; simp
            · unfold wellTypedAt; rw [hgt]; simp
            · unfold wellTypedAt; rw [hgf]; simp
          · simp [hτtf] at h
        · simp [hτcb] at h

private theorem wellTypedAt_and_inv (Γ : List Ty) (τ : Ty) (a b : Expr)
    (h : wellTypedAt Γ τ (.and a b) = true) :
    τ = .bool ∧ wellTypedAt Γ .bool a = true ∧ wellTypedAt Γ .bool b = true := by
  unfold wellTypedAt getType at h
  cases hga : getType a Γ with
  | none => rw [hga] at h; simp at h
  | some τa =>
    cases hgb : getType b Γ with
    | none => rw [hga, hgb] at h; simp at h
    | some τb =>
      rw [hga, hgb] at h
      by_cases hτa : τa = .bool
      · subst hτa
        by_cases hτb : τb = .bool
        · subst hτb
          simp at h
          have hττ : τ = .bool := by
            cases τ <;> simp at h; rfl
          subst hττ
          refine ⟨rfl, ?_, ?_⟩
          · unfold wellTypedAt; rw [hga]; simp
          · unfold wellTypedAt; rw [hgb]; simp
        · simp [hτb] at h
      · simp [hτa] at h

-- ────────────────────────────────────────────────────────────────────
-- Step 4: depth-≤1 completeness (the V1 generator's reachable scope).
--
-- The V1 generator recurses at fuel-0 only, so depth-1 is the
-- ceiling. Lifting to depth-k is camera-ready and requires
-- replacing the `genSize Γ 0 _` call inside the .succ arm with
-- `genSize Γ k _`.
-- ────────────────────────────────────────────────────────────────────

/-- Coverage at the V1 fuel scope (depth ≤ 1). Direct case analysis
    on the head constructor and the type τ; the `.ite` and `.and`
    arms factor through `wellTypedAt_ite_inv` /
    `wellTypedAt_and_inv` plus three `genLeaf_complete` calls each.
    Sorry-free. -/
theorem genSize_succ_complete (Γ : List Ty) (n : Nat) (τ : Ty) (e : Expr)
    (hpal : Expr.inPalette e)
    (hdepth : e.depth ≤ 1)
    (htyp : wellTypedAt Γ τ e = true) :
    _root_.Gen.support (genSize Γ (n+1) τ) e := by
  -- Either e is a leaf (depth 0) or a depth-1 compound.
  cases e with
  | litInt _ =>
    cases τ with
    | int =>
      simp only [genSize, Gen.Support.support_pick]
      left
      exact genLeaf_complete Γ .int _ hpal rfl htyp
    | bool =>
      simp only [wellTypedAt, getType] at htyp
      simp at htyp
  | litBool _ =>
    cases τ with
    | int =>
      simp only [wellTypedAt, getType] at htyp
      simp at htyp
    | bool =>
      simp only [genSize, Gen.Support.support_pick]
      left
      exact genLeaf_complete Γ .bool _ hpal rfl htyp
  | var _ =>
    cases τ with
    | int =>
      simp only [genSize, Gen.Support.support_pick]
      left
      exact genLeaf_complete Γ .int _ hpal rfl htyp
    | bool =>
      simp only [genSize, Gen.Support.support_pick]
      left
      exact genLeaf_complete Γ .bool _ hpal rfl htyp
  | ite c t f =>
    -- Depth-1 ite. Sub-expressions c, t, f must each be leaves.
    have hde : (Expr.ite c t f).depth = 1 + max c.depth (max t.depth f.depth) :=
      rfl
    rw [hde] at hdepth
    have hdc' : c.depth = 0 := by omega
    have hdt' : t.depth = 0 := by
      have : max t.depth f.depth ≤ 0 := by omega
      omega
    have hdf' : f.depth = 0 := by
      have : max t.depth f.depth ≤ 0 := by omega
      omega
    obtain ⟨htc, htt, htf⟩ := wellTypedAt_ite_inv Γ τ c t f htyp
    have hpc : c.inPalette ∧ t.inPalette ∧ f.inPalette := hpal
    obtain ⟨hpc', hpt', hpf'⟩ := hpc
    cases τ with
    | int =>
      simp only [genSize, Gen.Support.support_pick,
                 Gen.Support.support_bind, Gen.Support.support_pure]
      right
      refine ⟨c, ?_, t, ?_, f, ?_, rfl⟩
      · simpa [genSize] using genLeaf_complete Γ .bool c hpc' hdc' htc
      · simpa [genSize] using genLeaf_complete Γ .int  t hpt' hdt' htt
      · simpa [genSize] using genLeaf_complete Γ .int  f hpf' hdf' htf
    | bool =>
      simp only [genSize, Gen.Support.support_pick,
                 Gen.Support.support_bind, Gen.Support.support_pure]
      right; right
      refine ⟨c, ?_, t, ?_, f, ?_, rfl⟩
      · simpa [genSize] using genLeaf_complete Γ .bool c hpc' hdc' htc
      · simpa [genSize] using genLeaf_complete Γ .bool t hpt' hdt' htt
      · simpa [genSize] using genLeaf_complete Γ .bool f hpf' hdf' htf
  | and a b =>
    -- Depth-1 and. Symmetric to .ite. Both subexpressions must be leaves
    -- at .bool; result is .bool.
    have hde : (Expr.and a b).depth = 1 + max a.depth b.depth := rfl
    rw [hde] at hdepth
    have hda' : a.depth = 0 := by omega
    have hdb' : b.depth = 0 := by omega
    obtain ⟨hττ, hta, htb⟩ := wellTypedAt_and_inv Γ τ a b htyp
    subst hττ
    have hpab : a.inPalette ∧ b.inPalette := hpal
    obtain ⟨hpa', hpb'⟩ := hpab
    -- The .bool arm of genSize.succ has the .and branch.
    simp only [genSize, Gen.Support.support_pick,
               Gen.Support.support_bind, Gen.Support.support_pure]
    right; left
    refine ⟨a, ?_, b, ?_, rfl⟩
    · simpa [genSize] using genLeaf_complete Γ .bool a hpa' hda' hta
    · simpa [genSize] using genLeaf_complete Γ .bool b hpb' hdb' htb

-- ────────────────────────────────────────────────────────────────────
-- Main theorem: coverage-completeness dual of soundness.
-- ────────────────────────────────────────────────────────────────────

/-- Coverage-completeness of the hand-authored generator at the V1
    fuel scope (depth ≤ 1).

    Statement: every Cedar-micro expression on the literal palette
    that type-checks at the requested target type and has depth at
    most 1 is reachable by `genWellTyped Γ τ`.

    Pair: with `genWellTyped_sound`, the hand-authored V1 generator
    image is *contained in* and *contains* the depth-≤1 well-typed
    expressions on the palette. No type-correct depth-≤1
    palette-expression is missed; no out-of-spec expression is
    produced.

    The depth bound is the V1 fuel-recursion limit. Lifting to
    depth ≤ k requires the V2 generator that recurses at fuel `k`
    instead of `0` in the compound arms; the proof above
    generalises by induction on `n` once the V2 recursion is
    plumbed. -/
theorem genWellTyped_complete (Γ : List Ty) (τ : Ty) (e : Expr)
    (hpal : Expr.inPalette e)
    (hdepth : e.depth ≤ 1)
    (htyp : wellTypedAt Γ τ e = true) :
    _root_.Gen.support (genWellTyped Γ τ) e := by
  unfold genWellTyped
  exact genSize_succ_complete Γ 1 τ e hpal hdepth htyp

end Pythia.LanguageSemantics.Cedar
