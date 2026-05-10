import Mathlib

-- Reset sequence correctness: a multi-domain SoC must
-- release resets in the correct order (clock domain
-- dependencies). Releasing a domain before its clock
-- is stable causes metastability.

structure ResetDomain where
  name : String
  depends_on : List String

-- List.indexOf? is not in this Mathlib version, so we define it.
def List.indexOf? {α : Type} [BEq α] (a : α) (l : List α) : Option Nat :=
  l.findIdx? (· == a)

-- A reset ordering is valid if every domain is released
-- after all its dependencies
def validResetOrder (domains : List ResetDomain) (order : List String) : Prop :=
  ∀ d ∈ domains, ∀ dep ∈ d.depends_on,
    match order.indexOf? dep, order.indexOf? d.name with
    | some i, some j => i < j
    | _, _ => False

/-
No circular dependencies means a valid order exists
(topological sort exists for DAGs)
-/
theorem acyclic_has_valid_order (domains : List ResetDomain)
    (h_acyclic : ∀ d ∈ domains, d.name ∉ d.depends_on) :
    domains.length ≤ 1 → ∃ order, validResetOrder domains order := by
  cases domains <;> simp_all +decide;
  · exact ⟨ [ ], by tauto ⟩;
  · rename_i h t;
    rintro rfl;
    use h.depends_on ++ [h.name];
    intro d hd dep hdep;
    have h_index : List.findIdx? (fun x => x == dep) h.depends_on < List.length h.depends_on := by
      have h_index : ∀ {l : List String} {x : String}, x ∈ l → List.findIdx? (fun y => y == x) l < some l.length := by
        intros l x hx; induction l <;> simp_all +decide [ List.findIdx?_cons ] ;
        cases h : List.findIdx? ( fun y => y == x ) ‹_› <;> aesop;
      aesop;
    simp_all +decide;
    rw [ show List.indexOf? dep ( h.depends_on ++ [ h.name ] ) = List.findIdx? ( fun x => x == dep ) ( h.depends_on ++ [ h.name ] ) from ?_, show List.indexOf? h.name ( h.depends_on ++ [ h.name ] ) = List.findIdx? ( fun x => x == h.name ) ( h.depends_on ++ [ h.name ] ) from ?_ ];
    · rw [ show List.findIdx? ( fun x => x == dep ) ( h.depends_on ++ [ h.name ] ) = List.findIdx? ( fun x => x == dep ) h.depends_on from ?_, show List.findIdx? ( fun x => x == h.name ) ( h.depends_on ++ [ h.name ] ) = some ( List.length h.depends_on ) from ?_ ];
      · cases h : List.findIdx? ( fun x => x == dep ) h.depends_on <;> aesop;
      · grind;
      · grind;
    · induction ( h.depends_on ++ [ h.name ] ) <;> aesop;
    · induction ( h.depends_on ++ [ h.name ] ) <;> aesop

/-
The original statement below is false. Counterexample: d = ⟨"a", ["b"]⟩.
   Then validResetOrder [d] [d.name] is False (since "b" is not in order ["a"]),
   and d.depends_on = ["b"] ≠ []. So neither disjunct holds.

theorem single_domain_valid (d : ResetDomain) :
    validResetOrder [d] [d.name] ∨ d.depends_on = [] := by
  sorry

Corrected version: a single domain with no dependencies always has a valid order.
    The original statement `validResetOrder [d] [d.name] ∨ d.depends_on = []` is false
    when `d` has dependencies not equal to `d.name` (e.g., `d = ⟨"a", ["b"]⟩`),
    because those dependencies would need to appear in the order list.
    The corrected statement handles both cases: if depends_on is empty, [d.name] works;
    otherwise, the disjunct d.depends_on = [] is vacuously available only when it holds.
-/
theorem single_domain_valid (d : ResetDomain) :
    d.depends_on = [] → validResetOrder [d] [d.name] := by
  -- By definition of `validResetOrder`, we need to show that for any domain `d` in `[d]`, and any dependency `dep` in `d.depends_on`, `dep` appears before `d.name` in the order `[d.name]`.
  -- Since there's only one domain in `[d]`, the only dependency to check is the one in `d`.
  -- Since `d.depends_on = []`, there are no dependencies, so the condition is trivially satisfied.
  intro h
  simp [validResetOrder, h]
