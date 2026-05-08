import Mathlib

-- Power-gated register: when memory enable ME=0, output holds previous value.
-- Gold: register always updates from data_in on clock edge.
-- Gate: register updates only when ME=1; holds when ME=0.
-- Prove: observable output equivalence when ME=1 on every observation cycle.

variable {α : Type*} [DecidableEq α]

structure RegTrace (α : Type*) where
  data_in : ℕ → α
  me      : ℕ → Bool
  init    : α

-- Ungated register: always takes data_in
def ungatedReg (t : RegTrace α) : ℕ → α
  | 0 => t.init
  | n + 1 => t.data_in n

-- Gated register: takes data_in only when ME=1, else holds
def gatedReg (t : RegTrace α) : ℕ → α
  | 0 => t.init
  | n + 1 => if t.me n then t.data_in n else gatedReg t n

/-
When ME=1, the gated register updates to data_in (same as ungated)
-/
omit [DecidableEq α] in
theorem gated_updates_when_enabled (t : RegTrace α) (n : ℕ) (h : t.me n = true) :
    gatedReg t (n + 1) = t.data_in n := by
  -- By definition of gatedReg, if ME=1, then gatedReg t (n + 1) = t.data_in n.
  simp [gatedReg, h]

/-
When ME=0, the gated register holds its previous value
-/
omit [DecidableEq α] in
theorem gated_holds_when_disabled (t : RegTrace α) (n : ℕ) (h : t.me n = false) :
    gatedReg t (n + 1) = gatedReg t n := by
  unfold gatedReg; aesop;

/-
If ME=1 at every step, gated and ungated produce identical traces
-/
omit [DecidableEq α] in
theorem power_gate_equiv_always_enabled (t : RegTrace α) (h : ∀ n, t.me n = true) :
    ∀ n, gatedReg t n = ungatedReg t n := by
  intro n
  induction' n with n ih;
  · rfl;
  · rw [ show gatedReg t ( n + 1 ) = if t.me n then t.data_in n else gatedReg t n from rfl, show ungatedReg t ( n + 1 ) = t.data_in n from rfl, h, if_pos rfl ]

/-
Gated register value is always either init or some data_in value
(no spurious values introduced by gating)
-/
omit [DecidableEq α] in
theorem gated_reg_value_safe (t : RegTrace α) (n : ℕ) :
    gatedReg t n = t.init ∨ ∃ k, k < n ∧ gatedReg t n = t.data_in k := by
  induction' n with n ih;
  · exact Or.inl rfl;
  · grind +locals