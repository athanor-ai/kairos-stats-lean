import Mathlib

-- AXI protocol handshake: VALID must not depend on READY.
-- The fundamental AXI rule that prevents deadlock.

-- VALID asserted independently of READY
def validIndependent (valid_fn : Bool → Bool) : Prop :=
  valid_fn true = valid_fn false

-- If VALID is asserted, it stays until READY
def validStable (valid : ℕ → Bool) (ready : ℕ → Bool) : Prop :=
  ∀ t, valid t = true → ready t = false → valid (t + 1) = true

-- Transfer occurs on VALID ∧ READY
def transfer (valid ready : ℕ → Bool) (t : ℕ) : Bool :=
  valid t && ready t

/-
No transfer without VALID
-/
theorem no_transfer_without_valid (valid ready : ℕ → Bool) (t : ℕ)
    (h : valid t = false) : transfer valid ready t = false := by
  -- By definition of transfer, if valid t is false, then transfer valid ready t is false.
  simp [transfer, h]

/-
Stable VALID guarantees eventual transfer under fair READY
-/
theorem stable_valid_eventual_transfer
    (valid ready : ℕ → Bool) (t₀ : ℕ)
    (h_valid : valid t₀ = true)
    (h_stable : validStable valid ready)
    (h_fair : ∃ t, t₀ ≤ t ∧ ready t = true) :
    ∃ t, t₀ ≤ t ∧ transfer valid ready t = true := by
  -- By induction on n where t = t₀ + n, show valid (t₀ + n) = true using h_stable.
  have h_ind : ∀ n ≥ 0, valid (t₀ + n) = true ∨ ∃ m ≤ n, ready (t₀ + m) = true := by
    intro n hn; induction hn <;> simp_all +decide [ Nat.succ_eq_add_one ] ;
    grind +locals;
  contrapose! h_ind;
  obtain ⟨ t, ht₁, ht₂ ⟩ := Nat.findX h_fair;
  use t - t₀ - 1;
  grind +locals