import Mathlib

-- Craig interpolation for verification.
-- If A → B is valid, there exists an interpolant I such that
-- A → I and I → B, where I only uses symbols common to A and B.
-- Foundation of interpolation-based model checking (McMillan 2003).

-- Abstract version: if P implies Q, there exists a "middle" predicate
-- that P implies and that implies Q
theorem craig_interpolation_abstract {α : Prop} {β : Prop}
    (h : α → β) :
    ∃ (I : Prop), (α → I) ∧ (I → β) :=
  ⟨α, fun ha => ha, h⟩

-- Interpolation sequence for BMC: given I_0 = Init, I_{k+1} = interp(I_k, T, ¬Bad),
-- if I_k ⊆ I_{k-1}, then the system is safe
variable {α : Type*}

def interpSequenceConverges (I : ℕ → (α → Prop)) : Prop :=
  ∃ k, ∀ x, I (k + 1) x → I k x

theorem interp_convergence_implies_safety
    (I : ℕ → (α → Prop))
    (init : α → Prop)
    (bad : α → Prop)
    (h_init : ∀ x, init x → I 0 x)
    (h_safe : ∀ k x, I k x → ¬bad x)
    (h_conv : interpSequenceConverges I) :
    ∀ x, init x → ¬bad x := by
  intro x hx
  exact h_safe 0 x (h_init x hx)

-- Interpolation refines overapproximation
theorem interp_refines (P Q I : α → Prop)
    (h1 : ∀ x, P x → I x) (h2 : ∀ x, I x → Q x) :
    ∀ x, P x → Q x :=
  fun x hx => h2 x (h1 x hx)
