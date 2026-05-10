import Mathlib

-- Formal refinement theory: abstraction-refinement between
-- specification and implementation. The mathematical backbone
-- of all hardware verification.

variable {Spec Impl : Type*}

-- A refinement relation: implementation refines specification
structure Refinement (Spec Impl : Type*) where
  abs : Impl → Spec  -- abstraction function
  spec_step : Spec → Spec
  impl_step : Impl → Impl
  commutes : ∀ i, abs (impl_step i) = spec_step (abs i)

/- The original statement of `refinement_compose` is false as stated: it lacks the
   hypothesis that `r2.spec_step = r1.impl_step` (the intermediate steps must agree).
   Counterexample: r1 = ⟨id, not, not, …⟩ and r2 = ⟨id, id, id, …⟩ on Bool.
   The corrected version adds the linking hypothesis `h_link`. -/

/-- Refinement composes when the intermediate steps agree:
    `r2.spec_step` (the spec-level step of the lower refinement) must equal
    `r1.impl_step` (the impl-level step of the upper refinement). -/
theorem refinement_compose {Mid : Type*}
    (r1 : Refinement Spec Mid) (r2 : Refinement Mid Impl)
    (h_link : r2.spec_step = r1.impl_step) :
    ∀ i, r1.abs (r2.abs (r2.impl_step i)) = r1.spec_step (r1.abs (r2.abs i)) := by
  intro i
  rw [r2.commutes]
  rw [h_link]
  rw [r1.commutes]

/-
Refinement preserves safety properties
-/
theorem refinement_preserves_safety
    (r : Refinement Spec Impl) (P : Spec → Prop)
    (h : ∀ s, P s → P (r.spec_step s))
    (i : Impl) (h_init : P (r.abs i)) :
    ∀ n, P (r.abs (Nat.iterate r.impl_step n i)) := by
  intro n;
  induction' n with n ih;
  · exact h_init;
  · simpa only [ Function.iterate_succ_apply', r.commutes ] using h _ ih

/-
Data refinement: if spec and impl agree on observations,
the impl is a valid refinement
-/
theorem observation_refinement
    {Obs : Type*} (spec_obs : Spec → Obs) (impl_obs : Impl → Obs)
    (r : Refinement Spec Impl)
    (h : ∀ i, spec_obs (r.abs i) = impl_obs i) :
    ∀ (n : ℕ) (i : Impl),
      spec_obs (r.abs (Nat.iterate r.impl_step n i)) =
      impl_obs (Nat.iterate r.impl_step n i) := by
  grind
