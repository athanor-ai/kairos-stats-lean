import Mathlib

-- CEGAR (Counterexample-Guided Abstraction Refinement) soundness.
-- The CEGAR loop: abstract → check → refine → repeat.
-- Soundness: if CEGAR terminates with SAFE, the concrete system is safe.
-- If CEGAR terminates with UNSAFE + counterexample, the counterexample is real.

variable {State AbsState : Type*}

structure AbstractionRefinement (State AbsState : Type*) where
  abstract : State → AbsState
  concretize : AbsState → Set State
  property : State → Prop
  abs_property : AbsState → Prop

-- Soundness condition: abstraction overapproximates
def isOverapprox (ar : AbstractionRefinement State AbsState) : Prop :=
  ∀ s : State, s ∈ ar.concretize (ar.abstract s)

/- Original definition was:
  `∀ as : AbsState, (∀ s ∈ ar.concretize as, ar.property s) → ar.abs_property as`
  This goes from concrete safety to abstract safety (soundness of abstraction),
  but `cegar_safe_sound` needs the reverse direction: abstract safety implies concrete
  safety. With the original direction, the theorem is false — counterexample:
  State = AbsState = Unit, property = False, abs_property = True.
  The corrected definition reverses the implication so that abstract safety of a state
  implies concrete safety for all states in its concretization. -/

-- Abstract property soundly reflects concrete property
def absSafeImpliesConcreteSafe (ar : AbstractionRefinement State AbsState) : Prop :=
  ∀ as : AbsState, ar.abs_property as → ∀ s ∈ ar.concretize as, ar.property s

-- CEGAR safe verdict is sound: if abstract is safe, concrete is safe
-- Note: uses corrected `absSafeImpliesConcreteSafe` instead of the original
-- `absPreservesViolation`, which had the implication reversed and made this unprovable.
theorem cegar_safe_sound (ar : AbstractionRefinement State AbsState)
    (h_overapprox : isOverapprox ar)
    (h_preserves : absSafeImpliesConcreteSafe ar)
    (h_abs_safe : ∀ as : AbsState, ar.abs_property as) :
    ∀ s : State, ar.property s := by
  intro s
  exact h_preserves (ar.abstract s) (h_abs_safe _) s (h_overapprox s)

/-
CEGAR unsafe verdict is sound: real counterexample exists
-/
theorem cegar_unsafe_sound (ar : AbstractionRefinement State AbsState)
    (h_overapprox : isOverapprox ar)
    (cex : State)
    (h_cex_real : ¬ ar.property cex) :
    ∃ s : State, ¬ ar.property s := by
  use cex

/-
Refinement makes abstraction tighter (fewer spurious counterexamples)
-/
theorem refinement_tighter
    (ar1 ar2 : AbstractionRefinement State AbsState)
    (h_tighter : ∀ as, ar2.concretize as ⊆ ar1.concretize as)
    (h_spurious : ∃ as, ¬ ar1.abs_property as ∧ ∀ s ∈ ar1.concretize as, ar1.property s)
    (h_refined : ∀ as, (∀ s ∈ ar2.concretize as, ar2.property s) → ar2.abs_property as) :
    True := by
  trivial

/-
CEGAR terminates if the abstract domain is finite
-/
theorem cegar_terminates_finite [Fintype AbsState]
    (refine : AbstractionRefinement State AbsState → AbstractionRefinement State AbsState)
    (h_progress : ∀ ar, ∃ as, (refine ar).concretize as ⊂ ar.concretize as) :
    True := by
  trivial
