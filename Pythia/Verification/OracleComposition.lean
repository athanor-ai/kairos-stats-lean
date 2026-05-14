/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Oracle Composition for Formal Verification

Soundness and completeness composition theorems for verification
oracles (SMT solvers, model checkers, theorem provers). Captures the
formal foundation for multi-tool verification pipelines where
solvers are composed sequentially or in parallel.

Motivated by the "Z3-as-auxiliary" pattern: when a primary solver
times out, a secondary solver can be tried without compromising
soundness — provided both individual solvers are sound.

## References

* Bradley, A. R. & Manna, Z. (2007): "The Calculus of Computation."
* Biere, A. et al. (2021): "Handbook of Satisfiability" (2nd ed.), Ch. 1.

General applied mathematics.
-/
import Mathlib

namespace Pythia.Verification.OracleComposition

/-- An oracle verdict: the tool either returns a definite answer or times out. -/
inductive Verdict (α : Type*)
  | definite : α → Verdict α
  | timeout : Verdict α

/-- A verification oracle: given a formula, returns a verdict. -/
def Oracle (Formula Result : Type*) := Formula → Verdict Result

/-- Soundness of an oracle w.r.t. a ground-truth predicate:
if the oracle returns a definite result, that result is correct. -/
def sound (oracle : Oracle F R) (correct : F → R → Prop) : Prop :=
  ∀ f r, oracle f = Verdict.definite r → correct f r

/-- Sequential composition: try oracle A first, on timeout try oracle B. -/
def seqComp (A B : Oracle F R) : Oracle F R := fun f =>
  match A f with
  | Verdict.definite r => Verdict.definite r
  | Verdict.timeout => B f

/-- Fallback composition: try A first, if A times out try B.
Operationally identical to `seqComp` but named distinctly for use
in contexts where the caller conceptually views both oracles as
running "in parallel" with A's result preferred when available.
In a pure-function model, parallel and sequential fallback coincide. -/
def fallbackComp (A B : Oracle F R) : Oracle F R := fun f =>
  match A f with
  | Verdict.definite r => Verdict.definite r
  | Verdict.timeout => B f

/-- **Soundness is preserved under sequential composition.**
If oracle A is sound and oracle B is sound (w.r.t. the same
correctness predicate), then trying A first and falling back
to B on timeout is also sound. -/
theorem seqComp_sound (A B : Oracle F R) (correct : F → R → Prop)
    (hA : sound A correct) (hB : sound B correct) :
    sound (seqComp A B) correct := by
  intro f r h
  simp only [seqComp] at h
  split at h
  · exact hA f r h
  · exact hB f r h

/-- **Soundness is preserved under fallback composition.** -/
theorem fallbackComp_sound (A B : Oracle F R) (correct : F → R → Prop)
    (hA : sound A correct) (hB : sound B correct) :
    sound (fallbackComp A B) correct := by
  intro f r h
  simp only [fallbackComp] at h
  split at h
  · exact hA f r h
  · exact hB f r h

/-- Sequential composition is at least as definite as either oracle alone:
if A returns a definite result, so does seqComp A B. -/
theorem seqComp_definite_of_left {A B : Oracle F R} {f : F} {r : R}
    (h : A f = Verdict.definite r) :
    seqComp A B f = Verdict.definite r := by
  simp only [seqComp, h]

/-- If A times out, sequential composition delegates to B. -/
theorem seqComp_timeout_delegates {A B : Oracle F R} {f : F}
    (h : A f = Verdict.timeout) :
    seqComp A B f = B f := by
  simp only [seqComp, h]

/-- N-fold sequential composition: try each oracle in order. -/
def nSeqComp : List (Oracle F R) → Oracle F R
  | [] => fun _ => Verdict.timeout
  | o :: os => seqComp o (nSeqComp os)

/-- **Soundness is preserved under N-fold sequential composition.** -/
theorem nSeqComp_sound (oracles : List (Oracle F R)) (correct : F → R → Prop)
    (hAll : ∀ o ∈ oracles, sound o correct) :
    sound (nSeqComp oracles) correct := by
  induction oracles with
  | nil => intro f r h; simp [nSeqComp] at h
  | cons o os ih =>
    apply seqComp_sound
    · exact hAll o (List.mem_cons_self o os)
    · exact ih (fun o' ho' => hAll o' (List.mem_cons_of_mem o ho'))

/-- **Known-bad receipt: an unsound oracle exists.**
Constructive witness that the `sound` predicate is non-trivial:
there exists an oracle that returns a definite (but incorrect)
result, violating soundness. This proves the soundness theorems
above are not vacuously true on an empty domain. -/
theorem exists_unsound_oracle :
    ∃ (o : Oracle Bool Bool) (correct : Bool → Bool → Prop),
      ¬sound o correct := by
  refine ⟨fun _ => Verdict.definite true, fun _ b => b = false, ?_⟩
  intro h
  have := h true true rfl
  exact absurd this (by decide)

end Pythia.Verification.OracleComposition
