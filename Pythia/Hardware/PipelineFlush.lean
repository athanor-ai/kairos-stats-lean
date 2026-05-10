import Mathlib

-- Pipeline flush correctness: on exception/branch mispredict,
-- all in-flight instructions are squashed and the pipeline
-- returns to a known-good state.

variable {n : ℕ} {α : Type*}

@[ext]
structure PipeState (n : ℕ) (α : Type*) where
  stages : Fin n → Option α
  valid : Fin n → Bool

def flushPipeline (_s : PipeState n α) : PipeState n α :=
  { stages := fun _ => none, valid := fun _ => false }

def countValid (s : PipeState n α) : ℕ :=
  (Finset.univ.filter (fun i => s.valid i)).card

-- Flush empties all stages
theorem flush_all_empty (s : PipeState n α) :
    ∀ i : Fin n, (flushPipeline s).stages i = none := by
  intro i; simp [flushPipeline]

-- Flush invalidates all stages
theorem flush_all_invalid (s : PipeState n α) :
    ∀ i : Fin n, (flushPipeline s).valid i = false := by
  intro i; simp [flushPipeline]

-- Flush reduces valid count to zero
theorem flush_zero_valid (s : PipeState n α) :
    countValid (flushPipeline s) = 0 := by
  simp [countValid, flushPipeline]

-- Flush is idempotent
theorem flush_idempotent (s : PipeState n α) :
    flushPipeline (flushPipeline s) = flushPipeline s := by
  ext <;> simp [flushPipeline]
