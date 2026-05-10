import Mathlib

-- Branch predictor safety: mispredictions are always caught
-- and corrected. No architectural state corruption from
-- speculative execution on wrong path.

structure BPState where
  prediction : Bool  -- predicted taken/not-taken
  actual : Bool      -- actual branch outcome
  speculative_state : ℕ  -- speculative architectural state
  committed_state : ℕ    -- committed architectural state

def mispredicted (s : BPState) : Bool := s.prediction != s.actual

def recover (s : BPState) : BPState :=
  if mispredicted s then { s with speculative_state := s.committed_state }
  else s

-- Recovery restores committed state on mispredict
theorem recover_restores_on_mispredict (s : BPState) (h : mispredicted s = true) :
    (recover s).speculative_state = s.committed_state := by
  simp [recover, mispredicted] at h ⊢
  split <;> simp_all

-- No recovery needed on correct prediction
theorem no_recover_on_correct (s : BPState) (h : mispredicted s = false) :
    (recover s).speculative_state = s.speculative_state := by
  simp [recover, h]

-- Committed state is never affected by speculation
theorem committed_unchanged (s : BPState) :
    (recover s).committed_state = s.committed_state := by
  simp [recover]
  split <;> rfl
