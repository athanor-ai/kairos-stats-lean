import Mathlib

-- Hardware semaphore for multi-core synchronization.
-- Test-and-set atomic operation prevents race conditions.

structure SemState where
  locked : Bool
  owner : ℕ

def tryAcquire (s : SemState) (core : ℕ) : SemState × Bool :=
  if s.locked then (s, false)
  else ({ locked := true, owner := core }, true)

def release (s : SemState) (core : ℕ) : SemState :=
  if s.locked && s.owner = core then { locked := false, owner := 0 }
  else s

-- Acquire on unlocked succeeds
theorem acquire_unlocked (s : SemState) (core : ℕ) (h : s.locked = false) :
    (tryAcquire s core).2 = true := by
  simp [tryAcquire, h]

-- Acquire on locked fails
theorem acquire_locked (s : SemState) (core : ℕ) (h : s.locked = true) :
    (tryAcquire s core).2 = false := by
  simp [tryAcquire, h]

-- After acquire, owner is the acquiring core
theorem acquire_sets_owner (s : SemState) (core : ℕ) (h : s.locked = false) :
    (tryAcquire s core).1.owner = core := by
  simp [tryAcquire, h]

-- Release by owner unlocks
theorem release_by_owner (s : SemState) (core : ℕ)
    (h_locked : s.locked = true) (h_owner : s.owner = core) :
    (release s core).locked = false := by
  simp [release, h_locked, h_owner]

-- Release by non-owner has no effect
theorem release_by_nonowner (s : SemState) (core : ℕ)
    (h : s.owner ≠ core) :
    release s core = s := by
  simp [release]
  cases s.locked <;> simp [h]
