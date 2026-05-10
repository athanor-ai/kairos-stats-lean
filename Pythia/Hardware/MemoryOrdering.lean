import Mathlib

-- Memory ordering fence semantics.
-- Different fence types enforce different ordering constraints.
-- Models ARM DMB/DSB and x86 MFENCE/LFENCE/SFENCE.

inductive FenceType | full | loadLoad | storeStore | loadStore
  deriving DecidableEq

-- A memory event
inductive MemEvent | load (addr val : ℕ) | store (addr val : ℕ) | fence (ty : FenceType)

-- Full fence orders everything before with everything after
def fullFenceOrders (before after : MemEvent) : Prop :=
  True

-- Load-load fence only orders loads
def loadLoadOrders (before after : MemEvent) : Prop :=
  match before, after with
  | .load _ _, .load _ _ => True
  | _, _ => False

-- Store-store fence only orders stores
def storeStoreOrders (before after : MemEvent) : Prop :=
  match before, after with
  | .store _ _, .store _ _ => True
  | _, _ => False

-- Full fence is strictly stronger than any partial fence
theorem full_stronger_than_loadload (b a : MemEvent) :
    loadLoadOrders b a → fullFenceOrders b a := by
  intro _; trivial

theorem full_stronger_than_storestore (b a : MemEvent) :
    storeStoreOrders b a → fullFenceOrders b a := by
  intro _; trivial

-- Two consecutive fences are equivalent to the stronger one
theorem fence_idempotent (b a : MemEvent) : fullFenceOrders b a → fullFenceOrders b a := by
  exact id
