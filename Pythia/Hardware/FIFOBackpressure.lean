import Mathlib

-- FIFO backpressure correctness: when FIFO is full,
-- backpressure signal prevents data loss.
-- Common pattern in NoC routers and pipeline stages.

structure BPFifoState where
  count : ℕ
  depth : ℕ
  h_depth_pos : 0 < depth

def isFull (s : BPFifoState) : Bool := decide (s.count = s.depth)
def isEmpty (s : BPFifoState) : Bool := decide (s.count = 0)

def bpWrite (s : BPFifoState) (h : s.count < s.depth) : BPFifoState :=
  { s with count := s.count + 1 }

def bpRead (s : BPFifoState) (h : 0 < s.count) : BPFifoState :=
  { s with count := s.count - 1 }

-- Backpressure prevents overflow: can only write when not full
theorem backpressure_prevents_overflow (s : BPFifoState)
    (h : s.count < s.depth) :
    (bpWrite s h).count ≤ s.depth := by
  unfold bpWrite; simp; omega

-- After read, FIFO is not full (backpressure can deassert)
theorem read_deasserts_backpressure (s : BPFifoState)
    (h_read : 0 < s.count) (h_full : s.count = s.depth) :
    (bpRead s h_read).count < s.depth := by
  unfold bpRead; simp; omega

-- No data loss: count tracks number of elements faithfully
theorem count_faithful_write (s : BPFifoState) (h : s.count < s.depth) :
    (bpWrite s h).count = s.count + 1 := by
  unfold bpWrite; simp

theorem count_faithful_read (s : BPFifoState) (h : 0 < s.count) :
    (bpRead s h).count = s.count - 1 := by
  unfold bpRead; simp
