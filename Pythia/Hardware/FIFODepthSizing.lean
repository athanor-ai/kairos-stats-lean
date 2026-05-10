import Mathlib

-- FIFO depth sizing: minimum depth to prevent overflow
-- given producer and consumer rates with latency.
-- Directly relevant for NoC buffer sizing decisions.

-- Minimum FIFO depth to avoid overflow
def minFIFODepth (producerRate consumerRate latency : ℕ) : ℕ :=
  if producerRate ≤ consumerRate then 1
  else (producerRate - consumerRate) * latency + 1

/-
If depth ≥ minFIFODepth, no overflow for latency cycles
-/
theorem depth_sufficient (prodRate consRate latency depth : ℕ)
    (h : minFIFODepth prodRate consRate latency ≤ depth) :
    (prodRate - consRate) * latency < depth := by
  unfold minFIFODepth at h;
  grind

/-
Balanced rates need depth 1
-/
theorem balanced_needs_one (rate latency : ℕ) :
    minFIFODepth rate rate latency = 1 := by
  exact if_pos le_rfl

/-
Depth scales linearly with latency
-/
theorem depth_linear_latency (prodRate consRate : ℕ) (h : consRate < prodRate)
    (l1 l2 : ℕ) (hl : l1 ≤ l2) :
    minFIFODepth prodRate consRate l1 ≤ minFIFODepth prodRate consRate l2 := by
  unfold minFIFODepth; aesop;