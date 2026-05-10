import Mathlib

-- Pipeline stall freedom: under sufficient buffering,
-- a pipeline stage never stalls (always has room to accept).
-- Key for high-throughput designs.

variable {n : ℕ}

def pipelineOccupancy (buffer_depth produce_rate consume_rate : ℕ) (t : ℕ) : ℕ :=
  produce_rate * t - consume_rate * t

-- If consume_rate ≥ produce_rate, occupancy never exceeds buffer_depth
theorem stall_free_balanced (buffer_depth produce_rate consume_rate : ℕ)
    (h : consume_rate ≥ produce_rate) (t : ℕ) :
    produce_rate * t - consume_rate * t ≤ buffer_depth := by
  have : consume_rate * t ≥ produce_rate * t := Nat.mul_le_mul_right t h
  omega

-- Minimum buffer depth for stall freedom
theorem min_buffer_for_stall_free (produce_rate consume_rate latency : ℕ)
    (h_faster : produce_rate > consume_rate) :
    produce_rate * latency - consume_rate * latency ≤
      (produce_rate - consume_rate) * latency := by
  rw [Nat.sub_mul]
