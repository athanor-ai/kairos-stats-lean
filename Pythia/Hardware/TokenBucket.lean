import Mathlib

-- Token bucket rate limiter correctness.
-- Used in QoS enforcement for NoC and network interfaces.
-- Tokens replenish at fixed rate, consumed on send.

structure TokenBucketState where
  tokens : ℕ
  max_tokens : ℕ
  refill_rate : ℕ

def refill (s : TokenBucketState) : TokenBucketState :=
  { s with tokens := min (s.tokens + s.refill_rate) s.max_tokens }

def consume (s : TokenBucketState) (cost : ℕ) (h : cost ≤ s.tokens) : TokenBucketState :=
  { s with tokens := s.tokens - cost }

/-
Tokens never exceed max
-/
theorem tokens_bounded (s : TokenBucketState) :
    (refill s).tokens ≤ s.max_tokens := by
  exact min_le_right _ _

/-
Consume reduces tokens
-/
theorem consume_reduces (s : TokenBucketState) (cost : ℕ) (h : cost ≤ s.tokens) (hc : 0 < cost) :
    (consume s cost h).tokens < s.tokens := by
  exact Nat.sub_lt ( Nat.pos_of_ne_zero ( by aesop ) ) hc

/-
Refill then consume: tokens ≤ max
-/
theorem refill_consume_bounded (s : TokenBucketState) (cost : ℕ) (h : cost ≤ (refill s).tokens) :
    (consume (refill s) cost h).tokens ≤ s.max_tokens := by
  exact le_trans ( Nat.sub_le _ _ ) ( tokens_bounded s )