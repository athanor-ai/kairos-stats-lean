import Mathlib

-- Fixed-point arithmetic correctness.
-- Hardware DSP blocks use fixed-point instead of floating-point.
-- Prove rounding and overflow properties.

def fixedMul (a b : Int) (frac_bits : ℕ) : Int :=
  (a * b) / (2 ^ frac_bits)

def fixedAdd (a b : Int) : Int := a + b

/-
Fixed-point multiplication rounding error
-/
theorem fixed_mul_error (a b : Int) (frac_bits : ℕ) :
    |fixedMul a b frac_bits * (2 ^ frac_bits) - a * b| < 2 ^ frac_bits := by
  unfold fixedMul;
  rw [ abs_sub_comm, abs_of_nonneg ];
  · linarith [ Int.mul_ediv_add_emod ( a * b ) ( 2 ^ frac_bits ), Int.emod_lt_of_pos ( a * b ) ( by positivity : ( 2 ^ frac_bits : ℤ ) > 0 ) ];
  · linarith [ Int.mul_ediv_add_emod ( a * b ) ( 2 ^ frac_bits ), Int.emod_nonneg ( a * b ) ( by positivity : ( 2 ^ frac_bits : ℤ ) ≠ 0 ) ]

/-
Fixed-point addition is exact (no rounding)
-/
theorem fixed_add_exact (a b : Int) :
    fixedAdd a b = a + b := by
  rfl

/-
Overflow detection: result exceeds representable range
-/
theorem fixed_overflow_detect (a b : Int) (max_val : Int) (_h : 0 < max_val) :
    max_val < a + b → max_val < fixedAdd a b := by
  exact fun h => h