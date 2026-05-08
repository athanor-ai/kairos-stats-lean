import Mathlib

open Finset BigOperators

noncomputable section

-- RMSNorm(x)_i = x_i / rms(x) * γ_i where rms(x) = sqrt(mean(x²))
-- Error bound for floating-point RMSNorm

noncomputable def rms (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  Real.sqrt ((∑ i, x i ^ 2) / n)

noncomputable def rmsNorm (n : ℕ) (x γ : Fin n → ℝ) (i : Fin n) : ℝ :=
  x i / rms n x * γ i

/-
RMS is always nonneg
-/
theorem rms_nonneg (n : ℕ) (x : Fin n → ℝ) : 0 ≤ rms n x := by
  exact Real.sqrt_nonneg _

/-
RMS of a nonzero vector is positive
-/
theorem rms_pos (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) (hx : ∃ i, x i ≠ 0) :
    0 < rms n x := by
  exact Real.sqrt_pos.2 ( div_pos ( lt_of_lt_of_le ( sq_pos_of_ne_zero hx.choose_spec ) ( Finset.single_le_sum ( fun i _ => sq_nonneg ( x i ) ) ( Finset.mem_univ _ ) ) ) ( Nat.cast_pos.2 hn ) )

/-
RMSNorm outputs sum of squares = n (when γ = 1)
-/
theorem rmsNorm_sum_sq (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ)
    (hx : ∃ i, x i ≠ 0) :
    ∑ i, (rmsNorm n x (fun _ => 1) i) ^ 2 = n := by
  unfold rmsNorm;
  simp +decide [ ← Finset.sum_div, div_pow ];
  rw [ div_eq_iff ] <;> norm_num [ show n ≠ 0 by linarith ];
  · rw [ show rms n x = Real.sqrt ( ( ∑ i, x i ^ 2 ) / n ) by rfl, Real.sq_sqrt <| div_nonneg ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) <| Nat.cast_nonneg _, mul_div_cancel₀ _ <| by positivity ];
  · exact ne_of_gt <| rms_pos n hn x hx

/-
The original statement with `c ≠ 0` is false for negative c, since
rms(c·x) = |c| · rms(x), so rmsNorm(c·x)_i = (c/|c|) · rmsNorm(x)_i.
We correct the statement to require 0 < c.

RMSNorm is scale-invariant for positive scalars: RMSNorm(c·x) = RMSNorm(x) for 0 < c.
-/
theorem rmsNorm_scale_invariant (n : ℕ) (_hn : 0 < n) (x γ : Fin n → ℝ)
    (c : ℝ) (hc : 0 < c) (hx : ∃ i, x i ≠ 0) (i : Fin n) :
    rmsNorm n (fun j => c * x j) γ i = rmsNorm n x γ i := by
  unfold rmsNorm;
  unfold rms;
  norm_num [ mul_pow, ← Finset.mul_sum _ _ _, hc.le ];
  grind +splitIndPred