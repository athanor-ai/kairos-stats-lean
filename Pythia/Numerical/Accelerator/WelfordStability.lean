import Mathlib

open Finset BigOperators

noncomputable section

-- Welford's online algorithm for mean and variance.
-- mean_n = mean_{n-1} + (x_n - mean_{n-1}) / n
-- M2_n = M2_{n-1} + (x_n - mean_{n-1}) * (x_n - mean_n)
-- variance_n = M2_n / n

noncomputable def welfordMean : (n : ℕ) → (x : Fin n → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, x => welfordMean n (x ∘ Fin.castSucc) +
      (x ⟨n, Nat.lt_succ_iff.mpr (le_refl n)⟩ -
       welfordMean n (x ∘ Fin.castSucc)) / (n + 1)

noncomputable def trueMean (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  if h : 0 < n then (∑ i, x i) / n else 0

/-
Helper: welfordMean n x * n = ∑ i, x i
-/
theorem welfordMean_mul_eq_sum (n : ℕ) (x : Fin n → ℝ) :
    welfordMean n x * n = ∑ i, x i := by
  induction' n with n ih <;> norm_num [ Fin.sum_univ_castSucc ] at *;
  grind +locals

/-
Welford's online mean equals the true mean
-/
theorem welford_mean_correct (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) :
    welfordMean n x = trueMean n x := by
  unfold trueMean;
  rw [ ← welfordMean_mul_eq_sum, mul_div_cancel_right₀ _ ( by positivity ) ] ; aesop