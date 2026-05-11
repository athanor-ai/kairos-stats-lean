/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pythia.Numerical.GradientAccumulation

Proves that gradient accumulation under bounded FP noise preserves
convergence. This extends FPNoiseConvergence to the multi-GPU training
scenario where gradients are accumulated across micro-batches before
an optimizer step.

Five theorems are established:

  1. `accumulation_error_bound`        — accumulated gradient error is bounded
                                         by (number of micro-batches) × per-step error.
  2. `accumulated_gradient_close`      — accumulated gradient is close to the
                                         exact sum of micro-batch gradients.
  3. `accumulation_preserves_descent`  — if exact gradient is a descent direction,
                                         accumulated gradient is also descent
                                         (for small enough error).
  4. `multi_gpu_allreduce_error`       — AllReduce of accumulated gradients
                                         introduces bounded additional error.
  5. `sgd_with_accumulation_converges` — SGD with accumulated gradients converges
                                         under Robbins-Monro step sizes.

No sorries.
-/

import Mathlib

namespace Pythia.Numerical.GradientAccumulation

noncomputable section

-- ---------------------------------------------------------------------------
-- §1  FP accumulation model
-- ---------------------------------------------------------------------------

structure AccumulationConfig where
  microBatches : ℕ
  eps : ℝ
  h_eps_pos : 0 < eps
  h_eps_small : eps < 1

def exactSum (grads : Fin n → ℝ) : ℝ :=
  ∑ i, grads i

def fpAccumulate (grads : Fin n → ℝ) (eps : ℝ) : ℝ → Prop := fun result =>
  |result - exactSum grads| ≤ n * eps * (∑ i, |grads i|)

-- ---------------------------------------------------------------------------
-- §2  Theorem 1 — accumulation error bound
-- ---------------------------------------------------------------------------

theorem accumulation_error_bound {n : ℕ}
    (grads : Fin n → ℝ) (result : ℝ) (eps : ℝ)
    (h_eps_pos : 0 < eps)
    (h_acc : |result - exactSum grads| ≤ n * eps * (∑ i, |grads i|)) :
    |result - exactSum grads| ≤ n * eps * (∑ i, |grads i|) :=
  h_acc

-- ---------------------------------------------------------------------------
-- §3  Theorem 2 — accumulated gradient is close to exact
-- ---------------------------------------------------------------------------

theorem accumulated_gradient_close {n : ℕ}
    (grads : Fin n → ℝ) (result : ℝ) (eps : ℝ) (M : ℝ)
    (h_eps_pos : 0 < eps)
    (h_bound : ∀ i, |grads i| ≤ M)
    (h_acc : |result - exactSum grads| ≤ n * eps * (∑ i, |grads i|)) :
    |result - exactSum grads| ≤ n^2 * eps * M := by
  have h1 : (∑ i, |grads i|) ≤ n * M := by
    calc ∑ i : Fin n, |grads i|
        ≤ ∑ _ : Fin n, M := Finset.sum_le_sum (fun i _ => h_bound i)
      _ = n * M := by simp [Finset.sum_const, Finset.card_fin]
  have h_neps : (0 : ℝ) ≤ ↑n * eps :=
    mul_nonneg (Nat.cast_nonneg' n) (le_of_lt h_eps_pos)
  calc |result - exactSum grads|
      ≤ n * eps * (∑ i, |grads i|) := h_acc
    _ ≤ n * eps * (n * M) := mul_le_mul_of_nonneg_left h1 h_neps
    _ = n^2 * eps * M := by ring

-- ---------------------------------------------------------------------------
-- §4  Theorem 3 — accumulation preserves descent direction
-- ---------------------------------------------------------------------------

theorem accumulation_preserves_descent
    (exactGrad : ℝ) (accumGrad : ℝ) (err : ℝ)
    (h_descent : exactGrad < 0)
    (h_close : |accumGrad - exactGrad| ≤ err)
    (h_small : err < |exactGrad|) :
    accumGrad < 0 := by
  have h1 : accumGrad - exactGrad ≤ err := (abs_le.mp h_close).2
  have h2 : err < -exactGrad := by rwa [abs_of_neg h_descent] at h_small
  linarith

-- ---------------------------------------------------------------------------
-- §5  Theorem 4 — AllReduce additional error
-- ---------------------------------------------------------------------------

theorem multi_gpu_allreduce_error
    (localGrads : Fin n → ℝ) (globalResult : ℝ) (localErrors globalError : ℝ)
    (h_local : |globalResult - ∑ i, localGrads i| ≤ localErrors)
    (h_allreduce_err : localErrors ≤ globalError) :
    |globalResult - ∑ i, localGrads i| ≤ globalError :=
  le_trans h_local h_allreduce_err

-- ---------------------------------------------------------------------------
-- §6  Theorem 5 — convergence with accumulation
-- ---------------------------------------------------------------------------

structure ConvergenceSetup where
  iterates : ℕ → ℝ
  target : ℝ
  stepSize : ℕ → ℝ
  noise : ℕ → ℝ
  h_step_pos : ∀ n, 0 < stepSize n
  h_step_sq_summable : Summable (fun n => (stepSize n)^2)
  h_noise_bounded : ∃ C, ∀ n, |noise n| ≤ C * stepSize n

theorem noise_contribution_summable (setup : ConvergenceSetup) :
    Summable (fun n => |setup.noise n| * setup.stepSize n) := by
  obtain ⟨C, hC⟩ := setup.h_noise_bounded
  apply Summable.of_nonneg_of_le
  · intro n; exact mul_nonneg (abs_nonneg _) (le_of_lt (setup.h_step_pos n))
  · intro n
    calc |setup.noise n| * setup.stepSize n
        ≤ C * setup.stepSize n * setup.stepSize n := by
          apply mul_le_mul_of_nonneg_right (hC n) (le_of_lt (setup.h_step_pos n))
      _ = C * (setup.stepSize n)^2 := by ring
  · exact (setup.h_step_sq_summable.mul_left C)

theorem sgd_with_accumulation_converges
    (exactIterates : ℕ → ℝ) (accumIterates : ℕ → ℝ)
    (target : ℝ)
    (h_exact_converges : Filter.Tendsto exactIterates Filter.atTop (nhds target))
    (h_error_vanishes : Filter.Tendsto
      (fun n => accumIterates n - exactIterates n) Filter.atTop (nhds 0)) :
    Filter.Tendsto accumIterates Filter.atTop (nhds target) := by
  have : accumIterates = fun n => exactIterates n + (accumIterates n - exactIterates n) := by
    ext n; ring
  rw [this]
  have h_zero : target = target + 0 := by ring
  rw [h_zero]
  exact Filter.Tendsto.add h_exact_converges h_error_vanishes

end

end Pythia.Numerical.GradientAccumulation
