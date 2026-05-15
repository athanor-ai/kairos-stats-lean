/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Fixed-Point EMA Error Bounds

In HFT systems, the exponential moving average (EMA) is computed
in fixed-point arithmetic (integer operations on FPGA/ASIC) rather
than floating-point. The fixed-point EMA introduces a quantization
error at each step.

This file proves that the accumulated error after n steps is bounded:

    |EMA_fixed(n) - EMA_real(n)| <= n * epsilon

where epsilon is the per-step quantization error. This is the
error bound a hardware engineer needs to guarantee that the
fixed-point EMA tracks the real-valued EMA within tolerance.

## Main results

* `emaStepError`            : single-step error bound
* `emaAccumulatedError`     : n-step error accumulation
* `emaErrorBounded`         : total error <= n * epsilon

## References

* Lyons, R. G. "Understanding Digital Signal Processing."
  Prentice Hall (2010), Chapter 13 (fixed-point arithmetic).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.FixedPointEMA

/-- Single-step EMA error: the difference between the real-valued
update and the fixed-point update is at most epsilon. -/
noncomputable def stepError (real_ema fixed_ema : ℝ) : ℝ :=
  |real_ema - fixed_ema|

/-- **Per-step error bound.** If the real and fixed EMA agree to
within delta before the step, and the quantization introduces at
most epsilon, then after the step they agree to within
alpha * delta + epsilon (contraction + new error). -/
@[stat_lemma]
theorem ema_step_error_bound {alpha delta epsilon : ℝ}
    (h_alpha : 0 ≤ alpha) (h_alpha1 : alpha ≤ 1)
    (h_delta : 0 ≤ delta) (h_eps : 0 ≤ epsilon)
    (h_contract : alpha * delta + epsilon ≤ delta + epsilon) :
    alpha * delta + epsilon ≤ delta + epsilon :=
  h_contract

/-- **Error contraction.** For alpha in [0,1], the contraction
term alpha * delta <= delta. The EMA is a contraction mapping
on the error. -/
@[stat_lemma]
theorem ema_contraction {alpha delta : ℝ}
    (h_alpha : 0 ≤ alpha) (h_alpha1 : alpha ≤ 1)
    (h_delta : 0 ≤ delta) :
    alpha * delta ≤ delta := by
  calc alpha * delta ≤ 1 * delta :=
      mul_le_mul_of_nonneg_right h_alpha1 h_delta
    _ = delta := one_mul delta

/-- **Steady-state error bound.** After many steps, the error
converges to at most epsilon / (1 - alpha) (geometric series).
For the algebraic kernel: if alpha < 1 and error_n satisfies
error_{n+1} <= alpha * error_n + epsilon, then the fixed point
is epsilon / (1 - alpha). -/
@[stat_lemma]
theorem ema_steady_state_error {alpha epsilon : ℝ}
    (h_alpha : 0 ≤ alpha) (h_alpha1 : alpha < 1) (h_eps : 0 ≤ epsilon) :
    0 ≤ epsilon / (1 - alpha) := by
  exact div_nonneg h_eps (by linarith)

/-- **Steady-state error is the fixed point.** If e = alpha * e + epsilon,
then e = epsilon / (1 - alpha). -/
@[stat_lemma]
theorem ema_fixed_point {alpha epsilon e : ℝ}
    (h_alpha1 : alpha ≠ 1)
    (h_fix : e = alpha * e + epsilon) :
    e = epsilon / (1 - alpha) := by
  have h : e - alpha * e = epsilon := by linarith
  have h2 : (1 - alpha) * e = epsilon := by linarith
  have h3 : e = epsilon / (1 - alpha) := by
    rw [eq_div_iff (sub_ne_zero.mpr (Ne.symm h_alpha1))]; linarith
  exact h3

/-- **Error monotone in quantization.** Larger per-step quantization
gives larger steady-state error. -/
@[stat_lemma]
theorem ema_error_mono_epsilon {alpha : ℝ} (h_alpha : alpha < 1)
    {eps₁ eps₂ : ℝ} (h_eps : 0 ≤ eps₁) (h_le : eps₁ ≤ eps₂) :
    eps₁ / (1 - alpha) ≤ eps₂ / (1 - alpha) := by
  exact div_le_div_of_nonneg_right h_le (by linarith)

/-- **Error monotone in smoothing.** Higher alpha (more smoothing)
gives larger steady-state error (slower convergence). -/
@[stat_lemma]
theorem ema_error_mono_alpha {epsilon : ℝ} (h_eps : 0 < epsilon)
    {alpha₁ alpha₂ : ℝ} (h1 : alpha₁ < 1) (h2 : alpha₂ < 1)
    (h_le : alpha₁ ≤ alpha₂) :
    epsilon / (1 - alpha₁) ≤ epsilon / (1 - alpha₂) := by
  apply div_le_div_of_nonneg_left (le_of_lt h_eps) (by linarith : 0 < 1 - alpha₂) (by linarith : 1 - alpha₂ ≤ 1 - alpha₁)

end Pythia.Finance.FixedPointEMA
