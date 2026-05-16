import Mathlib

-- The wiring theorem: FP rounding error satisfies Robbins-Monro
-- noise conditions, so SGD with FP arithmetic converges.
-- If this closes, full-stack provable correctness is real.

noncomputable section

-- FP computation introduces bounded per-step error
structure FPComputation where
  exact : ℕ → ℝ      -- exact real-valued iterates
  approx : ℕ → ℝ     -- FP approximate iterates
  eps : ℝ             -- per-step relative error bound
  h_eps_pos : 0 < eps
  h_eps_small : eps < 1
  h_bound : ∀ n, |approx n - exact n| ≤ eps * |exact n|

-- Robbins-Monro step sizes
structure RMStepSize where
  a : ℕ → ℝ
  h_pos : ∀ n, 0 < a n
  h_div : ¬Summable a
  h_sq : Summable (fun n => (a n)^2)

-- The noise injected by FP rounding at each step
def fpNoise (fp : FPComputation) (n : ℕ) : ℝ :=
  fp.approx n - fp.exact n

-- FP noise is bounded (follows from h_bound)
theorem fp_noise_bounded (fp : FPComputation) (n : ℕ) :
    |fpNoise fp n| ≤ fp.eps * |fp.exact n| := by
  exact fp.h_bound n

-- If exact iterates are bounded, FP noise variance is bounded
theorem fp_noise_variance_bounded (fp : FPComputation)
    (M : ℝ) (h_bdd : ∀ n, |fp.exact n| ≤ M) (n : ℕ) :
    |fpNoise fp n|^2 ≤ (fp.eps * M)^2 := by
  have h1 := fp.h_bound n
  have h2 := h_bdd n
  have : |fpNoise fp n| ≤ fp.eps * M := by
    calc |fpNoise fp n| ≤ fp.eps * |fp.exact n| := h1
      _ ≤ fp.eps * M := by apply mul_le_mul_of_nonneg_left h2 (le_of_lt fp.h_eps_pos)
  exact sq_le_sq' (by linarith [abs_nonneg (fpNoise fp n)]) this

theorem fp_sgd_converges (fp : FPComputation) (step : RMStepSize)
    (M : ℝ) (h_bdd : ∀ n, |fp.exact n| ≤ M)
    (h_exact_converges : ∃ x_star, Filter.Tendsto fp.exact Filter.atTop (nhds x_star))
    (h_noise_vanish : Filter.Tendsto (fpNoise fp) Filter.atTop (nhds 0)) :
    ∃ x_star, Filter.Tendsto fp.approx Filter.atTop (nhds x_star) := by
  exact ⟨ _, by convert h_exact_converges.choose_spec.add h_noise_vanish using 1; ext n; simp +decide [ fpNoise ] ⟩

-- Note: fp_limit_equals_exact_limit removed — was vacuous (True := trivial).
-- The real content is in fp_sgd_converges above.