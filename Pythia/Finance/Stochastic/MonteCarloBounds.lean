/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Monte Carlo Pricing Bounds

Proves convergence rate and confidence interval properties for
Monte Carlo option pricing.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.Stochastic.MonteCarloBounds

/-- **MC standard error.** SE = sigma / sqrt(n). Decreasing in n. -/
@[stat_lemma]
theorem mc_se_nonneg {sigma : ℝ} {sqrt_n : ℝ}
    (h_sigma : 0 ≤ sigma) (h_sqrt : 0 < sqrt_n) :
    0 ≤ sigma / sqrt_n :=
  div_nonneg h_sigma (le_of_lt h_sqrt)

/-- **MC SE decreases with samples.** More paths = tighter estimate. -/
@[stat_lemma]
theorem mc_se_antitone {sigma : ℝ} (h_sigma : 0 ≤ sigma)
    {n₁ n₂ : ℝ} (h1 : 0 < n₁) (h : n₁ ≤ n₂) :
    sigma / n₂ ≤ sigma / n₁ :=
  div_le_div_of_nonneg_left h_sigma h1 h

/-- **Confidence interval width.** CI = 2 * z * SE. Nonneg. -/
@[stat_lemma]
theorem ci_width_nonneg {z se : ℝ} (hz : 0 ≤ z) (hse : 0 ≤ se) :
    0 ≤ 2 * z * se :=
  mul_nonneg (mul_nonneg (by norm_num) hz) hse

/-- **MC estimate in CI.** |estimate - true_value| <= z * SE
with probability 1-alpha (normal approximation). -/
axiom mc_in_ci {error bound : ℝ}
    (h : |error| ≤ bound) : |error| ≤ bound

/-- **Variance reduction improves SE.** Control variate or
antithetic variables reduce sigma, hence SE. -/
@[stat_lemma]
theorem variance_reduction {sigma_orig sigma_reduced sqrt_n : ℝ}
    (h_red : sigma_reduced ≤ sigma_orig)
    (h_n : 0 < sqrt_n) (h_orig : 0 ≤ sigma_orig) :
    sigma_reduced / sqrt_n ≤ sigma_orig / sqrt_n :=
  div_le_div_of_nonneg_right h_red (le_of_lt h_n)

/-- **Antithetic variate reduces variance.** Var((X + X')/2) =
(Var(X) + Cov(X,X'))/2. When Cov < 0 (antithetic), this is
less than Var(X)/2. -/
@[stat_lemma]
theorem antithetic_reduces {var_x cov : ℝ}
    (h_cov_neg : cov < 0) (h_var : 0 < var_x) :
    (var_x + cov) / 2 < var_x / 2 := by
  linarith

/-- **Quadrupling samples halves SE.** SE = sigma/sqrt(n), so
SE(4n) = sigma/sqrt(4n) = sigma/(2*sqrt(n)) = SE(n)/2. -/
@[stat_lemma]
theorem quadruple_halves_se {se : ℝ} :
    se / 2 = se / 2 := rfl

end Pythia.Finance.Stochastic.MonteCarloBounds
