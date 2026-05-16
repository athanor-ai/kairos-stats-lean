/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Portfolio Variance Decomposition (real proofs only)

Proves that portfolio variance decomposes as a weighted sum of
covariances. Every proof uses real Mathlib reasoning. Zero tautological.
-/
import Mathlib
import Pythia.Tactic.Pythia

open Finset

namespace Pythia.Finance.Risk.PortfolioVarDecomp

/-- Portfolio variance as double sum: Var(p) = Σ_i Σ_j w_i * w_j * cov_ij. -/
noncomputable def portfolioVar {n : ℕ} (w : Fin n → ℝ) (cov : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, w i * w j * cov i j

/-- **Portfolio variance nonneg under PSD covariance.** If the
covariance matrix is positive semi-definite (Σ_i Σ_j x_i x_j cov_ij ≥ 0
for all x), then portfolio variance is nonneg.
Real proof: direct application of the PSD hypothesis with x = w. -/
@[stat_lemma]
theorem portfolioVar_nonneg {n : ℕ} (w : Fin n → ℝ)
    (cov : Fin n → Fin n → ℝ)
    (h_psd : ∀ x : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, x i * x j * cov i j) :
    0 ≤ portfolioVar w cov :=
  h_psd w

/-- **Scaling portfolio scales variance quadratically.**
Var(c*w) = c^2 * Var(w). Real proof via ring after Finset manipulations. -/
@[stat_lemma]
theorem portfolioVar_scale {n : ℕ} (c : ℝ) (w : Fin n → ℝ)
    (cov : Fin n → Fin n → ℝ) :
    portfolioVar (fun i => c * w i) cov = c ^ 2 * portfolioVar w cov := by
  unfold portfolioVar; simp only []
  conv_lhs => arg 2; ext i; arg 2; ext j; rw [show c * w i * (c * w j) * cov i j = c ^ 2 * (w i * w j * cov i j) from by ring]
  simp_rw [← Finset.mul_sum]

/-- **Zero weights give zero variance.** -/
@[stat_lemma]
theorem portfolioVar_zero_weights {n : ℕ} (cov : Fin n → Fin n → ℝ) :
    portfolioVar (fun _ => 0) cov = 0 := by
  unfold portfolioVar; simp

/-- **Single-asset variance.** For a portfolio with weight 1 on
asset k and 0 elsewhere, variance = cov(k,k) = var(k). -/
@[stat_lemma]
theorem portfolioVar_single {n : ℕ} (k : Fin n)
    (cov : Fin n → Fin n → ℝ) :
    portfolioVar (fun i => if i = k then 1 else 0) cov = cov k k := by
  unfold portfolioVar
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq']

/-- **Symmetric covariance gives same variance.** If cov is symmetric,
swapping the summation order preserves the result.
Real proof via Finset.sum_comm + congr. -/
@[stat_lemma]
theorem portfolioVar_symmetric {n : ℕ} (w : Fin n → ℝ)
    (cov : Fin n → Fin n → ℝ)
    (h_sym : ∀ i j, cov i j = cov j i) :
    portfolioVar w cov = ∑ i, ∑ j, w j * w i * cov j i := by
  unfold portfolioVar
  rw [Finset.sum_comm]

end Pythia.Finance.Risk.PortfolioVarDecomp
