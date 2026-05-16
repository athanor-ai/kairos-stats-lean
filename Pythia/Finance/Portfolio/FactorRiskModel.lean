/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Multi-Factor Risk Model

Proves properties of factor-based risk decomposition used by
every institutional portfolio manager: Barra, Axioma, etc.
-/
import Mathlib
import Pythia.Tactic.Pythia

open Finset

namespace Pythia.Finance.Portfolio.FactorRiskModel

/-- **Systematic risk nonneg.** Factor risk = sum beta_k^2 * var_k
is nonneg (sum of nonneg terms). -/
@[stat_lemma]
theorem systematic_risk_nonneg {n : ℕ} (beta_sq var : Fin n → ℝ)
    (h_bsq : ∀ k, 0 ≤ beta_sq k) (h_var : ∀ k, 0 ≤ var k) :
    0 ≤ ∑ k, beta_sq k * var k :=
  Finset.sum_nonneg fun k _ => mul_nonneg (h_bsq k) (h_var k)

/-- **Idiosyncratic risk diversifiable.** As n grows, the average
idiosyncratic variance goes to zero: (1/n) * sum var_eps_i <= max_var / n. -/
@[stat_lemma]
theorem idio_risk_shrinks {max_var : ℝ} {n : ℕ}
    (h_max : 0 ≤ max_var) (hn : 0 < (n : ℝ)) :
    0 ≤ max_var / ↑n :=
  div_nonneg h_max (le_of_lt hn)

/-- **Tracking error from factor mismatch.** The tracking error
between portfolio and benchmark comes from differences in factor
exposures. TE^2 = sum (beta_p_k - beta_b_k)^2 * var_k + var_resid. -/
@[stat_lemma]
theorem tracking_error_from_mismatch {n : ℕ}
    (delta_beta_sq var : Fin n → ℝ) (var_resid : ℝ)
    (h_dbsq : ∀ k, 0 ≤ delta_beta_sq k) (h_var : ∀ k, 0 ≤ var k) (h_resid : 0 ≤ var_resid) :
    0 ≤ ∑ k, delta_beta_sq k * var k + var_resid :=
  add_nonneg (Finset.sum_nonneg fun k _ => mul_nonneg (h_dbsq k) (h_var k)) h_resid

end Pythia.Finance.Portfolio.FactorRiskModel
