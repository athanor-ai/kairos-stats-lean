/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Risk Parity Optimality

Inverse-vol weighting equalizes marginal risk contributions.

## References

* Maillard, Roncalli, Teiletche (2010). J. Portfolio Management.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.Portfolio.RiskParityOptimal

noncomputable def inverseVolWeight (sigma1 sigma2 : ℝ) : ℝ :=
  sigma2 / (sigma1 + sigma2)

@[stat_lemma]
theorem inverseVolWeights_sum {sigma1 sigma2 : ℝ}
    (h : sigma1 + sigma2 ≠ 0) :
    inverseVolWeight sigma1 sigma2 + inverseVolWeight sigma2 sigma1 = 1 := by
  unfold inverseVolWeight
  have h_ne -- TAUTOLOGICAL: hypothesis restate, needs real proof
  := h
  field_simp [h_ne, show sigma2 + sigma1 ≠ 0 from by rwa [add_comm]]
  ring

@[stat_lemma]
theorem riskContribution_equal {sigma1 sigma2 : ℝ}
    (h : sigma1 + sigma2 ≠ 0) :
    inverseVolWeight sigma1 sigma2 * sigma1 =
      inverseVolWeight sigma2 sigma1 * sigma2 := by
  unfold inverseVolWeight
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  congr 1
  · ring
  · ring

@[stat_lemma]
theorem inverseVolWeight_nonneg {sigma1 sigma2 : ℝ}
    (h1 : 0 ≤ sigma1) (h2 : 0 ≤ sigma2) :
    0 ≤ inverseVolWeight sigma1 sigma2 :=
  div_nonneg h2 (by linarith)

@[stat_lemma]
theorem inverseVolWeight_le_one {sigma1 sigma2 : ℝ}
    (h1 : 0 ≤ sigma1) (h2 : 0 < sigma2) :
    inverseVolWeight sigma1 sigma2 ≤ 1 := by
  unfold inverseVolWeight
  rw [div_le_one (by linarith)]; linarith

@[stat_lemma]
theorem more_volatile_less_weight {sigma1 sigma2 : ℝ}
    (h1 : 0 < sigma1) (h2 : 0 < sigma2) (h : sigma2 < sigma1) :
    inverseVolWeight sigma1 sigma2 < inverseVolWeight sigma2 sigma1 := by
  unfold inverseVolWeight
  have hd : (0 : ℝ) < sigma1 + sigma2 := by linarith
  rw [div_lt_div_iff₀ hd (by linarith : 0 < sigma2 + sigma1)]
  nlinarith

end Pythia.Finance.Portfolio.RiskParityOptimal
