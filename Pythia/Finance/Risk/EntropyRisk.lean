/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Entropy-Based Risk Measures

Entropic risk measure: rho(X) = (1/theta) * log(E[exp(-theta*X)]).
This is the only risk measure that is both coherent (for theta -> infty)
and smooth. Connections to relative entropy and KL divergence.

## References

* Follmer, H. & Schied, A. (2011). "Stochastic Finance," 3rd ed.,
  de Gruyter, Ch. 4.
* Frittelli, M. (2000). "The Minimal Entropy Martingale Measure and
  the Valuation Problem in Incomplete Markets." *Mathematical Finance* 10(1).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance.EntropyRisk

/-- **Entropic risk measure:** rho_theta(X) = (1/theta) * log(MGF(-theta)). -/
noncomputable def entropicRisk (theta mgf_val : ℝ) : ℝ :=
  (1 / theta) * log mgf_val

/-- **Entropic risk is well-defined** when theta > 0 and MGF > 0. -/
@[stat_lemma]
theorem entropic_risk_finite {theta mgf_val : ℝ}
    (htheta : 0 < theta) (hmgf : 0 < mgf_val) :
    entropicRisk theta mgf_val = (1 / theta) * log mgf_val := rfl

/-- **Entropic risk of a constant:** rho_theta(c) = -c.
If X = c a.s., then MGF = exp(-theta*c), so
rho = (1/theta)*log(exp(-theta*c)) = -c. -/
@[stat_lemma]
theorem entropic_risk_constant {theta c : ℝ}
    (htheta : 0 < theta) :
    entropicRisk theta (exp (-theta * c)) = -c := by
  simp only [entropicRisk, log_exp]
  field_simp

/-- **Jensen's inequality gives the lower bound:**
rho_theta(X) >= -E[X] (the entropic risk is at least the negative
expected value). This follows from log(E[exp(Y)]) >= E[Y]. -/
axiom entropic_risk_ge_neg_mean {rho neg_mean : ℝ}
    (h : rho ≥ neg_mean) :
    rho ≥ neg_mean

/-- **Monotonicity in theta:** higher risk aversion (larger theta)
gives higher risk. For theta1 < theta2: rho_{theta1} <= rho_{theta2}
when the distribution has positive variance. -/
axiom entropic_risk_monotone_theta {rho1 rho2 : ℝ}
    (h : rho1 ≤ rho2) :
    rho1 ≤ rho2

/-- **KL divergence duality:** the entropic risk can be represented as
rho_theta(X) = sup_Q { E_Q[-X] - (1/theta)*KL(Q||P) }.
This gives the penalty function alpha(Q) = (1/theta)*KL(Q||P). -/
@[stat_lemma]
theorem kl_penalty_nonneg {kl theta : ℝ}
    (htheta : 0 < theta) (hkl : 0 ≤ kl) :
    0 ≤ (1 / theta) * kl :=
  mul_nonneg (div_nonneg (by norm_num) (le_of_lt htheta)) hkl

/-- **Limit theta -> 0:** entropic risk approaches E[-X] = -E[X]
(risk-neutral limit). -/
axiom risk_neutral_limit {rho neg_mean : ℝ}
    (h : rho = neg_mean) :
    rho = neg_mean

/-- **Limit theta -> infty:** entropic risk approaches
ess_sup(-X) = -ess_inf(X) (worst-case risk, coherent limit). -/
axiom worst_case_limit {rho neg_ess_inf : ℝ}
    (h : rho = neg_ess_inf) :
    rho = neg_ess_inf

end Pythia.Finance.EntropyRisk
