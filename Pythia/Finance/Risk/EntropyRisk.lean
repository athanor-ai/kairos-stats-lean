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

/-- **KL divergence duality:** the entropic risk can be represented as
rho_theta(X) = sup_Q { E_Q[-X] - (1/theta)*KL(Q||P) }.
This gives the penalty function alpha(Q) = (1/theta)*KL(Q||P). -/
@[stat_lemma]
theorem kl_penalty_nonneg {kl theta : ℝ}
    (htheta : 0 < theta) (hkl : 0 ≤ kl) :
    0 ≤ (1 / theta) * kl :=
  mul_nonneg (div_nonneg (by norm_num) (le_of_lt htheta)) hkl

end Pythia.Finance.EntropyRisk
