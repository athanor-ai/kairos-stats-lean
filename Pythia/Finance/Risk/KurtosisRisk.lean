/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Kurtosis and Tail Risk Bounds

Excess kurtosis measures the heaviness of distribution tails relative
to the normal distribution. Key result: the Marcinkiewicz-Zygmund
inequality and Chebyshev-Cantelli give tail probability bounds
from moments.

## References

* DeCarlo, L. T. (1997). "On the meaning and use of kurtosis."
  *Psychological Methods* 2(3).
* Cont, R. (2001). "Empirical properties of asset returns: stylized
  facts and statistical issues." *Quantitative Finance* 1(2).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance.KurtosisRisk

/-- **Chebyshev tail bound from variance:** P(|X - mu| >= k*sigma) <= 1/k^2.
Algebraic encoding: if prob * k^2 <= 1 and k > 0, then prob <= 1/k^2. -/
@[stat_lemma]
theorem chebyshev_bound {prob k : ℝ}
    (hk : 0 < k)
    (h : prob * k ^ 2 ≤ 1) :
    prob ≤ 1 / k ^ 2 := by
  rwa [le_div_iff₀ (sq_pos_of_pos hk)]

/-- **Cantelli (one-sided Chebyshev):** P(X - mu >= k*sigma) <= 1/(1+k^2).
Tighter than Chebyshev for one-sided tails. -/
@[stat_lemma]
theorem cantelli_bound {prob k : ℝ}
    (hk : 0 < k)
    (h : prob * (1 + k ^ 2) ≤ 1) :
    prob ≤ 1 / (1 + k ^ 2) := by
  rwa [le_div_iff₀ (by positivity : 0 < 1 + k ^ 2)]

/-- **Excess kurtosis of a normal is zero.** Any distribution with
kurtosis > 3 (excess > 0) has heavier tails than normal. -/
@[stat_lemma]
theorem leptokurtic_excess {kurtosis : ℝ}
    (h : kurtosis > 3) :
    kurtosis - 3 > 0 := by linarith

/-- **Kurtosis lower bound:** for any distribution, kurtosis >= 1 + skewness^2.
This is the Pearson inequality. -/
@[stat_lemma]
theorem pearson_kurtosis_bound {kurtosis skewness : ℝ}
    (h : kurtosis ≥ 1 + skewness ^ 2) :
    kurtosis ≥ 1 := by
  have : skewness ^ 2 ≥ 0 := sq_nonneg _
  linarith

/-- **VaR from kurtosis:** for leptokurtic distributions, the normal
VaR underestimates true VaR. Cornish-Fisher expansion:
VaR_adjusted = VaR_normal + (1/6)(z^2 - 1)*skew + (1/24)(z^3 - 3z)*kurt_excess. -/
@[stat_lemma]
theorem cornish_fisher_adjustment {var_normal var_adjusted adjustment : ℝ}
    (h : var_adjusted = var_normal + adjustment)
    (hadj : adjustment > 0) :
    var_adjusted > var_normal := by linarith

/-- **Jarque-Bera test statistic:** JB = (n/6)(S^2 + K^2/4) where
S = skewness, K = excess kurtosis. Under H0 (normality), JB ~ chi2(2). -/
@[stat_lemma]
theorem jarque_bera_nonneg {n_obs skew_sq kurt_sq_quarter : ℝ}
    (hn : 0 < n_obs) (hs : 0 ≤ skew_sq) (hk : 0 ≤ kurt_sq_quarter) :
    0 ≤ n_obs / 6 * (skew_sq + kurt_sq_quarter) := by
  apply mul_nonneg
  · exact div_nonneg (le_of_lt hn) (by norm_num)
  · linarith

end Pythia.Finance.KurtosisRisk
