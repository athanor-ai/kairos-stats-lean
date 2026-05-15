/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Mean-Variance Utility (Markowitz 1952)

The *mean-variance utility* for an investor with risk aversion
parameter `gamma > 0` is

    U(mu, sigma_sq) = mu - (gamma / 2) * sigma_sq,

where `mu` is the expected portfolio return and `sigma_sq` is the
return variance.  This quadratic-utility representation is exact
under normally distributed returns (where expected utility of a
CARA investor collapses to the mean-variance form) and is the
standard working approximation in portfolio construction under
any distribution once the mean and variance are the only moments
that matter to the investor.

## Main results

* `mvUtility`                                      : `mu - (gamma / 2) * sigma_sq`
* `mvUtility_zero_variance`                        : zero variance recovers the mean
* `mvUtility_le_mean`                              : utility is at most the mean
* `mvUtility_mono_return`                          : utility is monotone in expected return
* `mvUtility_antitone_variance`                    : utility is antitone in variance
* `mvUtility_antitone_risk_aversion`               : utility is antitone in risk aversion
* `mvUtility_eq_mean_iff_zero_variance_or_zero_gamma` : utility equals mean iff the
  risk-penalty term vanishes

## Why these lemmas

Mean-variance utility is the algebraic core of Modern Portfolio
Theory.  Every Markowitz-efficient-frontier computation, CAPM
derivation, and Black-Litterman tilting step rests on this functional
form.  Surfacing the sign, monotonicity, and zero-penalty identities
in Pythia gives the `pythia` tactic cascade clean closure targets for
utility-comparison, portfolio-selection, and optimality-condition goals.

## References

* Markowitz, H. "Portfolio Selection."
  *Journal of Finance* 7(1): 77-91 (1952).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Mean-variance utility for an investor with risk aversion
    parameter `gamma`:
    `U(mu, sigma_sq) = mu - (gamma / 2) * sigma_sq`. -/
noncomputable def mvUtility (gamma mu sigma_sq : ℝ) : ℝ :=
  mu - (gamma / 2) * sigma_sq

/-- **Zero-variance specialisation.** When return variance is zero,
mean-variance utility equals the expected return exactly — no
risk penalty is applied. -/
@[stat_lemma]
theorem mvUtility_zero_variance (gamma mu : ℝ) :
    mvUtility gamma mu 0 = mu := by
  unfold mvUtility; ring

/-- **Utility bounded above by the mean.** For strictly positive risk
aversion `gamma > 0` and non-negative variance `sigma_sq >= 0`, the
mean-variance utility is at most the expected return — the risk
penalty can only reduce utility below the mean. -/
@[stat_lemma]
theorem mvUtility_le_mean {gamma mu sigma_sq : ℝ}
    (hgamma : 0 < gamma) (hsigma : 0 ≤ sigma_sq) :
    mvUtility gamma mu sigma_sq ≤ mu := by
  unfold mvUtility
  apply sub_le_self
  exact mul_nonneg (div_nonneg hgamma.le (by norm_num)) hsigma

/-- **Monotone in expected return.** For fixed risk aversion and
variance, mean-variance utility is monotone non-decreasing in the
expected return `mu` — higher expected return always increases utility. -/
@[stat_lemma]
theorem mvUtility_mono_return {gamma sigma_sq : ℝ}
    {mu1 mu2 : ℝ} (h : mu1 ≤ mu2) :
    mvUtility gamma mu1 sigma_sq ≤ mvUtility gamma mu2 sigma_sq := by
  unfold mvUtility
  exact sub_le_sub_right h _

/-- **Antitone in variance.** For fixed positive risk aversion and
expected return, mean-variance utility is antitone in variance —
higher variance lowers utility. -/
@[stat_lemma]
theorem mvUtility_antitone_variance {gamma mu : ℝ} (hgamma : 0 < gamma)
    {sigma_sq1 sigma_sq2 : ℝ} (h : sigma_sq1 ≤ sigma_sq2) :
    mvUtility gamma mu sigma_sq2 ≤ mvUtility gamma mu sigma_sq1 := by
  unfold mvUtility
  apply sub_le_sub_left
  exact mul_le_mul_of_nonneg_left h (div_nonneg hgamma.le (by norm_num))

/-- **Antitone in risk aversion.** For fixed expected return and
non-negative variance, mean-variance utility is antitone in the risk
aversion parameter `gamma` — a more risk-averse investor assigns
lower utility to any risky position. -/
@[stat_lemma]
theorem mvUtility_antitone_risk_aversion {mu sigma_sq : ℝ} (hsigma : 0 ≤ sigma_sq)
    {gamma1 gamma2 : ℝ} (h : gamma1 ≤ gamma2) :
    mvUtility gamma2 mu sigma_sq ≤ mvUtility gamma1 mu sigma_sq := by
  unfold mvUtility
  apply sub_le_sub_left
  apply mul_le_mul_of_nonneg_right _ hsigma
  exact div_le_div_of_nonneg_right h (by norm_num)

/-- **Utility equals mean iff risk penalty vanishes.** Mean-variance
utility equals the expected return if and only if the product
`gamma * sigma_sq = 0`, which holds precisely when the investor is
risk-neutral (`gamma = 0`) or the portfolio has zero variance
(`sigma_sq = 0`). -/
@[stat_lemma]
theorem mvUtility_eq_mean_iff_zero_variance_or_zero_gamma
    (gamma mu sigma_sq : ℝ) :
    mvUtility gamma mu sigma_sq = mu ↔ gamma * sigma_sq = 0 := by
  unfold mvUtility
  -- Reduce to: mu - (gamma / 2) * sigma_sq = mu ↔ gamma * sigma_sq = 0.
  -- Note (gamma / 2) * sigma_sq = gamma * sigma_sq / 2, and dividing by 2
  -- is a bijection on ℝ, so both sides vanish simultaneously.
  constructor
  · intro h
    -- mu - (gamma / 2) * sigma_sq = mu implies (gamma / 2) * sigma_sq = 0.
    have h1 : (gamma / 2) * sigma_sq = 0 := by linarith
    -- (gamma / 2) * sigma_sq = (1/2) * (gamma * sigma_sq); since 1/2 ≠ 0, gamma*sigma_sq = 0.
    have h2 : (1 / 2 : ℝ) * (gamma * sigma_sq) = 0 := by linarith [show (gamma / 2) * sigma_sq = (1 / 2) * (gamma * sigma_sq) by ring]
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  · intro h
    -- gamma * sigma_sq = 0 implies (gamma / 2) * sigma_sq = 0.
    have h1 : (gamma / 2) * sigma_sq = 0 := by
      have : (gamma / 2) * sigma_sq = (1 / 2) * (gamma * sigma_sq) := by ring
      rw [this, h, mul_zero]
    linarith

end Pythia.Finance
