/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Merton Jump-Diffusion Model (algebraic identities)

In Merton's model, the stock price follows
dS/S = (mu - lambda*kappa) dt + sigma dW + J dN
where N is a Poisson process and J is log-normal jump size.

## References

* Merton, R. C. (1976). "Option pricing when underlying stock returns
  are discontinuous." *Journal of Financial Economics* 3(1-2).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance.MertonJumpDiffusion

/-- Compensated drift: the risk-neutral drift under jump diffusion
is mu - lambda * kappa where kappa = E[J] - 1 is the expected
percentage jump. -/
@[stat_lemma]
theorem compensated_drift {mu lam kappa drift : ℝ}
    (h : drift = mu - lam * kappa) :
    mu - drift = lam * kappa := by linarith

/-- Total variance over [0,T]: sigma^2 * T + lambda * T * (delta^2 + kappa^2)
where delta is jump volatility. -/
@[stat_lemma]
theorem total_variance {sigma_sq delta_sq kappa_sq lam T total_var : ℝ}
    (hT : 0 ≤ T)
    (h : total_var = sigma_sq * T + lam * T * (delta_sq + kappa_sq))
    (hsig : 0 ≤ sigma_sq) (hdel : 0 ≤ delta_sq) (hkap : 0 ≤ kappa_sq)
    (hlam : 0 ≤ lam) :
    0 ≤ total_var := by
  rw [h]; nlinarith [mul_nonneg hsig hT, mul_nonneg hlam hT, add_nonneg hdel hkap]

/-- Poisson probability: P(N(T) = n) = (lambda*T)^n * exp(-lambda*T) / n!.
For n=0 (no jumps), the price reduces to Black-Scholes. -/
@[stat_lemma]
theorem no_jump_probability {lam T p0 : ℝ}
    (hlam : 0 ≤ lam) (hT : 0 ≤ T)
    (h : p0 = exp (-(lam * T))) :
    0 < p0 := by
  rw [h]; exact exp_pos _

/-- Jump-adjusted volatility for the n-th term:
sigma_n^2 = sigma^2 + n * delta^2 / T. -/
@[stat_lemma]
theorem jump_adjusted_vol {sigma_sq delta_sq T sigma_n_sq : ℝ} {n : ℕ}
    (hT : 0 < T) (hsig : 0 ≤ sigma_sq) (hdel : 0 ≤ delta_sq)
    (h : sigma_n_sq = sigma_sq + n * delta_sq / T) :
    sigma_sq ≤ sigma_n_sq := by
  rw [h]; linarith [div_nonneg (mul_nonneg (Nat.cast_nonneg' n (α := ℝ)) hdel) (le_of_lt hT)]

end Pythia.Finance.MertonJumpDiffusion
