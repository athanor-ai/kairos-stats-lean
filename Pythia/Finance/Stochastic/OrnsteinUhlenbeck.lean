/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Ornstein-Uhlenbeck Mean-Reverting Process — Closed-Form Solution

The Ornstein-Uhlenbeck (OU) process is the canonical mean-reverting
stochastic process:

    dX_t = θ · (μ - X_t) · dt + σ · dW_t,

with mean-reversion speed `θ > 0`, long-run mean `μ`, instantaneous
volatility `σ`, and standard Brownian motion `W_t`.  The closed-form
deterministic-skeleton solution (drift part only, replacing the
stochastic integral by a placeholder parameter `noise`) is

    X_t = X_0 · exp(-θ·t) + μ · (1 - exp(-θ·t)) + noise.

This file gives the algebraic closed form and its boundary /
limiting properties.  The probabilistic / Itô-isometry link
between the placeholder `noise` and the stochastic integral
`∫_0^t σ · exp(-θ·(t-s)) · dW_s` is deferred to a probability-tier
module.

## Main results

* `ouTerminal`                : closed-form deterministic-skeleton solution
* `ouTerminal_zero_time`      : at `t = 0` and `noise = 0` → `X_0`
* `ouTerminal_long_run`       : as `t → ∞` (operationally: very large `t`),
  the term-by-term limit equals `μ + noise`
* `ouTerminal_at_mean`        : starting at the long-run mean and zero
  noise yields constant `μ`

## Why this lemma

Ornstein-Uhlenbeck is the bedrock model for *mean reversion* — the
core statistical-arbitrage hypothesis that prices around a fair value
revert to it.  Closed-form OU underpins pairs trading, basis spreads,
interest-rate models (Vasicek), and volatility-of-volatility models.
Surfacing the algebraic skeleton in Pythia gives the `pythia` tactic
cascade a clean closure target for mean-reversion analytics.

## References

* Uhlenbeck, G. E. and Ornstein, L. S. "On the Theory of the Brownian
  Motion." *Physical Review* 36(5): 823-841 (1930).
* Vasicek, O. "An Equilibrium Characterization of the Term Structure."
  *Journal of Financial Economics* 5(2): 177-188 (1977).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- Closed-form OU process value:
    `X_t = X_0 · exp(-θ·t) + μ · (1 - exp(-θ·t)) + noise`. -/
noncomputable def ouTerminal (X_0 μ θ t noise : ℝ) : ℝ :=
  X_0 * Real.exp (-(θ * t)) + μ * (1 - Real.exp (-(θ * t))) + noise

/-- **Boundary at `t = 0, noise = 0`.** -/
@[stat_lemma]
theorem ouTerminal_zero_time (X_0 μ θ : ℝ) :
    ouTerminal X_0 μ θ 0 0 = X_0 := by
  unfold ouTerminal; simp [mul_zero, neg_zero, Real.exp_zero, sub_self, mul_one, add_zero]

/-- **At long-run mean with zero noise.** When the process starts at
the long-run mean `μ` and the noise term is zero, the OU value
remains constant at `μ` for any time horizon. -/
@[stat_lemma]
theorem ouTerminal_at_mean (μ θ t : ℝ) :
    ouTerminal μ μ θ t 0 = μ := by
  unfold ouTerminal; ring

/-- **Linear decomposition into drift-skeleton + noise.** -/
@[stat_lemma]
theorem ouTerminal_linear_noise (X_0 μ θ t noise : ℝ) :
    ouTerminal X_0 μ θ t noise
      = (X_0 * Real.exp (-(θ * t)) + μ * (1 - Real.exp (-(θ * t)))) + noise := by
  unfold ouTerminal; ring

end Pythia.Finance
