/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Geometric Brownian Motion — Closed-Form Terminal Value

For a geometric Brownian motion with initial value `S₀`, drift `μ`,
volatility `σ`, time horizon `T`, and Brownian-sample value `w`
(representing one realisation of `W_T`), the closed-form terminal
value is

    S(S₀, μ, σ, T, w) = S₀ · exp((μ - σ²/2) · T + σ · w).

This is the explicit solution to the SDE `dS = μ S dt + σ S dW`.
The probabilistic/SDE link is *not* established in this file
(requires Itô-calculus machinery, deferred to a hard-tier file);
this module surfaces the algebraic closed form and its boundary /
sign / log-relation properties.

## Main results

* `gbmTerminal`                  : closed-form terminal value
* `gbmTerminal_pos`              : `0 < gbmTerminal` when `0 < S₀`
* `gbmTerminal_zero_time`        : `gbmTerminal S₀ μ σ 0 0 = S₀`
* `log_gbmTerminal`              : closed-form log relation
  `log(gbmTerminal S₀ μ σ T w) = log S₀ + (μ - σ²/2)·T + σ·w` for `0 < S₀`

## Why this lemma

Mathlib has `Real.exp_pos`, `Real.exp_zero`, `Real.log_mul`,
`Real.log_exp`, but no named `geometric_brownian_motion` declaration.
Pythia surfaces the algebraic GBM closed form so the `pythia` tactic
cascade can close terminal-value goals (Monte-Carlo simulation
sanity-checks, log-normality identities, no-arbitrage forward-price
matching) without re-deriving the closed form.

## References

* Black, F. and Scholes, M.
  "The Pricing of Options and Corporate Liabilities."
  *Journal of Political Economy* 81(3): 637-654 (1973).
  (Closed-form GBM dynamics under risk-neutral measure.)
* Hull, J. C. *Options, Futures, and Other Derivatives*, 10th ed.
  Pearson (2017), §14.6 (lognormal property of GBM).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- Closed-form terminal value of a geometric Brownian motion:

    S(S₀, μ, σ, T, w) = S₀ · exp((μ - σ²/2) · T + σ · w).

`w` is a real parameter representing the Brownian sample `W_T`.
This file does **not** establish the SDE link
(`dS = μ S dt + σ S dW`); that requires Itô calculus and lives in
a separate hard-tier module.  Here we surface the closed form for
algebraic reasoning. -/
noncomputable def gbmTerminal (S₀ μ σ T w : ℝ) : ℝ :=
  S₀ * Real.exp ((μ - σ^2 / 2) * T + σ * w)

/-- **Positivity.** For positive initial value, the GBM terminal is
strictly positive at any drift, volatility, horizon, and Brownian
sample.  This is the classical "GBM stays positive almost surely"
property in its algebraic form. -/
@[stat_lemma]
theorem gbmTerminal_pos {S₀ : ℝ} (hS₀ : 0 < S₀) (μ σ T w : ℝ) :
    0 < gbmTerminal S₀ μ σ T w := by
  unfold gbmTerminal; exact mul_pos hS₀ (Real.exp_pos _)

/-- **Boundary at `T = 0`, `w = 0`.** At zero horizon with zero
Brownian sample, the terminal value equals the initial value:
`gbmTerminal S₀ μ σ 0 0 = S₀`. -/
@[stat_lemma]
theorem gbmTerminal_zero_time (S₀ μ σ : ℝ) :
    gbmTerminal S₀ μ σ 0 0 = S₀ := by
  unfold gbmTerminal; simp [mul_zero, Real.exp_zero, mul_one]

/-- **Log-linear relation.** For positive initial value,

    log(gbmTerminal S₀ μ σ T w) = log S₀ + (μ - σ²/2)·T + σ·w.

This is the algebraic kernel of the GBM log-normality property
(`log S_T` is affine in `T` and `W_T`). -/
@[stat_lemma]
theorem log_gbmTerminal {S₀ : ℝ} (hS₀ : 0 < S₀) (μ σ T w : ℝ) :
    Real.log (gbmTerminal S₀ μ σ T w) =
      Real.log S₀ + ((μ - σ^2 / 2) * T + σ * w) := by
  unfold gbmTerminal
  rw [Real.log_mul hS₀.ne' (Real.exp_pos _).ne', Real.log_exp]

end Pythia.Finance
