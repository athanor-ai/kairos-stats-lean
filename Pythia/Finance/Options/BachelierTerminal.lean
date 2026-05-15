/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bachelier Model: Arithmetic-Brownian-Motion Terminal Value

The Bachelier (1900) model for asset prices uses *arithmetic*
Brownian motion `dS = μ dt + σ dW` (linear drift + additive noise),
in contrast to the *geometric* Brownian motion `dS = μ S dt + σ S dW`
of the Black-Scholes model.  The closed-form terminal value is

    S_T = S₀ + μ · T + σ · w,

where `w` is the Brownian sample (representing one realisation of
`W_T`).  This file gives the algebraic closed form, treating `w` as
an unconstrained real parameter (the stochastic-integral / variance
link is deferred to a probability-tier module).

The Bachelier model is the practitioner-standard for *interest-rate
options* (where negative rates are legal and log-normal modelling
breaks) and *short-horizon equity quoting* (where linear-in-noise
is a reasonable local approximation).  Its closed form differs from
GBM in one critical way: `S_T` can be negative.

## Main results

* `bachelierTerminal`              : `S₀ + μ · T + σ · w`
* `bachelierTerminal_zero_time`    : at `T = 0` and `w = 0` → `S₀`
* `bachelierTerminal_linear_drift` : linear shift on `μ` translates `T`-scaled
* `bachelierTerminal_linear_noise` : linear shift on `w` translates `σ`-scaled

## Why this lemma

Bachelier is the right baseline for *negative-rate* fixed-income
options (post-2008 sovereign debt, SOFR options) where the log-normal
Black-Scholes framework fails by construction.  Surfacing the
algebraic Bachelier closed form in Pythia gives the `pythia` tactic
cascade a clean closure target for short-rate-option / negative-rate
analytics.

## References

* Bachelier, L. "Théorie de la spéculation."
  *Annales scientifiques de l'École Normale Supérieure* 17:
  21-86 (1900).
* Schachermayer, W. and Teichmann, J.
  "How Close Are the Option Pricing Formulas of Bachelier and
   Black-Merton-Scholes?"
  *Mathematical Finance* 18(1): 155-170 (2008).
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Finance

/-- Closed-form Bachelier (arithmetic-BM) terminal value:
    `S_T = S₀ + μ · T + σ · w`.

`w` is a real parameter representing the Brownian sample `W_T`.
Unlike GBM, the Bachelier process can take negative values — this
is by design (interest-rate options in negative-rate regimes). -/
noncomputable def bachelierTerminal (S₀ μ σ T w : ℝ) : ℝ :=
  S₀ + μ * T + σ * w

/-- **Boundary at `T = 0, w = 0`.** -/
@[stat_lemma]
theorem bachelierTerminal_zero_time (S₀ μ σ : ℝ) :
    bachelierTerminal S₀ μ σ 0 0 = S₀ := by
  unfold bachelierTerminal; ring

/-- **Linear in drift.** Shifting the drift `μ` by `Δμ` shifts the
terminal value by `Δμ · T`. -/
@[stat_lemma]
theorem bachelierTerminal_linear_drift (S₀ μ Δμ σ T w : ℝ) :
    bachelierTerminal S₀ (μ + Δμ) σ T w
      = bachelierTerminal S₀ μ σ T w + Δμ * T := by
  unfold bachelierTerminal; ring

/-- **Linear in Brownian sample.** Shifting `w` by `Δw` shifts the
terminal value by `σ · Δw`. -/
@[stat_lemma]
theorem bachelierTerminal_linear_noise (S₀ μ σ T w Δw : ℝ) :
    bachelierTerminal S₀ μ σ T (w + Δw)
      = bachelierTerminal S₀ μ σ T w + σ * Δw := by
  unfold bachelierTerminal; ring

/-- **Sum-of-Bacheliers.** The Bachelier closed form decomposes as

    S_T = S₀ + μ·T + σ·w. -/
@[stat_lemma]
theorem bachelierTerminal_decompose (S₀ μ σ T w : ℝ) :
    bachelierTerminal S₀ μ σ T w = S₀ + (μ * T + σ * w) := by
  unfold bachelierTerminal; ring

/-- **Monotone in drift over a positive horizon.** For `T ≥ 0` and
`μ₁ ≤ μ₂`, the Bachelier terminal value with higher drift is at least
the terminal value with lower drift:
    `bachelierTerminal S₀ μ₁ σ T w ≤ bachelierTerminal S₀ μ₂ σ T w`.

Real Mathlib reasoning via `mul_le_mul_of_nonneg_right` lifting
`μ₁ ≤ μ₂` to `μ₁·T ≤ μ₂·T` using `0 ≤ T`, then `linarith` on the
remaining algebraic sum. -/
@[stat_lemma]
theorem bachelierTerminal_mono_drift (S₀ σ T w : ℝ) (hT : 0 ≤ T)
    {μ₁ μ₂ : ℝ} (h_drift : μ₁ ≤ μ₂) :
    bachelierTerminal S₀ μ₁ σ T w ≤ bachelierTerminal S₀ μ₂ σ T w := by
  unfold bachelierTerminal
  have : μ₁ * T ≤ μ₂ * T := mul_le_mul_of_nonneg_right h_drift hT
  linarith

/-- **Monotone in noise sample over non-negative volatility.** For
`σ ≥ 0` and `w₁ ≤ w₂`, the Bachelier terminal value with higher
noise sample is at least the terminal value with lower noise sample:
    `bachelierTerminal S₀ μ σ T w₁ ≤ bachelierTerminal S₀ μ σ T w₂`.

Same proof pattern as `bachelierTerminal_mono_drift`, applied to
the `σ * w` term. -/
@[stat_lemma]
theorem bachelierTerminal_mono_noise (S₀ μ σ T : ℝ) (hσ : 0 ≤ σ)
    {w₁ w₂ : ℝ} (h_noise : w₁ ≤ w₂) :
    bachelierTerminal S₀ μ σ T w₁ ≤ bachelierTerminal S₀ μ σ T w₂ := by
  unfold bachelierTerminal
  have : σ * w₁ ≤ σ * w₂ := mul_le_mul_of_nonneg_left h_noise hσ
  linarith

end Pythia.Finance
