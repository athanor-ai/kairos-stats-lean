/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Black-Scholes Greeks (abstract-CDF form)

The Black-Scholes call-price formula and its first-order sensitivities
("Greeks") in closed form, parametrised over an abstract CDF `Φ : ℝ → ℝ`
and density `φ : ℝ → ℝ`.

Working over an abstract CDF lets us state and prove sign / bound
properties without depending on Mathlib's `Real.gaussianPdf` /
`Real.normalCDF` machinery (which may differ across Mathlib versions).
The concrete-normal instantiation is deferred to a separate module.

Standard formulas (with `d₁ = (log(S/K) + (r + σ²/2)·T) / (σ·√T)`
and `d₂ = d₁ - σ·√T`):

    Call(S, K, T, r, σ)  =  S · Φ(d₁) - K · exp(-r·T) · Φ(d₂)
    Δ                     =  Φ(d₁)
    Γ                     =  φ(d₁) / (S · σ · √T)
    Vega                  =  S · φ(d₁) · √T
    Rho                   =  K · T · exp(-r·T) · Φ(d₂)

## Main results

* `bsD1`, `bsD2`                : the standard `d₁` / `d₂` arguments
* `bsCallPrice` (abstract Φ)    : closed-form call price
* `bsDelta` (abstract Φ)        : `Φ(d₁)`
* `bsGamma` (abstract φ)        : `φ(d₁) / (S · σ · √T)`
* `bsDelta_bounded`             : under `0 ≤ Φ ≤ 1` axiom, `0 ≤ Δ ≤ 1`
* `bsGamma_nonneg`              : under `0 ≤ φ` axiom, `0 ≤ Γ` for `S, σ, √T > 0`
* `bsVega_nonneg`               : under `0 ≤ φ` axiom, `0 ≤ Vega` for `S, √T ≥ 0`
* `bsRho_nonneg`                : under `0 ≤ Φ` axiom + `K, T ≥ 0`, `0 ≤ Rho`

## Why this lemma

Options Greeks are the practitioner-standard sensitivity vocabulary
(option-desk P&L attribution, delta-hedging, gamma scalping, vega
trading).  Surfacing the closed forms in Pythia — even at the abstract
CDF/PDF level — gives the `pythia` tactic cascade a clean closure target
for sign-direction sanity checks on derivatives pricing.

## References

* Black, F. and Scholes, M. "The Pricing of Options and Corporate
  Liabilities." *Journal of Political Economy* 81(3): 637-654 (1973).
* Hull, J. C. *Options, Futures, and Other Derivatives*, 10th ed.
  Pearson (2017), §19.4-§19.8 (the Greeks).
-/
import Mathlib
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance

/-- Black-Scholes `d₁`: `(log(S/K) + (r + σ²/2)·T) / (σ·√T)`. -/
noncomputable def bsD1 (S K T r σ : ℝ) : ℝ :=
  (Real.log (S / K) + (r + σ^2 / 2) * T) / (σ * Real.sqrt T)

/-- Black-Scholes `d₂`: `d₁ - σ·√T`. -/
noncomputable def bsD2 (S K T r σ : ℝ) : ℝ :=
  bsD1 S K T r σ - σ * Real.sqrt T

/-- Black-Scholes call price (abstract CDF form). -/
noncomputable def bsCallPrice (Φ : ℝ → ℝ) (S K T r σ : ℝ) : ℝ :=
  S * Φ (bsD1 S K T r σ) - K * Real.exp (-(r * T)) * Φ (bsD2 S K T r σ)

/-- Black-Scholes delta `Δ = ∂C/∂S = Φ(d₁)` (abstract CDF form). -/
noncomputable def bsDelta (Φ : ℝ → ℝ) (S K T r σ : ℝ) : ℝ :=
  Φ (bsD1 S K T r σ)

/-- Black-Scholes gamma `Γ = ∂²C/∂S² = φ(d₁) / (S·σ·√T)` (abstract PDF form). -/
noncomputable def bsGamma (φ : ℝ → ℝ) (S K T r σ : ℝ) : ℝ :=
  φ (bsD1 S K T r σ) / (S * σ * Real.sqrt T)

/-- Black-Scholes vega `V = ∂C/∂σ = S·φ(d₁)·√T` (abstract PDF form). -/
noncomputable def bsVega (φ : ℝ → ℝ) (S K T r σ : ℝ) : ℝ :=
  S * φ (bsD1 S K T r σ) * Real.sqrt T

/-- Black-Scholes rho `ρ = ∂C/∂r = K·T·exp(-r·T)·Φ(d₂)` (abstract CDF form). -/
noncomputable def bsRho (Φ : ℝ → ℝ) (S K T r σ : ℝ) : ℝ :=
  K * T * Real.exp (-(r * T)) * Φ (bsD2 S K T r σ)

/-- **Delta is bounded in `[0, 1]`.** Under the standard CDF axioms
`0 ≤ Φ(x) ≤ 1` for all `x`, delta lies in `[0, 1]` — the classical
"call delta is a probability" interpretation. -/
@[stat_lemma]
theorem bsDelta_bounded (Φ : ℝ → ℝ)
    (hΦ_nonneg : ∀ x, 0 ≤ Φ x) (hΦ_le_one : ∀ x, Φ x ≤ 1)
    (S K T r σ : ℝ) :
    0 ≤ bsDelta Φ S K T r σ ∧ bsDelta Φ S K T r σ ≤ 1 := by
  unfold bsDelta; exact ⟨hΦ_nonneg _, hΦ_le_one _⟩

/-- **Gamma is non-negative.** Under the standard PDF non-negativity
axiom `0 ≤ φ`, gamma is non-negative when `S > 0`, `σ > 0`, `T > 0`. -/
@[stat_lemma]
theorem bsGamma_nonneg (φ : ℝ → ℝ) (hφ_nonneg : ∀ x, 0 ≤ φ x)
    {S σ T : ℝ} (hS : 0 < S) (hσ : 0 < σ) (hT : 0 < T) (K r : ℝ) :
    0 ≤ bsGamma φ S K T r σ := by
  unfold bsGamma
  apply div_nonneg (hφ_nonneg _)
  have hsqrtT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  positivity

/-- **Vega is non-negative.** Under PDF non-negativity, vega is
non-negative when `S ≥ 0` and `T ≥ 0`. -/
@[stat_lemma]
theorem bsVega_nonneg (φ : ℝ → ℝ) (hφ_nonneg : ∀ x, 0 ≤ φ x)
    {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) (K r σ : ℝ) :
    0 ≤ bsVega φ S K T r σ := by
  unfold bsVega
  have hsqrtT : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  exact mul_nonneg (mul_nonneg hS (hφ_nonneg _)) hsqrtT

/-- **Rho is non-negative for a call.** Under CDF non-negativity,
rho on a call is non-negative when `K ≥ 0` and `T ≥ 0`. -/
@[stat_lemma]
theorem bsRho_nonneg (Φ : ℝ → ℝ) (hΦ_nonneg : ∀ x, 0 ≤ Φ x)
    {K T : ℝ} (hK : 0 ≤ K) (hT : 0 ≤ T) (S r σ : ℝ) :
    0 ≤ bsRho Φ S K T r σ := by
  unfold bsRho
  have h_exp : 0 ≤ Real.exp (-(r * T)) := (Real.exp_pos _).le
  exact mul_nonneg (mul_nonneg (mul_nonneg hK hT) h_exp) (hΦ_nonneg _)

end Pythia.Finance
