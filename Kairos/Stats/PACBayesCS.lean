/-
Kairos.Stats.PACBayesCS — PAC-Bayes confidence sequences.

References:
- Grunwald, de Heide, Koolen (2024, revised). *Safe testing.* JRSS-B
  (discussion paper). The GROW criterion + e-process formalism.
- Mhammedi-Grunwald (2019). PAC-Bayes confidence intervals via
  log-likelihood ratios.
- Chugg, Wang, Ramdas (2024). PAC-Bayes anytime-valid bounds.

The PAC-Bayes CS extends the standard betting CS by averaging the
test statistic over a *posterior* distribution of betting strategies,
paying a price proportional to the KL divergence between the
posterior and a prior. Tighter than worst-case betting whenever the
data is consistent with a low-KL posterior.

Phase C / v0.3.0 deliverable. Stated theorems sorry'd; the underlying
machinery (KL divergence on Polish spaces, the variational form of
PAC-Bayes, the e-process integration trick) is partially in Mathlib
but needs assembly here.

This module is the open promise from `neurips-2026-anytime-valid`
discussion §6 "Extensions left open: ... PAC-Bayes CS extension".
-/
import Mathlib
import Kairos.Stats.Basic
import Kairos.Stats.SubGaussianMG

namespace Kairos.Stats

open MeasureTheory ProbabilityTheory

/-- A PAC-Bayes prior over a measurable parameter space `Θ`. -/
structure PACBayesPrior (Θ : Type*) [MeasurableSpace Θ] where
  prior : Measure Θ
  is_probability : IsProbabilityMeasure prior

/-- A PAC-Bayes posterior is any measurable, absolutely-continuous-
with-respect-to-the-prior distribution on `Θ`. -/
structure PACBayesPosterior (Θ : Type*) [MeasurableSpace Θ]
    (P : PACBayesPrior Θ) where
  posterior : Measure Θ
  is_probability : IsProbabilityMeasure posterior
  abs_continuous : posterior ≪ P.prior

/-- KL divergence between posterior and prior, defined as
`D_KL(Q ‖ P) = ∫ log(dQ/dP) dQ`, where `dQ/dP` is the
Radon–Nikodym derivative. This equals `∫ (dQ/dP) log(dQ/dP) dP`
when `Q ≪ P`. Uses the `ENNReal`-valued `rnDeriv` from Mathlib,
converted to `ℝ` for the logarithm. -/
noncomputable def pacBayesKL
    {Θ : Type*} [MeasurableSpace Θ]
    {P : PACBayesPrior Θ} (Q : PACBayesPosterior Θ P) : ℝ :=
  ∫ θ, Real.log ((P.prior.rnDeriv Q.posterior θ)⁻¹).toReal ∂Q.posterior

/-- The pointwise wealth process for parameter `θ`:
$W_t(\theta, \omega) = \prod_{s < t} (1 + b(\theta, s, \omega))$.
Defined as a noncomputable real-valued process. -/
noncomputable def pointwiseWealth
    {Ω : Type*} {Θ : Type*} (b : Θ → ℕ → Ω → ℝ) (θ : Θ) (t : ℕ) (ω : Ω) : ℝ :=
  (Finset.range t).prod (fun s => 1 + b θ s ω)

/-- The mixture wealth process `W_t(ω) = ∫_Θ wealth(θ, t, ω) dP(θ)`,
where `P` is the PAC-Bayes prior. -/
noncomputable def mixtureWealth
    {Ω : Type*} {Θ : Type*} [MeasurableSpace Θ]
    (P : PACBayesPrior Θ) (b : Θ → ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∫ θ, pointwiseWealth b θ t ω ∂P.prior

/-- **PAC-Bayes confidence sequence** (Chugg-Wang-Ramdas 2024 Theorem 1).

Given a parameterised family of betting strategies `b : Θ → ℕ → Ω → ℝ`
and a PAC-Bayes prior `P`, the wealth process `W_t(ω) = ∫_Θ ∏_{s ≤ t}
(1 + b(θ, s, ω)) dQ(θ)` satisfies a Ville bound for any posterior `Q`
with `D_KL(Q‖P) ≤ K`:

    μ {ω | sup_t W_t(ω) ≥ exp(τ + K)} ≤ exp(-τ)

The PAC-Bayes CS at level α is then `{ω | W_t(ω) < (1/α) · exp(K)}`.
-/
theorem pacbayes_cs_ville
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Θ : Type*} [MeasurableSpace Θ]
    (P : PACBayesPrior Θ)
    (b : Θ → ℕ → Ω → ℝ)
    (hb_betting : ∀ θ, ∀ t, ∀ ω, -1 < b θ t ω ∧ b θ t ω < 1)
    (Q : PACBayesPosterior Θ P)
    (K : ℝ) (hK : pacBayesKL Q ≤ K) (τ : ℝ) (hτ : 0 < τ) :
    μ {ω | ∃ t : ℕ, mixtureWealth P b t ω ≥ Real.exp (τ + K)}
      ≤ ENNReal.ofReal (Real.exp (-τ)) := by
  sorry

/-- **PAC-Bayes mixture e-process construction**: integrating the
betting wealth against a prior produces a non-negative
supermartingale, the e-process backbone of any PAC-Bayes anytime-
valid bound. -/
theorem pacbayes_mixture_eprocess
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Θ : Type*} [MeasurableSpace Θ]
    (P : PACBayesPrior Θ)
    (b : Θ → ℕ → Ω → ℝ)
    (hb_betting : ∀ θ, ∀ t, ∀ ω, -1 < b θ t ω ∧ b θ t ω < 1)
    (𝓕 : MeasureTheory.Filtration ℕ mΩ) :
    -- The mixture wealth W_t = ∫_Θ wealth(θ, t, ·) dP(θ) is
    -- non-negative + a supermartingale under μ. Implication:
    -- ν A ↦ μ {ω | sup_t W_t(ω) ≥ τ} ≤ E[W_0] / τ via
    -- Kairos.Stats.ville_supermartingale.
    Supermartingale (mixtureWealth P b) 𝓕 μ ∧
      (∀ t ω, 0 ≤ mixtureWealth P b t ω) := by
  sorry

end Kairos.Stats
