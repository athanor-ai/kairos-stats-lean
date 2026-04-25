# pythia

> *Aesop-grade automation for statistics in Lean 4.*

`pythia` is the headline tactic of a Lean 4 library that wants to be the
canonical machine-checked reference for the statistical territory Mathlib
does not yet cover — anytime-valid inference, sequential statistics,
empirical processes, stochastic approximation, and the cross-domain
results practitioners in quant / actuarial / physics / biology / ML reach
for. Like `aesop` for general math, `pythia` closes domain-specific goals
in one tactic call, backed by a registered lemma library, a stats-domain
`grind` simp set, and a published aesop ruleset.

This repository is the Lean library only. **No LLMs, no cloud, no fleet
machinery.** The library works offline against any Lean 4 / Mathlib
installation. LLM-driven autoformalization, multi-prover swarm
orchestration, and Aristotle integration live separately in
[`athanor-sdk`](https://github.com/athanor-ai/athanor-sdk).

The repo was previously hosted at `athanor-ai/kairos-stats-lean` and was
renamed to `pythia` on 2026-04-25 to align with the headline tactic. The
old URL still works via GitHub's redirect; no action needed for existing
consumers.

## Status

| Block | Tag | Status |
|-------|-----|:------:|
| Phase A — toolchain + CI + axiom-audit | `v0.1.0` | ✅ |
| Phase B — `anytime_valid` tactic + `@[cs_family]` attribute | `v0.2.0` | ✅ |
| Phase C — sub-gamma, time-uniform CLT, PAC-Bayes | `v0.3.0` | ⚠ partial |
| Tier 1 — Bernstein / Bennett / Freedman / sub-exp | `v0.4.0` | scaffolds in flight |
| Tier 2 — SPRT / Wald's identity / e-detector | `v0.5.0` | scaffolds landed (PR #11) |
| Tier 8 — `pythia` + `kairos_grind` + `kairos_aesop` ruleset + `#concentration` | `v0.6.0` | design in flight |
| Tier 3 / 4 / 5 / 6 / 7 + cross-domain candidates | `v0.7.0+` | roadmapped |

See [`ROADMAP.md`](ROADMAP.md) for the full multi-tier plan and the
cross-domain candidate pool (quant / actuarial / physics / biology / ML /
signal-processing / control).

## Install

Add to your `lakefile.lean` (the lake package name is still `KairosStats`
during the transition; that rename is deferred to v1.0):

```lean
require kairos-stats-lean from git
  "https://github.com/athanor-ai/pythia.git" @ "main"
```

Then `import Kairos` (the umbrella module) or any individual
`Kairos.Stats.*`. Mathlib is pulled transitively at the same revision; do
not bump independently. The toolchain is pinned to Lean 4.28.0 + Mathlib
v4.28.0 for Aristotle parity.

## Quick tour

Foundations:

- `Kairos.Stats.Basic` — `BitPrecision`, `Time := ℕ`, the `slack` envelope.
- `Kairos.Stats.SubGaussianMG` — measure-theoretic sub-Gaussian martingale + exponential supermartingale + finite-horizon Ville.
- `Kairos.Stats.VilleSupermartingale` — Ville's inequality for non-negative supermartingales: `μ{∃ t, f t ≥ c} ≤ E[f 0] / c`. Marquee theorem.
- `Kairos.Stats.VilleMathlibPR` — version of the Ville statement packaged in Mathlib-PR style.
- `Kairos.Stats.StoppingRule` — `StoppingRule` primitive with `monotone_once_fired`.
- `Kairos.Stats.BettingStrategy` — bounded adaptive strategy + wealth process `W_t = ∏ (1 + λ_s ξ_s)`.
- `Kairos.Stats.PhiTransform` — exponential betting-transform from self-normalized to wealth form.
- `Kairos.Stats.SubGamma` — sub-gamma tail-class generalization of `SubGaussianMG`.

CS families:

- `Kairos.Stats.HowardRamdasCS` — admissibility of the telescoping HR boundary `σ √(2 t log(t(t+1)/α))`.
- `Kairos.Stats.BettingCS` — admissibility of the betting CS via infinite-horizon Ville + log-wealth threshold.
- `Kairos.Stats.GaussianRandomWalk` — sub-Gaussian random-walk crossing scaffold for vector + asymptotic families.
- `Kairos.Stats.GaussianSmallBall` — Gaussian small-ball lower bound on the boundary-grazing event.

Constants and rates:

- `Kairos.Stats.Quantization` — scalar quantization-transport lemma + `etaHR`, `etaVector`, `etaAsymptotic`, `etaBetting` + family ranking.
- `Kairos.Stats.MatchingConstants` — closed-form sharp constants `c_vector_sharp = 1/(2√π)`, `c_aCS_sharp = 1/(2√(2π))`.
- `Kairos.Stats.Sharpness` — boundary-hugging adversaries that saturate `η_F · 2^{-s} · σ`.
- `Kairos.Stats.VectorSharpness` — sharp-constant upgrade for the vector family.
- `Kairos.Stats.PowerAnalysis` — Type-II / power-loss analogue of the slack theorem.
- `Kairos.Stats.DeploymentDesign` — inverse: minimal `s` for a target coverage deviation `δ`.

Quantization variants:

- `Kairos.Stats.InputQuantization` — input-quantized variant (process observed at finite precision; exact boundary).
- `Kairos.Stats.InformationTheoretic` — channel-capacity reformulation of the slack rate.
- `Kairos.Stats.EquivalenceBreak` — finite-precision equivalence-breaking between self-normalized and betting CS.
- `Kairos.Stats.ElegantUnification` — three structural unifications across families.

Experimental:

- `Kairos.Stats.NewTargetsStubs` — auxiliary lemma stubs feeding the formal-AVS expansion.
- `Kairos.Stats.BenchDefs` — definitions for the Aristotle T0/T1/T2 bench.
- `Kairos.Stats.AristotleT0T1T2Bench` — Aristotle-testable restatements of selected library theorems.

## Examples

### Ville's inequality on a non-negative supermartingale

```lean
import Kairos.Stats.VilleSupermartingale

open Kairos.Stats MeasureTheory

example
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0}
    (hsup : Supermartingale f 𝓕 μ) (hnn : ∀ t ω, 0 ≤ f t ω)
    (hint : Integrable (f 0) μ) {c : ℝ} (hc : 0 < c) :
    μ {ω | ∃ t, f t ω ≥ c} ≤ (∫ ω, f 0 ω ∂μ).toNNReal / c.toNNReal :=
  ville_supermartingale hsup hnn hint hc
```

### Howard-Ramdas CS admissibility

```lean
import Kairos.Stats.HowardRamdasCS

open Kairos.Stats MeasureTheory

example
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : SubGaussianMG 1 𝓕 μ)
    (hM0 : ∀ᵐ ω ∂μ, M.process 0 ω = 0)
    {α : ℝ} (hα : 0 < α ∧ α < 1) :
    μ {ω | ∃ t, M.process t ω ≥ hrBoundary 1 α t} ≤ ENNReal.ofReal α :=
  hrStoppingRule_admissible M hM0 α hα
```

### Betting CS admissibility

```lean
import Kairos.Stats.BettingCS

open Kairos.Stats MeasureTheory

example
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ} (σ : BettingStrategy 𝓕 B) (ξ : ℕ → Ω → ℝ)
    (h_bound : ∀ t ω, |σ.lam t ω * ξ t ω| < 1)
    (h_xi_adapted : Adapted 𝓕 ξ)
    (h_int : ∀ t, Integrable (ξ t) μ)
    (h_wint : ∀ t, Integrable (wealthProcess σ ξ t) μ)
    (h_zero : ∀ t, μ[(ξ t) | 𝓕 t] =ᵐ[μ] 0)
    (h_mart : Martingale (wealthProcess σ ξ) 𝓕 μ)
    {α : ℝ} (hα : 0 < α ∧ α < 1) :
    μ {ω | ∃ t, (bettingStoppingRule σ ξ α).decide
                  (fun t => logWealthProcess σ ξ t ω) t = true}
      ≤ ENNReal.ofReal α :=
  bettingStoppingRule_admissible σ ξ h_bound h_xi_adapted h_int h_wint
    h_zero h_mart α hα
```

## Versioning

Semantic versioning. The `Kairos.Stats.API` surface (the umbrella `Kairos`
module plus the public theorem names listed in the Quick tour) is stable
within a major version: signature changes go through a deprecation cycle.
Internal modules — names starting with a lowercase helper prefix or
declared `private`, plus everything under `BenchDefs` /
`AristotleT0T1T2Bench` / `NewTargetsStubs` — may churn on any release.
Mathlib revision pin is treated as part of the public surface; bumping it
is a major-version event.

## Axiom discipline

Every public theorem in this repository closes under the Lean 4 + Mathlib
core axiom set `{propext, Classical.choice, Quot.sound}`. No `sorry`, no
ad-hoc axioms, no `@[implemented_by]` shortcuts on theorem-level
definitions. Audit each theorem locally with

```lean
#print axioms Kairos.Stats.ville_supermartingale
#print axioms Kairos.Stats.hrStoppingRule_admissible
#print axioms Kairos.Stats.bettingStoppingRule_admissible
```

The full audit log lives at
`docs/axiom_audit.md` (regenerated on every release).

## Contributing

PRs welcome. Open an issue first to scope the change. All theorems must
axiom-audit clean (`#print axioms` reports only `propext`, `Classical.choice`,
`Quot.sound`) before merge, and the repo packaging matches Aristotle's
tarball convention so any reviewer can drop a contribution into a fresh
Aristotle worktree for a frictionless sanity-check.

## Acknowledgments

This library would not exist in its current form without
**[Harmonic](https://harmonic.fun)** and the **Aristotle** automated
theorem-proving system. Aristotle closed many of the hardest theorems in
this repository — including the Ville-supermartingale machine-check
(`d2755ea2`), the T3 Gaussian small-ball lower bound (`54614669`), the
T4 wealth-process martingale property (`ca5f0a75`), the deployment-design
trio (`4d9266c7`), the Type-II power-loss bound (`a03602a5`), the
Howard-Ramdas CS admissibility (`e0ca7af5`), the betting CS
admissibility (`82321bad`), the sub-gamma martingale + Bennett-Bernstein
maximal inequality (`f254e362`), and the PAC-Bayes Radon-Nikodym KL
divergence (`ff1832e6`) — all axiom-clean against
`{propext, Classical.choice, Quot.sound}`.

Several of those closures replaced sorry'd scaffolds that humans could
state cleanly but not prove without weeks of manual effort. Aristotle
reduced that to hours per theorem with full axiom-audit transparency on
every closure. The library is positioned, in part, around what is
*Aristotle-tractable* — the partnership shapes which territory we
formalize first.

The library is also indebted to the Lean 4 + Mathlib community
(particularly the `Mathlib.Probability.Moments.SubGaussian` and
`MeasureTheory.Martingale.OptionalStopping` machinery), and to the
`anytime-valid inference` research lineage (Howard-Ramdas-McAuliffe-
Sekhon 2021, Waudby-Smith-Ramdas 2024, Ramdas-Grünwald-Vovk-Shafer 2023,
Chugg-Wang-Ramdas 2024).

## License

Apache-2.0. See `LICENSE`.
