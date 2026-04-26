# pythia

[![CI](https://github.com/athanor-ai/pythia/actions/workflows/lean-build.yml/badge.svg)](https://github.com/athanor-ai/pythia/actions/workflows/lean-build.yml)
[![Lean](https://img.shields.io/badge/Lean-4.28.0-blue.svg)](https://github.com/leanprover/lean4/releases/tag/v4.28.0)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-blue.svg)](https://github.com/leanprover-community/mathlib4/releases/tag/v4.28.0)
[![License](https://img.shields.io/badge/License-Apache%202.0-green.svg)](LICENSE)
[![Axiom-clean](https://img.shields.io/badge/axioms-propext%20%2B%20Classical.choice%20%2B%20Quot.sound-success.svg)](Pythia/AxiomAudit.lean)

> *Aesop-grade automation for statistics in Lean 4.*

`pythia` is the headline tactic of a Lean 4 library that wants to be the
canonical machine-checked reference for the statistical territory Mathlib
does not yet cover — anytime-valid inference, sequential statistics,
empirical processes, stochastic approximation, and the cross-domain
results practitioners reach for. Like `aesop` for general math, `pythia`
closes domain-specific goals in one tactic call, backed by a registered
lemma library, a stats-domain `grind` simp set, and a published aesop
ruleset.

This repository is the Lean library only. **No LLMs, no cloud, no fleet
machinery.** The library works offline against any Lean 4 / Mathlib
installation.

## Install

Add to your `lakefile.lean`:

```lean
require pythia from git
  "https://github.com/athanor-ai/pythia.git" @ "main"
```

Then `import Pythia` (the umbrella module) or any individual `Pythia.*`
submodule. Mathlib is pulled transitively at the same revision; do not
bump independently. The toolchain is pinned to Lean 4.28.0 + Mathlib
v4.28.0.

## Hello, pythia

The shortest possible exposure to the headline tactic:

```lean
import Pythia.Tactic.Pythia

open Pythia

@[stat_lemma]
theorem nonneg_sum (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  linarith

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by pythia
```

Tag a theorem with `@[stat_lemma]` to register it into the `pythia`
lemma library. Then `pythia` closes goals that match — falling
through to Mathlib's standard `aesop` automation when no pythia rule
applies. See [`demo/`](demo/) for the 5-minute end-to-end walkthrough
and [`examples/`](examples/) for copy-paste-ready files.

## Tactics

Five registered tactics ship in the public surface:

| Tactic | Closes |
|--------|--------|
| `pythia` | stats-domain goals via `@[stat_lemma]` registry + aesop ruleset fallback |
| `stats_ineq` | scalar inequalities arising in concentration / tail bounds |
| `prob_simp` | probability-theoretic rewriting (measure pushforwards, conditional expectations) |
| `anytime_valid` | Ville-bound goals on non-negative supermartingales |
| `z3_check` | linear-real-arithmetic goals via Z3 oracle + Lean `linarith` reconstruction |

## Where to look

| If you want to… | Look at |
|-----------------|---------|
| run the headline `pythia` tactic | [`examples/01_pythia_smoke.lean`](examples/01_pythia_smoke.lean) |
| close a Ville-bound goal in 1 tactic call | [`examples/02_anytime_valid_smoke.lean`](examples/02_anytime_valid_smoke.lean) |
| introspect what's available | [`examples/03_cs_families_introspection.lean`](examples/03_cs_families_introspection.lean) |
| go from zero to closing your first goal | [`demo/README.md`](demo/README.md) |
| set up sub-second LSP feedback | [`docs/lean_lsp_mcp_setup.md`](docs/lean_lsp_mcp_setup.md) |

## Cross-prover hammer (`z3_check`)

`z3_check` dispatches linear-real-arithmetic goals to a local `z3`
binary, reads back the `unsat` verdict, and then asks Lean's `linarith`
to independently reconstruct the proof term. Z3 is treated strictly as
a ranking / filter oracle — its verdict never closes a goal. If `z3`
is unavailable on the build machine, the tactic falls through to
`linarith` directly, so CI is independent of the SMT install. See
[`Pythia.Tactic.Z3Check`](Pythia/Tactic/Z3Check.lean) and
[`Pythia.Tactic.Z3CheckTest`](Pythia/Tactic/Z3CheckTest.lean) for
worked examples.

The architectural rule: external solvers are **oracles**, not trusted
provers. Each backend produces a certificate (refutation, witness,
counterexample) that pythia's reconstruction layer turns into a Lean 4
tactic script. The Lean 4 kernel checks the script against
`{propext, Classical.choice, Quot.sound}` — same axiom budget as
Mathlib itself. CoqHammer (Czajka & Kaliszyk, JAR 2018) is the
canonical template for this discipline; we adapt it for Lean 4's CIC.

## Quick tour

Foundations:

- `Pythia.Basic` — `BitPrecision`, `Time := ℕ`, the `slack` envelope.
- `Pythia.SubGaussianMG` — measure-theoretic sub-Gaussian martingale + exponential supermartingale + finite-horizon Ville.
- `Pythia.VilleSupermartingale` — Ville's inequality for non-negative supermartingales: `μ{∃ t, f t ≥ c} ≤ E[f 0] / c`.
- `Pythia.StoppingRule` — `StoppingRule` primitive with `monotone_once_fired`.
- `Pythia.BettingStrategy` — bounded adaptive strategy + wealth process `W_t = ∏ (1 + λ_s ξ_s)`.
- `Pythia.PhiTransform` — exponential betting-transform from self-normalized to wealth form.
- `Pythia.SubGamma` — sub-gamma tail-class generalization of `SubGaussianMG`.

CS families:

- `Pythia.HowardRamdasCS` — admissibility of the telescoping HR boundary `σ √(2 t log(t(t+1)/α))`.
- `Pythia.BettingCS` — admissibility of the betting CS via infinite-horizon Ville + log-wealth threshold.
- `Pythia.GaussianRandomWalk` — sub-Gaussian random-walk crossing scaffold for vector + asymptotic families.
- `Pythia.GaussianSmallBall` — Gaussian small-ball lower bound on the boundary-grazing event.

Constants and rates:

- `Pythia.Quantization` — scalar quantization-transport lemma + `etaHR`, `etaVector`, `etaAsymptotic`, `etaBetting` + family ranking.
- `Pythia.MatchingConstants` — closed-form sharp constants `c_vector_sharp = 1/(2√π)`, `c_aCS_sharp = 1/(2√(2π))`.
- `Pythia.Sharpness` — boundary-hugging adversaries that saturate `η_F · 2^{-s} · σ`.
- `Pythia.VectorSharpness` — sharp-constant upgrade for the vector family.
- `Pythia.PowerAnalysis` — Type-II / power-loss analogue of the slack theorem.
- `Pythia.DeploymentDesign` — inverse: minimal `s` for a target coverage deviation `δ`.

Quantization variants:

- `Pythia.InputQuantization` — input-quantized variant (process observed at finite precision; exact boundary).
- `Pythia.InformationTheoretic` — channel-capacity reformulation of the slack rate.
- `Pythia.EquivalenceBreak` — finite-precision equivalence-breaking between self-normalized and betting CS.
- `Pythia.ElegantUnification` — three structural unifications across families.

## Examples

### Ville's inequality on a non-negative supermartingale

```lean
import Pythia.VilleSupermartingale

open Pythia MeasureTheory

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
import Pythia.HowardRamdasCS

open Pythia MeasureTheory

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
import Pythia.BettingCS

open Pythia MeasureTheory

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

Semantic versioning. The `Pythia.API` surface (the umbrella `Pythia`
module plus the public theorem names listed in the Quick tour) is stable
within a major version: signature changes go through a deprecation cycle.
Internal modules — names starting with a lowercase helper prefix or
declared `private` — may churn on any release. Mathlib revision pin is
treated as part of the public surface; bumping it is a major-version
event.

## Axiom discipline

Every public theorem in this repository closes under the Lean 4 + Mathlib
core axiom set `{propext, Classical.choice, Quot.sound}`. No `sorry`, no
ad-hoc axioms, no `@[implemented_by]` shortcuts on theorem-level
definitions. Audit each theorem locally with

```lean
#print axioms Pythia.ville_supermartingale
#print axioms Pythia.hrStoppingRule_admissible
#print axioms Pythia.bettingStoppingRule_admissible
```

The full audit log lives at
`docs/axiom_audit.md` (regenerated on every release).

## Contributing

PRs welcome. Open an issue first to scope the change. All theorems must
axiom-audit clean (`#print axioms` reports only `propext`, `Classical.choice`,
`Quot.sound`) before merge.

## Acknowledgments

This library would not exist in its current form without
**[Harmonic](https://harmonic.fun)** and the **Aristotle** automated
theorem-proving system. Aristotle closed many of the hardest theorems in
this repository — including the Ville-supermartingale machine-check, the
T3 Gaussian small-ball lower bound, the T4 wealth-process martingale
property, the deployment-design trio, the Type-II power-loss bound, the
Howard-Ramdas CS admissibility, the betting CS admissibility, the
sub-gamma martingale + Bennett-Bernstein maximal inequality, and the
PAC-Bayes Radon-Nikodym KL divergence — all axiom-clean against
`{propext, Classical.choice, Quot.sound}`.

The library is also indebted to the Lean 4 + Mathlib community
(particularly the `Mathlib.Probability.Moments.SubGaussian` and
`MeasureTheory.Martingale.OptionalStopping` machinery), and to the
`anytime-valid inference` research lineage (Howard-Ramdas-McAuliffe-
Sekhon 2021, Waudby-Smith-Ramdas 2024, Ramdas-Grünwald-Vovk-Shafer 2023,
Chugg-Wang-Ramdas 2024).

## License

Apache-2.0. See `LICENSE`.
