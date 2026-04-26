# pythia

[![CI](https://github.com/athanor-ai/pythia/actions/workflows/lean-build.yml/badge.svg)](https://github.com/athanor-ai/pythia/actions/workflows/lean-build.yml)
[![Lean](https://img.shields.io/badge/Lean-4.28.0-blue.svg)](https://github.com/leanprover/lean4/releases/tag/v4.28.0)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-blue.svg)](https://github.com/leanprover-community/mathlib4/releases/tag/v4.28.0)
[![License](https://img.shields.io/badge/License-Apache%202.0-green.svg)](LICENSE)
[![Axiom-clean](https://img.shields.io/badge/axioms-propext%20%2B%20Classical.choice%20%2B%20Quot.sound-success.svg)](Pythia/AxiomAudit.lean)

A Lean 4 tactic library for closing proofs in probability and statistics.

Mathlib supplies the foundations: measures, martingales, sub-Gaussian
machinery, the optional-stopping theorem. Closing a goal still takes
the kind of by-hand chase that ends with measurability obligations,
ENNReal arithmetic, and a stopping-time induction. `pythia` is what
the standard automation (`simp`, `linarith`, `aesop`, `bound`,
`measurability`) looks like once you specialize it for statistical
reasoning. A goal like

```lean
example
    {Ω : Type*} {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ _}
    (hsup : Supermartingale f 𝓕 μ) (hnn : ∀ t ω, 0 ≤ f t ω)
    (hint : Integrable (f 0) μ) {c : ℝ} (hc : 0 < c) :
    μ {ω | ∃ t, f t ω ≥ c} ≤ (∫ ω, f 0 ω ∂μ).toNNReal / c.toNNReal := by
  anytime_valid
```

closes in one line.

## What it does

- Ten tactics covering general stats hammering, inequality closure,
  probability normalization, anytime-valid Ville bounds, SMT-oracle
  dispatch (QF_LRA via Z3, QF_BV via CVC5), first-order-logic
  closure (Vampire, E), counterexample finding (`disprove`), and a
  rung-naming verbose orchestrator (`pythia?`).
- A registry layer: tag your own theorem with `@[stat_lemma]` /
  `@[stats_ineq]` / `@[prob_simp]` and the hammers pick it up at
  elaboration time. The same shape as `@[simp]`, `@[gcongr]`,
  `@[bound]`. No fork, no config file.
- A growing theorem library covering anytime-valid confidence
  sequences (Howard-Ramdas, betting CS, vector + asymptotic
  families), Bernstein / Bennett / sub-gamma concentration, optional
  stopping for unbounded τ, and information-theoretic bounds
  (Bretagnolle-Huber binary, PAC-Bayes Radon-Nikodym). All public
  theorems are axiom-clean against `{propext, Classical.choice,
  Quot.sound}`.
- A Z3 oracle (`z3_check`) that reconstructs every closure into a
  Lean tactic script: Z3's verdict never closes a goal on its own.
  Same axiom budget as Mathlib. Pattern adapted from CoqHammer
  (Czajka-Kaliszyk, JAR 2018).

## Why a separate library

Lean 4 + Mathlib already has strong general-purpose automation:
`aesop`, `simp`, `linarith`, `polyrith`, `nlinarith`, `positivity`,
`measurability`, `bound`, `gcongr`. They close a lot. They stop being
useful right when statistical reasoning starts: the moment a goal
mentions `Supermartingale`, an MGF chain, or a stopping time, the
generic hammers have nothing to apply.

Pythia is the closure layer (Bernstein-shaped lemmas, Ville's
inequality, Wald identities, e-detectors, the four canonical CS
families) registered so a domain-specialised hammer finds them.
Tactics read like Lean syntax (`by pythia`), not like library calls.
Error messages match Mathlib's tone.

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

## Bring-your-own LLM (for the natural-language → proof flow)

This repository is the Lean library: theorems, tactics, and oracle
adapters. The natural-language autoformalization layer (English → Lean
statement, then dispatch to `pythia` and friends, then the
natural-language summary) ships separately in our SDK and uses your
own LLM API key. We never hold a customer LLM key.

The SDK reads one of: `ANTHROPIC_API_KEY`, `OPENAI_API_KEY`,
`GEMINI_API_KEY` from your environment.

**Recommended model: Claude Opus 4.6 or Claude Opus 4.7.** The
autoformalization step benefits substantially from a strong reasoning
model. Opus has the highest closure rate on our internal calibration
set for the natural-language → Lean → tactic-dispatch path. Other
models work; Opus is the default we recommend.

Oracles wired on the pythia LEAN side today: Z3 (QF_LRA), CVC5
(QF_BV + QF_LRA backup), Vampire (FOL), E (FOL backup). All
open-source, all run locally, all kernel-clean: every verdict is
reconstructed into a Lean tactic script the kernel checks against
`{propext, Classical.choice, Quot.sound}`. No claim escapes the
kernel.

Phase 6 reflective adapters (EBMC for hardware assertions, CBMC for
software invariants, Dafny for Hoare triples) are design-only at
this point. See [`docs/reflective_oracles.md`](docs/reflective_oracles.md)
for the kernel-clean restriction (each requires a per-language
reflective decision procedure to land first). The companion SDK
ships separate Python adapters for those provers; the in-Lean
tactic is the gap.

## Hello, pythia

The shortest possible exposure to the `pythia` tactic:

```lean
import Pythia.Tactic.Pythia

open Pythia

@[stat_lemma]
theorem nonneg_sum (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  linarith

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by pythia
```

Tag a theorem with `@[stat_lemma]` to register it into the `pythia`
lemma library. Then `pythia` closes goals that match: falling
through to Mathlib's standard `aesop` automation when no pythia rule
applies. See [`demo/`](demo/) for the 5-minute end-to-end walkthrough
and [`examples/`](examples/) for copy-paste-ready files.

## Tactics

Ten registered tactics ship in the public surface:

| Tactic | Closes |
|--------|--------|
| `pythia` | shape-dispatching orchestrator: routes to `anytime_valid` / `stats_ineq` / `prob_simp` / `z3_check` / `cvc5_check` / `vampire_check` / `e_check` by goal shape, then falls through to the `@[stat_lemma]` aesop ruleset and the standard Mathlib chain |
| `vampire_check` | first-order-logic goals via Vampire ATP + Lean `aesop` reconstruction |
| `e_check` | first-order-logic goals via E theorem prover + Lean `aesop` reconstruction (Vampire backup) |
| `pythia?` | verbose `pythia`: same dispatch ladder, prints which rung closed the goal (Lean convention: `apply?`, `rw?`, `simp?`, `aesop?`) |
| `stats_ineq` | scalar inequalities arising in concentration / tail bounds |
| `prob_simp` | probability-theoretic rewriting (measure pushforwards, conditional expectations) |
| `anytime_valid` | Ville-bound goals on non-negative supermartingales |
| `z3_check` | linear-real-arithmetic goals via Z3 oracle + Lean `linarith` reconstruction |
| `cvc5_check` | bit-vector goals via CVC5 oracle + Lean `bv_decide` reconstruction; QF_LRA backup via `linarith` |
| `disprove` | counterexample finder. Asks Z3 for a model of the goal's negation; on `sat`, fails the proof attempt with a concrete witness. Lean has no built-in counterexample finder. |

## Where to look

| If you want to… | Look at |
|-----------------|---------|
| run the `pythia` tactic | [`examples/01_pythia_smoke.lean`](examples/01_pythia_smoke.lean) |
| close a Ville-bound goal in 1 tactic call | [`examples/02_anytime_valid_smoke.lean`](examples/02_anytime_valid_smoke.lean) |
| introspect what's available | [`examples/03_cs_families_introspection.lean`](examples/03_cs_families_introspection.lean) |
| see the full pythia dispatch ladder in action | [`examples/04_pythia_full_dispatch.lean`](examples/04_pythia_full_dispatch.lean) |
| pick the sharpest tail bound for your parameters | [`examples/05_tight_tail_calculator.lean`](examples/05_tight_tail_calculator.lean) |
| find a counterexample to a candidate stats claim | [`examples/06_disprove_smoke.lean`](examples/06_disprove_smoke.lean) |
| dispatch to the OSS cross-prover hammer chain | [`examples/07_cross_prover_smoke.lean`](examples/07_cross_prover_smoke.lean) |
| pick the right pythia tactic for your goal shape | [`docs/concentration_cookbook.md`](docs/concentration_cookbook.md) |
| run the MiniPythia benchmark | [`Pythia/Bench/README.md`](Pythia/Bench/README.md) |
| go from zero to closing your first goal | [`demo/README.md`](demo/README.md) |
| set up sub-second LSP feedback | [`docs/lean_lsp_mcp_setup.md`](docs/lean_lsp_mcp_setup.md) |
| understand the cross-prover dispatch | [`docs/sledgehammer_dispatch.md`](docs/sledgehammer_dispatch.md) |
| see why EBMC / CBMC / Dafny route through reflection | [`docs/reflective_oracles.md`](docs/reflective_oracles.md) |

## Cross-prover hammer (`z3_check`)

`z3_check` dispatches linear-real-arithmetic goals to a local `z3`
binary, reads back the `unsat` verdict, and then asks Lean's `linarith`
to independently reconstruct the proof term. Z3 is treated strictly as
a ranking / filter oracle: its verdict never closes a goal. If `z3`
is unavailable on the build machine, the tactic falls through to
`linarith` directly, so CI is independent of the SMT install. See
[`Pythia.Tactic.Z3Check`](Pythia/Tactic/Z3Check.lean) and
[`Pythia.Tactic.Z3CheckTest`](Pythia/Tactic/Z3CheckTest.lean) for
worked examples.

The architectural rule: external solvers are **oracles**, not trusted
provers. Each backend produces a certificate (refutation, witness,
counterexample) that pythia's reconstruction layer turns into a Lean 4
tactic script. The Lean 4 kernel checks the script against
`{propext, Classical.choice, Quot.sound}`: same axiom budget as
Mathlib itself. CoqHammer (Czajka & Kaliszyk, JAR 2018) is the
canonical template for this discipline; we adapt it for Lean 4's CIC.

`pythia` orchestrates a small pool of OSS oracles by goal shape:
linear-real to Z3/CVC5, bit-vector to CVC5, hardware-assertion to
EBMC, software-invariant to CBMC, first-order to Vampire/E,
Hoare-triple to Dafny. The full goal-shape dispatch table lives in
[`docs/sledgehammer_dispatch.md`](docs/sledgehammer_dispatch.md).

## Quick tour

Foundations:

- `Pythia.Basic`: `BitPrecision`, `Time := ℕ`, the `slack` envelope.
- `Pythia.SubGaussianMG`: measure-theoretic sub-Gaussian martingale + exponential supermartingale + finite-horizon Ville.
- `Pythia.VilleSupermartingale`: Ville's inequality for non-negative supermartingales: `μ{∃ t, f t ≥ c} ≤ E[f 0] / c`.
- `Pythia.StoppingRule`: `StoppingRule` primitive with `monotone_once_fired`.
- `Pythia.BettingStrategy`: bounded adaptive strategy + wealth process `W_t = ∏ (1 + λ_s ξ_s)`.
- `Pythia.PhiTransform`: exponential betting-transform from self-normalized to wealth form.
- `Pythia.SubGamma`: sub-gamma tail-class generalization of `SubGaussianMG`.

CS families:

- `Pythia.HowardRamdasCS`: admissibility of the telescoping HR boundary `σ √(2 t log(t(t+1)/α))`.
- `Pythia.BettingCS`: admissibility of the betting CS via infinite-horizon Ville + log-wealth threshold.
- `Pythia.GaussianRandomWalk`: sub-Gaussian random-walk crossing scaffold for vector + asymptotic families.
- `Pythia.GaussianSmallBall`: Gaussian small-ball lower bound on the boundary-grazing event.

Constants and rates:

- `Pythia.Quantization`: scalar quantization-transport lemma + `etaHR`, `etaVector`, `etaAsymptotic`, `etaBetting` + family ranking.
- `Pythia.MatchingConstants`: closed-form sharp constants `c_vector_sharp = 1/(2√π)`, `c_aCS_sharp = 1/(2√(2π))`.
- `Pythia.Sharpness`: boundary-hugging adversaries that saturate `η_F · 2^{-s} · σ`.
- `Pythia.VectorSharpness`: sharp-constant upgrade for the vector family.
- `Pythia.PowerAnalysis`: Type-II / power-loss analogue of the slack theorem.
- `Pythia.DeploymentDesign`: inverse: minimal `s` for a target coverage deviation `δ`.

Quantization variants:

- `Pythia.InputQuantization`: input-quantized variant (process observed at finite precision; exact boundary).
- `Pythia.InformationTheoretic`: channel-capacity reformulation of the slack rate.
- `Pythia.EquivalenceBreak`: finite-precision equivalence-breaking between self-normalized and betting CS.
- `Pythia.ElegantUnification`: three structural unifications across families.

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
Internal modules: names starting with a lowercase helper prefix or
declared `private`: may churn on any release. Mathlib revision pin is
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

The library is built on the Lean 4 + Mathlib community, particularly the
`Mathlib.Probability.Moments.SubGaussian` and
`MeasureTheory.Martingale.OptionalStopping` machinery. Theorems trace
to the anytime-valid inference research lineage (Howard-Ramdas-
McAuliffe-Sekhon 2021, Waudby-Smith-Ramdas 2024, Ramdas-Grünwald-Vovk-
Shafer 2023, Chugg-Wang-Ramdas 2024) and to the broader concentration
inequality + matrix probability lines cited inline. All public theorems
are axiom-clean against `{propext, Classical.choice, Quot.sound}`.

## License

Apache-2.0. See `LICENSE`.
