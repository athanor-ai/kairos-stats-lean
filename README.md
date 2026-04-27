# pythia

[![CI](https://github.com/athanor-ai/pythia/actions/workflows/lean-build.yml/badge.svg)](https://github.com/athanor-ai/pythia/actions/workflows/lean-build.yml)
[![Sim sweep](https://github.com/athanor-ai/pythia/actions/workflows/pythia-sim.yml/badge.svg)](https://github.com/athanor-ai/pythia/actions/workflows/pythia-sim.yml)
[![codecov](https://codecov.io/gh/athanor-ai/pythia/branch/main/graph/badge.svg)](https://codecov.io/gh/athanor-ai/pythia)
[![Lean](https://img.shields.io/badge/Lean-4.28.0-blue.svg)](https://github.com/leanprover/lean4/releases/tag/v4.28.0)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-blue.svg)](https://github.com/leanprover-community/mathlib4/releases/tag/v4.28.0)
[![License](https://img.shields.io/badge/License-Apache%202.0-green.svg)](LICENSE)
[![Axiom-clean](https://img.shields.io/badge/axioms-propext%20%2B%20Classical.choice%20%2B%20Quot.sound-success.svg)](Pythia/AxiomAudit.lean)

<!-- pythia-stats-auto-begin -->
**Coverage**:
- 549 theorem/lemma declarations in `Pythia/`
- 56 `@[stat_lemma]`-tagged theorems in the `pythia` tactic cascade
- 32 cross-domain theorems with Lean proof + Python sim runner across 15 domains (biology, chemistry, control, economics, engineering, game_theory, info_theory, mathlib_tags, mechanical, numerical, optimal_transport, or, quantum, stochastic, thermodynamics)

Auto-tracked from [`tools/sim/theorem_manifest.py`](tools/sim/theorem_manifest.py) and the `Pythia/` source tree; regenerate via `python3 tools/refresh_readme_stats.py`.
<!-- pythia-stats-auto-end -->

A Lean 4 tactic library for closing proofs across applied mathematics.
Probability, statistics, biology, actuarial science, control theory,
information theory, queueing, time series, and numerical analysis
all live here under one tactic cascade.

Mathlib supplies the foundations: measures, martingales, sub-Gaussian
machinery, ODE flows, the optional-stopping theorem. Closing a goal
still takes the kind of by-hand chase that ends with measurability
obligations, ENNReal arithmetic, a stopping-time induction, or a
domain-specific identity (Hardy-Weinberg conservation, Pareto tail,
Wold decomposition, Lyapunov stability). `pythia` is what the
standard automation (`simp`, `linarith`, `aesop`, `bound`,
`measurability`) looks like once you specialize it for the
applied-mathematics working set. A goal like

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

- Eleven tactics covering general stats hammering, inequality
  closure, probability normalization, anytime-valid Ville bounds,
  SMT-oracle dispatch (QF_LRA via Z3, QF_BV via CVC5), first-order-
  logic closure (Vampire, E), counterexample finding (`disprove`), a
  and the headline `pythia!` hammer ladder (ATH-753 / ATH-756) that
  walks the full closer surface in priority order with per-rung
  timing in the verbose form `pythia?`.
- A registry layer: tag your own theorem with `@[stat_lemma]` /
  `@[stats_ineq]` / `@[prob_simp]` and the hammers pick it up at
  elaboration time. The same shape as `@[simp]`, `@[gcongr]`,
  `@[bound]`. No fork, no config file.
- A statistics-spine theorem library covering anytime-valid confidence
  sequences (Howard-Ramdas, betting CS, vector + asymptotic
  families), Bernstein / Bennett / sub-gamma concentration, optional
  stopping for unbounded τ, and information-theoretic bounds
  (Bretagnolle-Huber binary, PAC-Bayes Radon-Nikodym).
- A cross-domain theorem library: chemistry (Arrhenius rate
  positivity, Henderson-Hasselbalch monotonicity, mass-action
  conservation), biology (Hardy-Weinberg, Lotka-Volterra equilibrium,
  SIR conservation), economics (Cobb-Douglas, CRRA, CAPM,
  risk-neutral call, Walras' Law), engineering (RC time constant,
  signal energy, Ohm power dissipation), mechanical (Hooke spring),
  control (scalar Lyapunov), operations research (Little's Law),
  plus mathlib retags with empirical companions (AM-GM, Markov,
  Cauchy-Schwarz). The full registry is at
  [`tools/sim/theorem_manifest.py`](tools/sim/theorem_manifest.py).
- An empirical layer alongside every cross-domain theorem: each
  ships a Python runner in
  [`tools/sim/`](tools/sim/) running 10 000-draw property-based
  testing, deterministic parameter sweeps, and mutation testing so
  the formal bound is checked numerically too.
  [`tools/add_theorem.py`](tools/add_theorem.py) scaffolds a new
  theorem from a single command; CI runs the full sim sweep on
  every PR.
- All public theorems are axiom-clean against
  `{propext, Classical.choice, Quot.sound}`. The Z3 / CVC5 / Vampire
  / E oracles reconstruct every closure into a Lean tactic script
  the kernel checks; no oracle's verdict closes a goal on its own.
  Pattern adapted from CoqHammer (Czajka-Kaliszyk, JAR 2018).

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

## Natural-language interface (via Claude + Athanor SDK)

This repository is the Lean library: theorems, tactics, and oracle
adapters, all Apache-2.0. The natural-language flow on top of it
(English requirement → Lean statement → tactic dispatch → English
summary) lives in the **Athanor SDK** companion, which you call from
Claude. Two entry points:

- **Claude Code with the SDK**:
  [`athanor-ai/athanor-sdk`](https://github.com/athanor-ai/athanor-sdk)
  exposes a `simple_prove(...)` API plus the multi-agent orchestrator
  that pulls in the right pythia tactics for each goal. You bring
  your own Claude API key; the SDK never holds it.
- **Claude MCP**: any MCP-capable client (Claude desktop, Claude
  Code) can attach to pythia via
  [`oOo0oOo/lean-lsp-mcp`](https://github.com/oOo0oOo/lean-lsp-mcp)
  for goal-state queries and tactic search.

**Recommended model: Claude Opus 4.6 or 4.7.** The autoformalization
step benefits substantially from a strong reasoning model.

Oracles wired on the pythia Lean side today: Z3 (QF_LRA), CVC5
(QF_BV + QF_LRA backup), Vampire (FOL), E (FOL backup). All
open-source, all run locally, all kernel-clean: every verdict is
reconstructed into a Lean tactic script the kernel checks against
`{propext, Classical.choice, Quot.sound}`. No claim escapes the
kernel.

Phase 6 reflective adapters (EBMC for hardware assertions, CBMC for
software invariants, Dafny for Hoare triples) are design-only at
this point. See [`docs/reflective_oracles.md`](docs/reflective_oracles.md)
for the kernel-clean restriction (each requires a per-language
reflective decision procedure to land first).

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

Eleven registered tactics ship in the public surface:

| Tactic | Closes |
|--------|--------|
| `pythia!` | hammer ladder orchestrator: walks a 9-rung ladder (`stat_simp`/`simp` → linarith chain → positivity → aesop[Pythia] → pythia → z3_check → cvc5_check → vampire_check/e_check → disprove) with per-rung budget; first to close wins. Rung 1 hooks the `@[stat_simp]` curated set (ATH-758) so every downstream rung sees a normalized goal. LLM-free per CONTRIBUTING rule 4; LLM-augmented closure lives in the kairos-sdk companion. Headline orchestrator (ATH-753 / ATH-756 / ATH-758) |
| `pythia?` | verbose `pythia!`: prints the closing rung plus per-rung wall-clock timing for the full 9-rung ladder. Lean convention `apply?` `rw?` `simp?` `aesop?` use the `?` suffix to ask "show me what you did". The legacy `pythia!!` / `pythia!?` spellings survive as deprecated aliases for one minor version (ATH-756) |
| `pythia` | shape-dispatching orchestrator: routes to `anytime_valid` / `stats_ineq` / `prob_simp` / `z3_check` / `cvc5_check` / `vampire_check` / `e_check` by goal shape, then falls through to the `@[stat_lemma]` aesop ruleset and the standard Mathlib chain |
| `vampire_check` | first-order-logic goals via Vampire ATP + Lean `aesop` reconstruction |
| `e_check` | first-order-logic goals via E theorem prover + Lean `aesop` reconstruction (Vampire backup) |
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
| see which `@[stat_lemma]`s feed into which top-level theorems | [`docs/dep_graph.md`](docs/dep_graph.md) |

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

Applied-math domain coverage (scaffolds + Aristotle-driven closures):

- `Pythia.Actuarial`: Pareto / Weibull / log-normal loss distributions (moment + tail formulas) plus the in-flight Cramér-Lundberg / Sparre Andersen / Lundberg / Cox proportional-hazards / Bornhuetter-Ferguson Aristotle queue.
- `Pythia.Numerical`: Picard-Lindelöf ODE existence + uniqueness + continuous dependence; Lyapunov stability + asymptotic stability + LaSalle invariance; Kahan compensated summation backward-error; KKT first-order conditions (necessary + sufficient under convexity).
- `Pythia.Bio`: chemical-reaction-network ODE wellposedness + nonneg-orthant invariance + mass conservation + detailed-balance equilibrium; phylogenetic likelihood + Jukes-Cantor substitution model.
- `Pythia.HypothesisTest`: Wald-test alpha-bound; Bonferroni / Holm / Benjamini-Hochberg multiple-testing corrections (FWER + FDR control).

Beyond-proof tools:

- `Pythia.Tactic.TightTail`: tail-bound calculator. `#eval TightTail.report (σ := 0.3) (b := 1) (n := 1000) (ε := 0.05)` evaluates Hoeffding / Bernstein / sub-Gaussian / sub-gamma / Markov / Chebyshev numerically, picks the sharpest. Lean has no equivalent.
- `Pythia.Tactic.DomainCalculator`: typeclass for per-domain calculators. TightTail is the first instance; v0.5+ adds Numerical / Bayesian / Bio calculators following the same recipe.
- `Pythia.Tactic.Disprove`: counterexample finder via Z3 sat verdict + model extraction. `disprove (minimize := |x|+|y|)` returns the smallest violating assignment via Z3 Optimize. Lean has no built-in counterexample finder.

LLM-defense layer (engine side; kairos owns the dashboard composite):

- `Pythia.Tactic.ValidateInvokedLemmas` (Guard B): catches LLM-hallucinated lemma names.
- `Pythia.Tactic.MinimizeHypotheses` (Guard C): flags unused hypothesis binders.
- `Pythia.Tactic.FlagConcreteConstants` (Guard H): flags hard-coded numerical literals in theorem statements.
- See [`docs/llm_defense.md`](docs/llm_defense.md) for the 8-failure-mode framework + engine-vs-dashboard split.

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

PRs welcome. The full walkthrough is in
[`CONTRIBUTING.md`](CONTRIBUTING.md). The short version:

For a **cross-domain closed-form fact** (chemistry, biology, economics,
engineering, mechanics, control, OR, etc.), use the scaffold:

```bash
python3 tools/add_theorem.py \
    --domain Mechanical \
    --name bernoulli_invariant \
    --statement '...' \
    --summary '...' \
    --strategy 'p1=floats(0,1e6),...' \
    --reference 'Bernoulli, D. Hydrodynamica (1738)'
```

This writes the Lean module + the Python runner skeleton + appends
the manifest entry. Fill in the proof body + the spec body, then:

```bash
lake build Pythia.Mechanical.BernoulliInvariant
python3 tools/run_pythia_sim.py
```

For a **statistics-spine** result (anytime-valid CS, concentration,
e-detectors, info-theoretic divergences), open an issue first to scope.
Same axiom-clean bar applies. Details in
[`CONTRIBUTING.md`](CONTRIBUTING.md).

All public theorems must axiom-audit clean (`#print axioms` reports only
`propext`, `Classical.choice`, `Quot.sound`) before merge. Two CI
checks gate every PR: Lean Build + Axiom Audit and the Pythia
simulation sweep.

## Acknowledgments

The library is built on the Lean 4 + Mathlib community, particularly the
`Mathlib.Probability.Moments.SubGaussian` and
`MeasureTheory.Martingale.OptionalStopping` machinery. Theorems trace
to the anytime-valid inference research lineage (Howard-Ramdas-
McAuliffe-Sekhon 2021, Waudby-Smith-Ramdas 2024, Ramdas-Grünwald-Vovk-
Shafer 2023, Chugg-Wang-Ramdas 2024) and to the broader concentration
inequality + matrix probability lines cited inline. All public theorems
are axiom-clean against `{propext, Classical.choice, Quot.sound}`.

A subset of the theorems were closed with help from automated proof
search and large-language-model assistance:

- *Aristotle* (Harmonic) helped close several of the harder
  measure-theoretic theorems in `Pythia.Bernstein`,
  `Pythia.MGFBoundedSubGamma`, and `Pythia.MeasureTheory.*`.
  See [aristotle.harmonic.fun](https://aristotle.harmonic.fun/dashboard/docs/citation)
  for the canonical citation.
- *Anthropic Claude* (Opus 4.6 and Sonnet 4.6) drafted proof
  candidates and reviewed library structure. The Pythia tactic
  cascade dispatches to model-side drafters via
  [`kairos.model_client`](https://github.com/athanor-ai/athanor-sdk).
- *DeepSeek-Prover-V2* (DeepSeek team) contributed candidate proofs
  via the specialised-prover row of the formal-AVS benchmark companion
  evaluation. See the [DSPv2-7B model card](https://huggingface.co/deepseek-ai/DeepSeek-Prover-V2-7B).

## License

Apache-2.0. See `LICENSE`.

## Citation

If you use pythia in your research, please cite:

```bibtex
@misc{pythia2026,
  title  = {Pythia: A Lean 4 Tactic Library for Statistics and Applied Math},
  author = {Yang, Aidan Z. H. and {Athanor-AI}},
  year   = {2026},
  url    = {https://github.com/athanor-ai/pythia},
  note   = {Apache-2.0}
}
```
