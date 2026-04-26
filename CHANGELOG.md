# Changelog

All notable changes to `pythia` are documented here. The format is loosely [Keep a Changelog](https://keepachangelog.com/), and this project follows [Semantic Versioning](https://semver.org/): `Pythia.API` is the stable public surface, internal modules may churn within a major version.

## Unreleased: Phase 0+5 Sledgehammer

### Added
- *Phase-0 dispatcher.* `pythia` is now a shape-dispatching orchestrator instead of a thin aesop wrapper: the tactic routes by goal shape to `anytime_valid` (Ville bounds), `stats_ineq` (concentration), `prob_simp` (measure rewriting), `z3_check` (QF_LRA), `vampire_check` and `e_check` (FOL), then falls through to the `@[stat_lemma]` aesop ruleset and the standard Mathlib chain. Each branch is gated by `done` so partial-closure inner tactics cannot capture the cascade.
- `pythia?`: verbose variant that prints which rung closed the goal. Lean convention `apply?` / `rw?` / `simp?` / `aesop?`.
- *Vampire + E FOL adapters.* `Pythia.Tactic.{TPTPEncode, VampireCheck, ECheck}` plus the matching test files. Vampire is the primary FOL backend; E is the backup. Both reconstruct via aesop with hypotheses promoted; the kernel never trusts the prover's verdict.
- `Pythia.Tactic.TightTail` (the tail-bound calculator). `TightTail.report (σ := …) (b := …) (n := …) (ε := …)` evaluates Hoeffding, Bernstein, sub-Gaussian, sub-gamma, Markov, Chebyshev numerically and prints them sorted, with the sharpest labeled. This is the kind of question Lean+Mathlib's standard automation does not answer: tactics close proofs of bounds; this picks the bound.
- `Pythia/Bench/MiniPythia.lean`: 30-theorem benchmark suite covering the six dispatch rungs. `#bench_summary` prints the section breakdown.
- `examples/04_pythia_full_dispatch.lean` and `examples/05_tight_tail_calculator.lean`.
- `docs/sledgehammer_dispatch.md`: the routing table for every OSS oracle.
- `docs/reflective_oracles.md`: design constraint for EBMC / CBMC / Dafny adapters (kernel-clean reconstruction via Lean shadow + reflective decision procedure).
- `docs/concentration_cookbook.md`: quick reference mapping stats goal shapes to the right pythia tactic + the inequality the tactic actually invokes.
- README BYO-LLM section recording the bring-your-own-LLM scope. Customer's LLM key, our SDK; pythia (this repo) is the Lean library only. Recommended model: Claude Opus 4.6 or Claude Opus 4.7 for the natural-language to Lean to tactic-dispatch path.

### Removed
- `python/` sidecar directory: stale dist artifacts from an early pip-package experiment. Pythia ships as a Lean-only library following aesop's Lake-only model.

### Backwards compatibility
- `Pythia.API` public surface is unchanged.
- All existing tests pass against the upgraded `pythia` cascade.
- Toolchain remains pinned to Lean 4.28.0 + Mathlib v4.28.0.

## v0.2.0: Phase B: aesop-grade tactic + DSL

Phase B turns the library from a collection of theorems into a toolkit. Users register a new CS family with one attribute and close the marquee Ville bound with one tactic invocation.

### Added
- `anytime_valid` tactic: closes the marquee countable-time Ville bound goal in one line, given supermartingale + non-negativity + integrability + positivity hypotheses in scope.
- `anytime_valid (horizon := N)`: finite-horizon variant calling `ville_supermartingale_finite`.
- `anytime_valid using h`: explicit supermartingale witness term.
- `@[cs_family]` attribute: register a `CSFamily` declaration in a fleet-wide table.
- `#cs_families` command: list every registered family with a count.
- `#ville myCS` command: print the `eta` + `slackFn` of a registered family.
- `Pythia.Tactic.CSFamilyRegistry`: the four canonical families (HR, betting, vector, asymptotic) auto-registered with `attribute [cs_family]`.
- Regression test files under `Pythia/Tactic/*Test.lean`: every tactic + command is exercised at compile time. CI fails here before any broken implementation lands on main.

### Deferred to v0.3.0
- Auto-derivation of `Admissible` instance from a registered family. Requires a richer attribute syntax to take user-supplied proof terms; not worth doing without that design.
- Auto-derivation of `quantizationSlack` for the same reason.

### Backwards compatibility
- `Pythia.API` public surface is unchanged.
- All 29 axiom-clean headline theorems from v0.1.0 stay axiom-clean.
- Toolchain remains pinned to Lean 4.28.0 + Mathlib v4.28.0 for Mathlib parity.

[v0.2.0]: https://github.com/athanor-ai/pythia/releases/tag/v0.2.0

## v0.1.0: Phase A: stabilization

First tagged release. Library is `lake build`-able on a fresh clone, documented, and CI-gated with a machine-checked axiom audit.

### Added
- `README.md`: pitch, install snippet, 25-module tour, three copy-paste examples (Ville bound, HR CS admissibility, betting CS admissibility), semver policy, axiom-discipline pointer.
- `Pythia/API.lean`: stable public surface re-exporting the headline modules. Downstream users `import Pythia.API` for 90% of use cases.
- `Pythia/AxiomAudit.lean`: machine-checked axiom discipline: `#print axioms` on 29 headline declarations across 9 modules. Every declaration depends only on `{propext, Classical.choice, Quot.sound}`. Zero `sorryAx`.
- `.github/workflows/lean-build.yml`: GH Actions CI: `lake build` + axiom audit on every push and PR.
- `Pythia/VilleMathlibPR.lean`: Mathlib-PR-style draft of `ville_ineq` (`ENNReal.ofReal` form matching Mathlib's `maximal_ineq`). On-disk reference for upstream contribution work.

### Changed
- `lakefile.lean`: Mathlib pin moved from `@ "master"` to `@ "v4.28.0"`, locked for toolchain stability across the development cycle.
- `lake-manifest.json`: pinned to known-good revisions (mathlib `8f9d9cff`, proofwidgets `v0.0.87`).
- `Pythia.SubGaussianMG.ville_supermartingale` (finite-horizon lemma, used internally by `BettingCS`) renamed to `ville_supermartingale_finite` to free the unqualified name `ville_supermartingale` for the marquee infinite-horizon theorem in `Pythia.VilleSupermartingale`.

### Fixed
- Toolchain wedge from `proofwidgets v0.0.98` requiring Lean 4.30: pinning to v4.28.0 across the dependency tree restores a clean build.
- `Pythia/GaussianRandomWalk.lean`: added `IsFiniteMeasure` scaffold instance on `gaussianProductMeasure`. The instance is sorry-axiomatic at the scaffold level, consistent with the file's existing definitional sorries; downstream `SubGaussianMG` instantiations now resolve.

### Marquee theorems (axiom-clean against `{propext, Classical.choice, Quot.sound}`)
- `ville_supermartingale`: Ville's inequality for non-negative supermartingales, infinite-horizon, finite-measure.
- `ville_supermartingale_unit_initial`: unit-initial corollary (`μ {∃ t, f t ω ≥ c} ≤ 1/c` on probability spaces).
- `c_HR_sharp`, `c_betting_sharp`, `c_aCS_sharp`, `c_vector_sharp`: sharp matching-lower-bound constants for the four canonical CS families.
- `c_sharp_ranking`, `c_vector_eq_sqrt_two_mul_c_HR`: constant-ranking + algebraic identity.
- `hrStoppingRule_admissible`, `bettingStoppingRule_admissible`: admissibility theorems for Howard-Ramdas + betting CS.
- `equivalence_break_at_finite_precision_generic`: generic-form equivalence-break theorem.
- 29 declarations total are audited in `Pythia/AxiomAudit.lean`.

[v0.1.0]: https://github.com/athanor-ai/pythia/releases/tag/v0.1.0
