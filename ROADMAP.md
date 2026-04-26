# kairos-stats-lean roadmap

This is the public roadmap for `kairos-stats-lean`. The library's
ambition is to be the canonical machine-checked formalization
reference for **anytime-valid inference and the broader sequential-
statistics territory that Mathlib does not yet cover**.

The bar is community utility. A theorem in this library should be
something a Lean user reaches for when their proof needs it, the
same way they reach for `aesop` or `Mathlib.Probability.Martingale`.

## Coverage status

### Already shipped (v0.2.0, axiom-clean)
- **Ville's inequality** for non-negative supermartingales (countable + finite-horizon).
- **Sub-Gaussian martingale** structure + Ville bound + admissibility.
- **Howard-Ramdas / Betting / Whitehouse-vector / Asymptotic-CLT** confidence-sequence families with sharp matching constants.
- **Quantization-transport lemma** for finite-precision deployment slack.
- **Equivalence-break theorem** under generic σ.
- **Sub-gamma martingale** structure + Bennett-Bernstein maximal inequality.
- **`anytime_valid` tactic** + `@[cs_family]` attribute + `#cs_families` / `#ville` commands.

### Phase C — in flight (v0.3.0)
- **Time-uniform CLT (WSSR24)**: scaffolded; Lévy-Prokhorov uniform-time convergence + Brownian-motion coupling. (`Kairos/Stats/TimeUniformCLT.lean`)
- **PAC-Bayes confidence sequences**: scaffolded; KL-divergence implementation via Mathlib `Measure.rnDeriv`. Statement upgrade pending. (`Kairos/Stats/PACBayesCS.lean`)
- **Universal aCS-sharp** (no σ ≤ 1 restriction): depends on time-uniform CLT.

### Already shipped (v0.6.0, axiom-clean) — 2026-04-25 + 2026-04-26 batches
- **Tier 8 tactic suite (5 tactics)**: `pythia` headline domain hammer + `stats_ineq` inequality hammer + `prob_simp` / `pdf_simp` probability normalization + `anytime_valid` Ville-closer hammer + `z3_check` cross-prover Phase 1 (Z3 oracle + linarith reconstruction). All tactics use the `@[X_lemma]` registry pattern.
- **Three Mathlib v4.28 gap closures (own-implementation)**: `OptionalStoppingUnbounded` (Williams §10.10 unbounded-τ), `BretagnolleHuberBinary` (binary-form, skips Pinsker), `AnytimeValid` Ville-closer hammer.
- **Tier 1 Bernstein** (`bernstein_of_subGamma`): closed via subGamma reparametrise; `@[stat_lemma]`-registered.
- **Tier 2 Wald-identity centered** (`wald_identity_centered_via_optional_stopping`) and **squared** (`wald_identity_squared_via_optional_stopping`): both axiom-clean, both apply OptionalStoppingUnbounded module.
- **Tier 7 matrix Bernstein scaffold**: Tropp's matrix Bernstein statement + 5-step dependency roadmap (HermitianFunctionalCalculus → Klein → Lieb → MGF → MatrixBernstein), excluded from AxiomAudit per honest-scaffold rule.
- **Cross-prover hammer Phase 1** (`Z3Check`): Z3 oracle + linarith reconstruction. Phase 2 (CVC5, EBMC, CBMC, Dafny, Vampire) roadmapped.
- **CI gate + community files**: per-branch lake build + per-file Lean sweep + axiom audit + CONTRIBUTING.md + CODE_OF_CONDUCT.md + README badges.

## Mathlib gaps we plan to cover

The following are statistical territory that Mathlib does not
currently include and that we plan to ship as part of the kairos-
stats-lean library. Priority order = decreasing community-utility
ratio (utility per closure effort).

### Tier 1 — direct extensions of existing Mathlib infrastructure
- [x] **Bernstein's inequality** for bounded random variables, in the `bernstein_of_subGamma` reparametrise form (v0.6.0). `@[stat_lemma]`-registered so `pythia` dispatches.
- [ ] **Bennett's inequality** (refined Bernstein for bounded RVs with explicit variance and range) — in flight via subagent against the bounded-implies-subGamma MGF Taylor-remainder bridge.
- [ ] **Freedman's inequality** (martingale Bernstein variant) — closure follows Bennett's bridge.
- [ ] **Bernstein-iid** + **Bernstein-martingale** — same bridge dependency.
- [ ] **Sub-exponential class** + **matrix Bernstein** (v0.7.0 Tier 7 scaffold exists with 5-step dependency roadmap).
- [ ] **Azuma-Hoeffding for unbounded but conditionally-bounded** martingales (Mathlib has the bounded case via `HasCondSubgaussianMGF`).

### Tier 2 — sequential statistics (Mathlib has nothing)
- [x] **Wald's SPRT** scaffold landed (ATH-604, PR #11). 4 statements: error_rates, wald_approximation, wald_wolfowitz_optimal (Aristotle-class), expected_sample_size.
- [x] **Wald's identity** scaffold landed (ATH-605, PR #11). 4 statements: m-parameterized + centered corollary closed locally + squared + exp form.
- [ ] **Sequential change detection** (CUSUM, Shewhart, Page's test).
- [ ] **E-detector framework** (Shin-Ramdas-Rinaldo 2024) — ATH-606 ticket filed.

### Tier 3 — empirical processes (Mathlib has fragments)
- [ ] **Glivenko-Cantelli theorem** in full generality (Mathlib has only narrow forms).
- [ ] **Donsker's theorem** (functional CLT for empirical distributions).
- [ ] **Vapnik-Chervonenkis (VC) inequality** + uniform LLN over VC classes.
- [ ] **Rademacher complexity** + symmetrization arguments.
- [ ] **Fixed-design Gaussian process bounds** (Dudley's chaining inequality).

### Tier 4 — stochastic approximation (Mathlib has nothing)
- [ ] **Robbins-Monro convergence theorem** for stochastic approximation.
- [ ] **Kiefer-Wolfowitz stochastic gradient descent** convergence.
- [ ] **Polyak-Ruppert averaging** + central limit theorem for SGD.

### Tier 5 — information theory + divergences (partial Mathlib coverage)
- [ ] **Hellinger distance** + total variation duality.
- [ ] **Rényi divergence** (parametric family of divergences).
- [ ] **f-divergence** general framework.
- [ ] **Pinsker's inequality** (KL bounds total variation).
- [ ] **Le Cam's two-point method** (lower bounds via TV distance).

### Tier 6 — Bayesian + exchangeable
- [ ] **De Finetti's theorem** (exchangeable sequences are mixtures of iid).
- [ ] **Kolmogorov's extension theorem** (full version with consistency conditions).
- [ ] **Conditional independence** + d-separation.
- [ ] **Posterior consistency** under regularity (Doob, Schwartz).

### Tier 7 — anytime-valid extensions beyond Phase C
- [ ] **Heavy-tailed anytime-valid CS** via Catoni-style estimators (sub-gamma scaffold already in place).
- [ ] **Vector-valued / matrix-valued anytime-valid CS** beyond the 1-d marginal Cauchy-Schwarz reduction.
- [ ] **Adaptive CS under continual model retraining** (ATH-591 long-term frame; the open problem from research).

### Tier 8 — tactic library (the moat)

The differentiator that makes kairos-stats-lean a *household name* in the
Lean / Mathlib community, not just another open-source library. Aesop is
"a household name" because of the *tactic*, not its lemma count.

- [ ] **`pythia`** — domain hammer over the kairos+mathlib lemma library, modeled on the lean4-skills 6-phase cycle engine (Plan → Work → Checkpoint → Review → Replan → Continue/Stop). Filed as ATH-608. Architecture in `docs/lean_lsp_mcp_setup.md`.
- [ ] **`kairos_grind`** — stats-domain extension of Mathlib's `grind` with normal forms for sub-Gaussian / sub-gamma / KL / MGF expressions and standard concentration-inequality unfolds. Filed as ATH-609.
- [ ] **`kairos_aesop`** — published aesop ruleset so users who never import kairos directly can opt in. Filed as ATH-610.
- [ ] **`#concentration` search command** — given a goal shape, return the tightest applicable concentration inequality (parallel to `#cs_families` / `#ville`). Filed as ATH-611.
- [ ] **Per-inequality apply tactics:** `bennett_apply`, `hoeffding_apply`, `freedman_apply`, `ville_apply`, `markov_apply`. One-tactic close of standard goals.

### Tier 9 — multi-agent infrastructure (the runtime)

Built on the lean-lsp-mcp + lean4-skills + OpenGauss substrate. This is what
makes the tactic library *self-improving* — auto-closes scaffold sorries
overnight rather than waiting for manual Aristotle submissions.

- [ ] **lean-lsp-mcp integration + self-hosted backends** — ATH-616. Wire 8 priority LSP tools, self-host loogle / leanfinder / hammer-premise to remove rate limits, pin REPL package at Lean 4.28.0. Setup smoke-tested 2026-04-25, `docs/lean_lsp_mcp_setup.md`.
- [ ] **`kairos.fleet.LeanProver`** — multi-agent cycle-driven proof closer (ATH-615). OpenGauss-style swarm: one child Claude Code session per scaffold sorry, each running the lean4-skills 6-phase cycle with `lean_multi_attempt` REPL mode + axiom gate + header fence. Stuck sorries re-queued to Aristotle with full LSP pre-flight bundle.
- [ ] **Aristotle-with-kairos-context bundle** — ATH-612. Package `Kairos.Stats.API` as Aristotle context so hardest-class theorems are solved with kairos lemmas in scope, not just Mathlib.

## Cross-domain candidate pool (sourced via sonnet subagent scans)

A rotating "external demand" feed — what practitioners across quant /
actuarial / physics / biology / ML / signal-processing / control are
asking for. Candidates are vetted before joining a tier:

- **Quant** (batch 2026-04-25 #1): Itô formula, Girsanov, Martingale Representation, CVaR coherence, Sklar copula, Kelly-Cover, Fisher-Tippett-Gnedenko, Pickands-Balkema-de Haan, Snell envelope (continuous-time), FTAP / NFLVR, Bachelier-Black-Scholes derivation chain.
- **Actuarial + statistical physics** (batch 2026-04-25 #1): Cramér-Lundberg ruin, Mack chain-ladder MSEP, Lindeberg-Feller triangular-array CLT, Kingman subadditive ergodic, Cramér's LDP, Gibbs variational principle, fluctuation-dissipation theorem.
- **Biology + natural sciences** (batch 2026-04-25 #1): Benjamini-Hochberg FDR, Galton-Watson extinction probability, Kaplan-Meier consistency, log-rank χ² asymptotic, Holm step-down FWER, Henderson BLUP, Kingman coalescent, Nadaraya-Watson consistency, Lan-DeMets alpha-spending, bootstrap consistency.
- **ML / AI** (batch 2026-04-25 #2 — pending).
- **Signal processing + control** (batch 2026-04-25 #2 — pending).
- **Actuarial life-tables + clinical biostatistics** (batch 2026-04-25 #2 — pending).

## Contribution strategy

Each tier is a multi-PR effort. The pattern:
1. **Module scaffold PR** — statements with honest sorries + math sketches in module docstrings. Establishes the API surface.
2. **Closure PR(s)** — proofs land via local Mathlib tactics, Aristotle (commercial prover, internal use only), or Lean community contributions.
3. **API integration PR** — each tier's headline theorems join `Kairos.Stats.API` once axiom-clean.
4. **Mathlib upstream PR** — once stable in our library, the closure-only versions go upstream so the broader Lean ecosystem inherits them.

Every theorem closes axiom-clean against `{propext, Classical.choice, Quot.sound}` before it joins `Kairos.Stats.API`. Anything in flight stays sorry'd in its source file with explicit math sketch, and is excluded from `Kairos.Stats.AxiomAudit`.

## How to contribute

External contributions welcome. The library is Apache-2.0, the Lean
4 / Mathlib v4.28.0 toolchain is pinned, and CI runs `lake build` +
the axiom audit on every push. A new theorem in any of the tiers
above starts a PR; the maintainer reviews + helps with proof closure
where Mathlib gaps make it hard.

## Status check

- v0.1.0 (Phase A): library is buildable + documented + CI-gated. ✓
- v0.2.0 (Phase B): aesop-grade tactic + DSL. ✓
- v0.3.0 (Phase C): Time-uniform CLT + PAC-Bayes + heavy-tailed (sub-gamma part DONE). ⚠ partial
- v0.4.0 (Tier 1): Bernstein + sub-exponential family.
- v0.5.0 (Tier 2): SPRT + Wald's identity + e-detector. ⚠ scaffold landed PR #11; closure in flight.
- v0.6.0 (Tier 8): tactic library — `pythia` / `kairos_grind` / `kairos_aesop` / `#concentration` / per-inequality apply tactics. The moat.
- v0.7.0 (Tier 9): multi-agent infra — `kairos.fleet.LeanProver` + Aristotle-with-kairos-context bundle + lean-lsp-mcp self-hosted backends. The runtime.
- v0.8.0+ (Tier 3-7): empirical processes, stochastic approximation, divergences, Bayesian, adaptive CS extensions; cross-domain candidates promoted from the pool above as practitioner demand surfaces.

The library is a long-running effort. Each version tag adds a
logical block of theorems, axiom-clean and CI-gated. The aim is to
be the canonical reference the Lean community reaches for in
sequential statistics and anytime-valid inference.
