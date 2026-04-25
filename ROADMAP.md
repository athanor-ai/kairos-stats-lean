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

## Mathlib gaps we plan to cover

The following are statistical territory that Mathlib does not
currently include and that we plan to ship as part of the kairos-
stats-lean library. Priority order = decreasing community-utility
ratio (utility per closure effort).

### Tier 1 — direct extensions of existing Mathlib infrastructure
- [ ] **Bernstein's inequality** for bounded random variables. Mathlib has Hoeffding (`measure_sum_ge_le_of_iIndepFun` in `Mathlib.Probability.Moments.SubGaussian`) but not the variance-aware Bernstein form. Sharper than Hoeffding when variance is small.
- [ ] **Sub-exponential class** + matrix Bernstein. Generalises the sub-gamma extension to operator-valued martingales.
- [ ] **Freedman's inequality** (martingale Bernstein variant).
- [ ] **Bennett's inequality** (refined Bernstein for bounded RVs with explicit variance and range).
- [ ] **Azuma-Hoeffding for unbounded but conditionally-bounded** martingales (Mathlib has the bounded case via `HasCondSubgaussianMGF`).

### Tier 2 — sequential statistics (Mathlib has nothing)
- [ ] **Wald's sequential probability ratio test (SPRT)**. Optimality (Wald-Wolfowitz), error-rate control, expected-stopping-time bounds.
- [ ] **Wald's identity** for stopping times.
- [ ] **Sequential change detection** (CUSUM, Shewhart, Page's test).
- [ ] **E-detector framework** (Shin-Ramdas-Rinaldo 2024) for nonparametric changepoint detection.

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
- v0.5.0 (Tier 2): SPRT + Wald's identity + e-detector.
- v0.6.0+ (Tier 3-7): empirical processes, stochastic approximation, divergences, Bayesian, adaptive CS extensions.

The library is a long-running effort. Each version tag adds a
logical block of theorems, axiom-clean and CI-gated. The aim is to
be the canonical reference the Lean community reaches for in
sequential statistics and anytime-valid inference.
