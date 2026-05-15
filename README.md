# pythia

[![CI](https://github.com/athanor-ai/pythia/actions/workflows/lean-build.yml/badge.svg)](https://github.com/athanor-ai/pythia/actions/workflows/lean-build.yml)
[![Sim sweep](https://github.com/athanor-ai/pythia/actions/workflows/pythia-sim.yml/badge.svg)](https://github.com/athanor-ai/pythia/actions/workflows/pythia-sim.yml)
[![Lean](https://img.shields.io/badge/Lean-4.28.0-blue.svg)](https://github.com/leanprover/lean4/releases/tag/v4.28.0)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-blue.svg)](https://github.com/leanprover-community/mathlib4/releases/tag/v4.28.0)
[![License](https://img.shields.io/badge/License-Apache%202.0-green.svg)](LICENSE)
[![Axiom-clean](https://img.shields.io/badge/axioms-propext%20%2B%20Classical.choice%20%2B%20Quot.sound-success.svg)](Pythia/AxiomAudit.lean)

Pythia is a Lean 4 library of formally verified results in applied
mathematics and computer science. It provides 1100+ sorry-free theorems
spanning probability theory, hardware verification, networking
protocols, programming language semantics, actuarial science, numerical
optimization, information theory, mechanism design, distributed
systems, and quantitative finance. All proofs close under the standard
Lean 4 axiom set `{propext, Classical.choice, Quot.sound}`.


**1100+ sorry-free theorems** across 12 domains. 5 open conjectures
remain in `Pythia/Frontier/` (frontier matrix analysis, not on the CI gate).

<!-- pythia-stats-auto-begin -->
**Coverage**:
- 1742 theorem/lemma declarations in `Pythia/`
- 586 `@[stat_lemma]`-tagged theorems in the `pythia` tactic cascade
- 42 cross-domain theorems with Lean proof + Python sim runner across 16 domains (biology, chemistry, control, economics, engineering, finance, game_theory, info_theory, mathlib_tags, mechanical, numerical, optimal_transport, or, quantum, stochastic, thermodynamics)

Auto-tracked from [`tools/sim/theorem_manifest.py`](tools/sim/theorem_manifest.py) and the `Pythia/` source tree; regenerate via `python3 tools/refresh_readme_stats.py`.
<!-- pythia-stats-auto-end -->

## Motivation

[Mathlib](https://github.com/leanprover-community/mathlib4) provides
over 100,000 theorems covering the foundations of pure mathematics:
measure theory, topology, algebra, category theory. These foundations
are necessary but not sufficient for applied verification work.

Practitioners in engineering and applied science rely on named results
that do not appear in Mathlib or any other Lean library: the KKT
optimality conditions for constrained programs, Hamming distance bounds
for error-correcting codes, MTBF growth rates for synchronizer chains,
starvation-freedom guarantees for congestion-control protocols, or
type soundness for policy languages. These are standard textbook
theorems in their respective fields. They follow from Mathlib's
foundations but require substantial domain-specific formalization to
state and close.

Pythia fills this gap. It depends on Mathlib for the underlying
measure-theoretic and algebraic machinery, and contributes the applied
formalization layer: theorem statements that match the form
practitioners cite, closed proofs, domain-specific automation, and
paired empirical verification.

## Domains

| Module | Theorems | Coverage |
|--------|----------|----------|
| `Pythia.Probability` | 350 | Anytime-valid confidence sequences (Howard-Ramdas, betting), Ville's inequality, sub-Gaussian and sub-gamma concentration, Bernstein and Bennett inequalities, optional stopping, e-detectors, Robbins-Monro and Dvoretzky stochastic approximation |
| `Pythia.LanguageSemantics` | 134 | Cedar policy-language type soundness and coverage completeness, Palamedes generator correctness (totality, support characterization, data-structure invariants for lists, trees, natural numbers, STLC types and terms, stacks) |
| `Pythia.Actuarial` | 21 | Pareto, Weibull, log-normal loss distributions; Cramér-Lundberg ruin, Sparre Andersen renewal-theory ruin, Bornhuetter-Ferguson reserving |
| `Pythia.Numerical` | 76 | KKT necessary/sufficient conditions (Slater, Lagrangian sandwich), Picard-Lindelof, Lyapunov stability, Kahan compensated summation, Forward Euler truncation, IEEE-754 round-to-nearest, QR factorization, Weyl/Bauer-Fike eigenvalue bounds, gradient descent convergence, MatMul/Softmax/LayerNorm/Attention numerical error bounds (Higham Thm 3.1) |
| `Pythia.Bio` | 20 | Mass-action CRN conservation, phylogenetic likelihood, Lotka-Volterra, SIR threshold + Kermack-McKendrick final size, Wright-Fisher, Michaelis-Menten + Hill Emax saturation, PK/PD AUC + half-life + Bateman positivity, Hardy-Weinberg invariance, Kimura neutral fixation, SEIR R0 threshold, RCT identifiability |
| `Pythia.Networking` | 20 | Reno (AIMD) + New Reno fast retransmit recovery + CUBIC starvation-freedom under bounded acknowledgment, BBRv3 trace wellformedness + BDP cap, SACK pairwise disjointness, DCTCP + RED marking monotonicity, AIMD additive-increase rate, Bellman-Ford non-negativity, QUIC packet-number-space disjointness + 0-RTT replay-resistance, CoDel sojourn-time bound, split-horizon termination |
| `Pythia.MechanismDesign` | 12 | VCG efficiency + truthfulness (DSIC), second-price allocation, Vickrey individual rationality + truthfulness (2-bidder), Bulow-Klemperer corollary, VCG budget-balance counter-example, Myerson optimal reserve price (regular distributions), Condorcet winner uniqueness, first-price symmetric BNE bid |
| `Pythia.Distributed` | 11 | Paxos quorum-intersection (canonical) + single-decree safety + corollaries (no two leaders, prepare-response uniqueness), Lamport clock monotonicity + happens-before clock condition, vector-clock causality completeness, Byzantine quorum intersection, two-phase commit agreement + validity + coordinator-failure blocking |
| `Pythia.InformationTheory` | 9 | Shannon entropy non-negativity + log-card upper bound, channel capacity = sup mutual information, mutual-info nonneg via Gibbs (parametrized), source-coding lower bound (Kraft + Gibbs), data processing inequality (parametrized chain rule), Kraft inequality, AEP for Bernoulli, BSC capacity = log 2 - binEntropy(δ) |

All mainline theorems are sorry-free. Work-in-progress proofs live in
`Pythia/Frontier/` and do not affect the CI build gate.

## Installation

Add to `lakefile.lean`:

<!-- doctest: skip-reason: lakefile syntax (require), not a Lean program -->
```lean
require pythia from git
  "https://github.com/athanor-ai/pythia.git" @ "main"
```

Then `import Pythia` or any individual submodule. Mathlib is pulled
as a transitive dependency. Toolchain: Lean 4.28.0, Mathlib v4.28.0.

## Example

Ville's inequality for non-negative supermartingales, closed in one
tactic call:

```lean
import Pythia

open Pythia MeasureTheory

example
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ}
    (hsup : Supermartingale f 𝓕 μ) (hnn : ∀ t ω, 0 ≤ f t ω)
    (hint : Integrable (f 0) μ) {c : ℝ} (hc : 0 < c) :
    μ {ω | ∃ t, f t ω ≥ c} ≤ (∫ ω, f 0 ω ∂μ).toNNReal / c.toNNReal := by
  anytime_valid
```

## Tactics

Pythia registers twelve tactics into the Lean elaborator.

| Tactic | Scope |
|--------|-------|
| `pythia!` | Nine-rung hammer ladder (stat_simp, linarith, positivity, aesop, z3_check, cvc5_check, vampire_check, e_check, disprove). Returns the first successful closure. |
| `pythia?` | Same as `pythia!` with per-rung timing output. |
| `anytime_valid` | Ville-type bounds on non-negative supermartingales. |
| `stats_ineq` | Concentration and tail-bound inequalities. |
| `prob_simp` | Measure-theoretic rewriting (pushforwards, conditional expectations). |
| `z3_check` | Linear real arithmetic via Z3, reconstructed through `linarith`. |
| `cvc5_check` | Bit-vector arithmetic via CVC5, reconstructed through `bv_decide`. |
| `vampire_check` | First-order clausal logic via Vampire, reconstructed through `aesop`. |
| `e_check` | First-order clausal logic via E (backup to Vampire). |
| `disprove` | Counterexample search via Z3 satisfiability. |

The `@[stat_lemma]` attribute registers user-defined theorems into the
`pythia` dispatch surface, following the same pattern as Mathlib's
`@[simp]` and `@[gcongr]`.

External solvers serve as oracles only. Every solver verdict is
reconstructed into a Lean 4 tactic script that the kernel verifies
against `{propext, Classical.choice, Quot.sound}`. This follows the
architecture of CoqHammer (Czajka and Kaliszyk, JAR 2018), adapted
for Lean 4.

## Empirical verification

Each domain pairs formal proofs with a computational verification layer:

- **Hardware**: EBMC bounded model checking on SystemVerilog properties ([`tools/ebmc/`](tools/ebmc/))
- **Probability/statistics**: Hypothesis property-based testing, 10,000 draws per theorem ([`tools/sim/`](tools/sim/))
- **Networking**: telos multi-backend trace replay
- **Language semantics**: differential oracle testing across Cedar implementations

## Theorem retrieval

The repository includes a full-text search index over all 
declarations ([`tools/theorem_index.py`](tools/theorem_index.py)).
Given a natural-language query, the index returns ranked theorem
matches and generates a minimal `.lean` scaffold with only the
required imports.

## References

| If you want to | See |
|----------------|-----|
| Close a goal in one tactic call | [`examples/01_pythia_smoke.lean`](examples/01_pythia_smoke.lean) |
| Inspect the hammer ladder | [`examples/04_pythia_full_dispatch.lean`](examples/04_pythia_full_dispatch.lean) |
| Select the tightest tail bound | [`examples/05_tight_tail_calculator.lean`](examples/05_tight_tail_calculator.lean) |
| Run the MiniPythia benchmark | [`Pythia/Bench/README.md`](Pythia/Bench/README.md) |
| Contribute a theorem | [`CONTRIBUTING.md`](CONTRIBUTING.md) |
| Understand cross-prover dispatch | [`docs/sledgehammer_dispatch.md`](docs/sledgehammer_dispatch.md) |

## Axiom discipline

Every public theorem closes under the Lean 4 + Mathlib axiom set
`{propext, Classical.choice, Quot.sound}`. No `sorry`, no added
axioms. Verify any theorem locally:

```lean
import Pythia
#print axioms Pythia.ville_supermartingale
```

Full audit: [`docs/axiom_audit.md`](docs/axiom_audit.md).

## Acknowledgments

Pythia is built on [Lean 4](https://github.com/leanprover/lean4) and
[Mathlib](https://github.com/leanprover-community/mathlib4).

## License

Apache-2.0. See [`LICENSE`](LICENSE).

## Citation

```bibtex
@misc{pythia2026,
  title  = {Pythia: Applied Formal Verification for Lean 4},
  author = {Yang, Aidan Z. H. and {Athanor-AI}},
  year   = {2026},
  url    = {https://github.com/athanor-ai/pythia},
  note   = {Apache-2.0}
}
```

