# MiniPythia: a benchmark suite for the pythia hammer

`Pythia/Bench/MiniPythia.lean` is a reference set of 30 statistics
theorems each closed in a single tactic call from pythia's hammer
surface. The suite is the anytime-valid analogue of MiniF2F (Zheng
and Polu, 2021): one theorem per declaration, a 1-line docstring
naming the source domain, and a single closing tactic.

## What the benchmark covers

The 30 theorems are split into six sections, organized by which
pythia tactic closes them:

| Section | Closer          | Count | Domain                                    |
|---------|-----------------|-------|-------------------------------------------|
| 1       | `anytime_valid` | 6     | Ville bounds (countable, finite, infinite, unit-initial, using-witness) |
| 2       | `pythia` cascade | 6    | sub-Gaussian / sub-gamma concentration, Bernstein, HR-CS admissibility |
| 3       | `stats_ineq`    | 6     | sqrt monotonicity, log nonneg, eta-rate orderings |
| 4       | `prob_simp`     | 4     | PDF normalization, ENNReal coercions, probability-measure axioms |
| 5       | `z3_check`      | 4     | QF_LRA over `ℝ` (Z3 oracle, `linarith` reconstruction) |
| 6       | `pythia` plain  | 4     | dispatch through 2+ rungs of the cascade  |

Two §2 entries are marked `WIP` because the closing tactic depends on
a Phase C scaffold that hasn't shipped yet (the conditional-MGF
embedding in `Pythia.MGFBoundedSubGamma`). Each WIP entry uses
`sorry` and is annotated in its docstring.

## How to run the benchmark

From the repo root:

```bash
lake build Pythia.Bench.MiniPythia
```

or as a single-file check:

```bash
lake env lean Pythia/Bench/MiniPythia.lean
```

The file ends with a `#bench_summary` command that prints the section
breakdown:

```text
MiniPythia benchmark summary
  §1 anytime_valid Ville bounds                  : 6
  §2 sub-Gaussian / sub-gamma concentration      : 6
  §3 stats_ineq scalar inequalities              : 6
  §4 prob_simp probability rewriting             : 4
  §5 z3_check linear-real arithmetic             : 4
  §6 dispatch via plain `by pythia` (multi-rung) : 4
                                                 total: 30
```

The benchmark passes when `lake build` is clean and the only warnings
are the two `declaration uses 'sorry'` notices on the WIP entries.

## How to add a new bench item

Three steps:

1. Pick a section that matches the goal shape. If the goal looks like
   `μ {ω | ∃ t, M t ω ≥ c} ≤ <bound>` the section is §1. If it is a
   sub-Gaussian / sub-gamma tail with a closed-form rate, §2. If it
   is a scalar inequality (sqrt, log, monotonicity), §3. If it is a
   probability-rewriting or coercion goal, §4. If it is QF_LRA, §5.
   If you want pythia's dispatcher to pick the right closer
   automatically, §6.

2. Add the theorem under the section heading. Required form:

   ```lean
   /-- §X.Y One-line description naming the source. -/
   theorem name_of_theorem ... : ... := by <tactic>
   ```

   The closer is one of `anytime_valid`, `stats_ineq`, `prob_simp`,
   `z3_check`, or `pythia`. If your closer is a registered
   `@[stat_lemma]`, `@[anytime_valid_lemma]`, `@[stats_ineq]`, or
   `@[prob_simp]`, an `exact` of the lemma name is fine, the
   regression value is the target shape itself.

3. Update the section-count comment in the file docstring and the
   `#bench_summary` table in this README. The summary command's
   per-section counters key off declaration name prefixes
   (`ville_`, `subgaussian_`, `bernstein_`, `hr_`, `subgamma_`,
   `freedman_`, `sqrt_`, `log_`, `eta_`, `prob_`, `z3_`, `pythia_`),
   so pick a name whose prefix matches the section.

If the goal cannot be closed at the current commit, mark it `WIP` in
the docstring and use `sorry`. The bench shape still counts toward
the section total.

## Comparison with MiniF2F

MiniF2F is a competition-mathematics benchmark: 488 problems from
IMO, AIME, AMC, drawn from olympiad and undergraduate algebra. Its
closers are general-purpose ATPs and tactic combinations. MiniPythia
targets the orthogonal axis: anytime-valid sequential statistics,
concentration of measure, and probability rewriting. The two suites
share the one-theorem-per-declaration shape and the closing-tactic
convention (`by <tactic>`). They differ in domain coverage and in
what counts as a closing tactic. Pythia ships a dispatch ladder, see
`docs/sledgehammer_dispatch.md`, where MiniF2F evaluates a single
ATP at a time.

## References

Zheng, K., Han, J. M., Polu, S. (2021). MiniF2F: a cross-system
benchmark for formal Olympiad-level mathematics.
arXiv:2109.00110.

Polu, S., Han, J. M., Zheng, K., Baksys, M., Babuschkin, I.,
Sutskever, I. (2022). Formal mathematics statement curriculum
learning. arXiv:2202.01344.

Howard, S. R., Ramdas, A., McAuliffe, J., Sekhon, J. (2021).
Time-uniform Chernoff bounds via nonnegative supermartingales.
Probability Surveys.

Ville, J. (1939). Étude critique de la notion de collectif. Gauthier
Villars.
