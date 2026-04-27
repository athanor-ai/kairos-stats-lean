# Concentration cookbook

A quick reference: given a stats goal, which pythia tactic closes it,
and which inequality is the tactic actually using.

If you know the parameter regime but aren't sure which bound is
tightest, use `Pythia.TightTail.report` (see
`examples/05_tight_tail_calculator.lean`); this cookbook covers the
qualitative side (shape, scope, the tactic to invoke).

## Anytime-valid Ville bounds

**Goal shape**: `μ {ω | ∃ t, f t ω ≥ c} ≤ E[f₀] / c` for a non-negative
supermartingale `f`.

**Tactic**: `anytime_valid` (or `pythia` which dispatches to it).

**Inequality**: Ville's inequality (1939). The countable-time
generalization of Doob's maximal inequality. Pythia ships the
finite-horizon and unit-initial variants too.

**When to use**: any anytime-valid confidence sequence (CS), e-process
admissibility, or stopping-time claim that bounds a maximum over an
unbounded time index.

**Examples**: `examples/02_anytime_valid_smoke.lean`. Family registry
covers Howard-Ramdas, betting, vector, and asymptotic CS via
`@[cs_family]`.

## Sub-Gaussian / sub-gamma concentration

**Goal shape**: `μ {ω | f n ω ≥ τ} ≤ exp(-τ² / (2 V))` (sub-Gaussian)
or `exp(-τ² / (2 (V + b τ / 3)))` (sub-gamma / Bernstein).

**Tactic**: `pythia` (dispatches to `stats_ineq` then to the
`@[stat_lemma]` registry containing `bernstein_of_subGamma` and
friends).

**Inequality**: Chernoff bound applied to an exponential
supermartingale. Bernstein 1924 (bounded variant) and the sub-gamma
generalization in Boucheron-Lugosi-Massart 2013 §2.4.

**When to use**: bounded mean / variance estimators, finite-horizon
empirical-process tail bounds, MGF-driven concentration.

**Examples**: `Pythia/BernsteinTest.lean`.

## Linear-real arithmetic

**Goal shape**: `a ≤ b`, `a < b`, `a = b` over `ℝ` with linear
combinations of free variables and literal coefficients.

**Tactic**: `z3_check` (or `pythia` which falls through to it). On the
backup, `cvc5_check`. Both reconstruct via `linarith`.

**Inequality**: none. This is pure arithmetic. The oracle is a
search filter; the proof is constructed by Lean's Farkas-certificate
search in `linarith`.

**When to use**: side-conditions in larger proofs (e.g. "0 < c", "ε ≤ ε
+ δ", positivity of a denominator), parameter-arithmetic checks.

## First-order logic without arithmetic

**Goal shape**: `Prop` involving `∀`, `∃`, `∧`, `∨`, `¬`, `→`, `↔`,
`=` over uninterpreted predicates / functions; no arithmetic
operators.

**Tactic**: `vampire_check` (or `e_check` as backup; or `pythia` which
tries both). Reconstruction via `aesop` with the local hypotheses
promoted.

**Inequality**: none. Pure logic. Vampire and E find a refutation
proof in TPTP; aesop reconstructs an equivalent Lean term.

**When to use**: combinatorial side-conditions, axiom-instance
elaboration, set-membership / predicate-equivalence chains.

## Probability rewriting

**Goal shape**: equalities or simplifications involving
`MeasureTheory.Measure.map`, `condExp`, `lintegral`, `integral`,
pushforwards under measurable functions.

**Tactic**: `prob_simp` (or `pythia` which dispatches to it).

**Reduction**: a curated `simp` set of probability normalization
lemmas (measurable image, conditional expectation tower, density
calculus).

**When to use**: reducing one measure expression to another before
applying a downstream concentration bound.

## Optional stopping

**Goal shape**: `E[X_τ] = E[X_0]` for a martingale `X` and stopping
time `τ`.

**Tactic**: `pythia` (dispatches to the `@[stat_lemma]` registry,
finds Mathlib's `OptionalStopping.expectedValue_eq_expectedValue_zero`
plus pythia's unbounded variant in
`Pythia.MeasureTheory.OptionalStoppingUnbounded`).

**When to use**: Wald identities, e-detector wealth processes,
sequential-test analysis.

## Information theory

**Goal shape**: KL-divergence inequalities of the form
`KL(P ‖ Q) ≥ φ(d_TV(P, Q))` (Bretagnolle-Huber binary form,
2-norm-Csiszár forms, Pinsker's inequality).

**Tactic**: `pythia` (dispatches via the `Pythia` aesop ruleset,
`bretagnolleHuber_binary` is registered).

**Inequality**: Bretagnolle-Huber 1979 binary form, Csiszár's f-divergence inequalities, Pinsker's inequality.

**When to use**: minimax lower bounds, mutual-information bounds,
contraction of KL under Markov kernels.

## Choosing a bound at concrete parameters

If you have specific numbers (n = 1000, σ = 0.3, ε = 0.05, b = 1),
and want to know which inequality gives the tightest bound, run

```lean
#eval Pythia.TightTail.report (σ := 0.3) (b := 1) (n := 1000) (ε := 0.05)
```

This evaluates Hoeffding, Bernstein, sub-Gaussian, sub-gamma, Markov,
and Chebyshev numerically and prints them sorted, with the sharpest
labeled. See `Pythia.Tactic.TightTail`.

## Goal didn't close?

Try `pythia?`: the verbose form of the `pythia!` hammer ladder that
prints which rung of the 9-rung ladder closed the goal plus per-rung
wall-clock timing. If `pythia?` reports the close came from the
plain `pythia` rung (slot 5) via the generic Mathlib chain, you
may want to register the closer with `@[stat_lemma]` so future
calls short-circuit at the dedicated aesop ruleset (rung 4). See
[`docs/pythia_bang.md`](pythia_bang.md) for the full ladder table.

If `pythia` fails entirely:

1. Run `set_option trace.aesop true in pythia` to see what aesop
   tried.
2. Check `#stat_lemmas` for the registered closers.
3. Open an issue with the goal shape; if it's a recurring stats
   pattern not covered, we will register a closer.
