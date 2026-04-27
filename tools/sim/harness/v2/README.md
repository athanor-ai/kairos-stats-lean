# harness/v2 — composable sim-runner primitives

A new sim is a ~20-line declaration. The harness wires together iid
generation, property checking, symmetry testing, Lean-vs-Python
differential checking, statistical replication, boundary targeting,
and counterexample replay.

## Design

Seven modules, each with a single responsibility:

| Module | Responsibility |
|---|---|
| `generators.py` | Parametric Hypothesis strategies for math objects |
| `properties.py` | Composable property checks (tail bound, identity, monotone, ...) |
| `metamorphic.py` | Symmetry relations the harness auto-checks (homogeneous, permutation-invariant, ...) |
| `statistical.py` | Wilson + Clopper-Pearson CIs and binomial CI gate |
| `targeting.py` | Wrappers that bias Hypothesis toward boundary regions |
| `differential.py` | Lean `#eval` vs Python comparison, skips gracefully when lake absent |
| `replay.py` | Counterexample persistence + regression replay |

The `Sim` dataclass in `__init__.py` composes all seven.

## Quickstart: write a v2 Sim

See `tests/test_smoke.py` for the canonical worked example. The minimal
form is:

```python
from tools.sim.harness.v2 import Sim
from tools.sim.harness.v2.generators import real_in
from tools.sim.harness.v2.properties import identity

my_sim = Sim(
    name="domain.theorem_name",
    lean_module="Pythia.Domain.TheoremName",
    generator=real_in(-1e6, 1e6),
    property=lambda x: identity(lambda x: x + 0, lambda x: x, {"x": x}),
    replications=500,
)

# pytest: def test_my_sim(): my_sim.run()
```

Add optional components as needed:

```python
from tools.sim.harness.v2.metamorphic import homogeneous
from tools.sim.harness.v2.differential import DifferentialCheck
import hypothesis.strategies as st

my_sim = Sim(
    name="domain.theorem_name",
    lean_module="Pythia.Domain.TheoremName",
    generator=real_in(0.1, 100.0),
    property=lambda x: x + 0 == x,
    symmetries=[
        homogeneous(
            fn=lambda x: x + 0,
            arg_names=["x"],
            factor_strategy=real_in(0.5, 5.0),
            exponent=1,
            base_strategy=st.fixed_dictionaries({"x": real_in(0.1, 10.0)}),
        ),
    ],
    differential=DifferentialCheck(
        lean_decl="{x} + 0",
        python_fn=lambda x: x + 0.0,
        inputs={"x": 42.0},
    ),
    statistical_assertion={"claimed_prob": 0.01, "ci_level": 0.99},
    replications=1000,
)
```

## Generators

```python
positive_real()                         # (0, 1e6]
real_in(lo, hi)                         # uniform [lo, hi]
bounded_iid(lo, hi, n)                  # list of n iid draws
sub_gaussian_sample(sigma, n)           # N(0, sigma^2) bounded draws
sub_gamma_sample(variance, scale, n)    # sub-Gamma draws
sample_path_supermartingale(steps, drift_max)  # downward random walk
random_ode_initial(state_dim)           # R^state_dim in [-10, 10]
random_density(simplex_dim)             # probability vector
random_stochastic_matrix(d)             # row-stochastic d x d matrix
production_inputs(alpha, K, L)          # Cobb-Douglas inputs dict
```

## Properties

```python
tail_bound(samples, threshold, claimed_bound)
identity(lhs_fn, rhs_fn, inputs, tolerance=1e-9)
monotone(fn, base_inputs, arg, lo=None, hi=None)
convergence(sequence_fn, target, n_steps, rate=None)
martingale_property(path, filtration_fn=None)
ergodic_match(time_average, space_average, tolerance=1e-3)
```

## Symmetries (metamorphic relations)

```python
homogeneous(fn, arg_names, factor_strategy, exponent, base_strategy)
permutation_invariant(fn, arg_names, base_strategy)
time_reversal_invariant(fn, path_strategy)
bilinear(fn, arg1, arg2, base_strategy, scalar_strategy)
subadditive(fn, arg_names, base_strategy)
limit_case(fn, arg, limit_value, expected_form_fn, base_strategy)
```

## Statistical CIs

```python
wilson_ci(successes, n, level=0.99)         -> (lower, upper)
clopper_pearson_ci(successes, n, level=0.99) -> (lower, upper)
binomial_ci_check(violations, n, claimed_prob) -> bool
```

## Differential check

`lean_eval_matches_python(lean_decl, python_fn, inputs)` invokes
`lake env lean` via subprocess, parses the `#eval` output, and
compares to the Python function. Skips gracefully (returns True with
a warning) when `lake` is not on PATH, so CI on environments without
Lean still runs.

`DifferentialCheck(lean_decl, python_fn, inputs, tolerance)` is the
dataclass form consumed by `Sim`.

## Counterexample replay

Failing examples are auto-persisted to
`tools/sim/counterexamples/<sim_name>/seed_<hash>.json` and replayed
on every subsequent `Sim.run()`. Use `replay_corpus(sim_name, fn)` to
replay manually in a pytest test. Import `replay_corpus_fixture` from
`tools.sim.harness.v2.replay` (or a `conftest.py`) for fixture form.

## v1 compatibility

`tools/sim/harness.py` is unchanged. Imports of the form
`from tools.sim.harness import run_harness` continue to work via the
`harness/__init__.py` shim.

## Running the v2 tests

```bash
pytest tools/sim/harness/v2/tests/ -v
```
