# pythia simulation runner

Companion to the Lean theorems under `Pythia/<Domain>/*.lean`. Every
theorem ships with two layers:

- **Layer 0 (formal)**: kernel-checked Lean proof in
  `Pythia/<Domain>/Foo.lean`. Axiom-clean against
  `{propext, Classical.choice, Quot.sound}`.
- **Layer 1 (empirical)**: this directory. A runner call in
  `tools/sim/<domain>_<theorem>.py` runs:
  - 10 000 random Hypothesis-style draws (PBT)
  - a deterministic sweep over realistic parameter ranges
  - mutation testing: deliberately-wrong specs the runner
    expects to catch (vacuous-test guard).

Lean stays a proof assistant. Python owns numerics. Zero external
deps in this runner itself (stdlib + pytest only).

## Quickstart: write a runner for a new theorem

```python
# tools/sim/economics_cobb_douglas.py
from tools.sim.harness import Mutation, Strategy, floats, isclose, run_harness


def cobb_douglas_crts_spec(K, L, lam, alpha):
    lhs = (lam * K) ** alpha * (lam * L) ** (1 - alpha)
    rhs = lam * (K ** alpha * L ** (1 - alpha))
    return isclose(lhs, rhs, rtol=1e-9)


def _drop_lambda(K, L, lam, alpha):
    # Mutation: drop the lambda on the L factor; harness expects
    # this to fail at >= 5% of draws, otherwise the test set is
    # vacuous.
    lhs = (lam * K) ** alpha * L ** (1 - alpha)
    rhs = lam * (K ** alpha * L ** (1 - alpha))
    return isclose(lhs, rhs, rtol=1e-9)


def test_cobb_douglas_crts():
    result = run_harness(
        name="economics.cobb_douglas_crts",
        spec=cobb_douglas_crts_spec,
        strategy=Strategy(
            K=floats(1e-2, 1e6, log_scale=True),
            L=floats(1e-2, 1e6, log_scale=True),
            lam=floats(1e-2, 100.0, log_scale=True),
            alpha=floats(0.05, 0.95),
        ),
        mutations=(
            Mutation(name="drop_lambda_on_L", spec=_drop_lambda),
        ),
    )
    assert result.all_passed, result.summarize()
```

Run as a script: `python -m tools.sim.economics_cobb_douglas`.
Or via pytest: `pytest tools/sim/economics_cobb_douglas.py`.

## Parameter strategies

```python
floats(lo, hi)                 # uniform in [lo, hi]
floats(lo, hi, log_scale=True) # geometric in [lo, hi] (orders of magnitude)
ints(lo, hi)                   # inclusive integer range
choice("a", "b", "c")          # one of these values
```

## Tolerance helpers

```python
from tools.sim.harness import isclose, le

isclose(a, b, rtol=1e-9)  # wraps math.isclose with our defaults
le(a, b, atol=1e-6)       # `a <= b + atol` for inequality slack
```

## Output

`run_harness` returns a `HarnessResult`:

| field                | meaning                                              |
|----------------------|------------------------------------------------------|
| `pbt_passed`         | did all `n_pbt` random draws satisfy `spec`?         |
| `sweep_passed`       | did all sweep grid points satisfy `spec`?            |
| `mutations_caught`   | mutations that failed at >= their declared rate      |
| `mutations_missed`   | mutations that did NOT fail enough (BAD: vacuous)    |
| `first_pbt_failure`  | kwargs of the first PBT draw that violated `spec`    |
| `first_sweep_failure`| same shape, for the deterministic sweep              |
| `wall_seconds`       | wall-clock runtime                                   |
| `all_passed`         | True iff PBT + sweep + every mutation was caught     |

`result.to_json()` for CI artifact upload, `result.summarize()` for
terminal output.

## Layout convention

| Domain        | Lean module                    | Python runner                              |
|---------------|--------------------------------|---------------------------------------------|
| Economics     | `Pythia/Economics/Foo.lean`    | `tools/sim/economics_foo.py`                |
| Chemistry     | `Pythia/Chemistry/Bar.lean`    | `tools/sim/chemistry_bar.py`                |
| Bio           | `Pythia/Bio/Baz.lean`          | `tools/sim/bio_baz.py`                      |
| Engineering   | `Pythia/Engineering/Qux.lean`  | `tools/sim/engineering_qux.py`              |
| OR            | `Pythia/OR/Quux.lean`          | `tools/sim/or_quux.py`                      |
| Mathlib retag | `Pythia/MathlibTags.lean`      | `tools/sim/mathlib_tags_<theorem>.py`       |

## Running the full simulation suite

```bash
pytest tools/sim/ -v
```

Each `tools/sim/<domain>_<theorem>.py` file exposes a
`test_<theorem>()` pytest hook so the whole suite runs as a normal
test invocation. Use `python -m tools.sim.<domain>_<theorem>` for an
ad-hoc run with full 10 000-draw PBT + summary print.
