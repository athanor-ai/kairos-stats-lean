# Mutation testing

Pythia's Python tooling ships with two test-quality gates. Line
coverage (60% floor, enforced by `pytest-cov` in the
`Pythia simulation sweep` workflow) tells us which lines a test
touched. Mutation testing tells us whether those tests would
actually catch a bug in those lines: it rewrites the source one
small change at a time (flip a boolean, swap `+` for `-`, drop
a return statement, etc.) and checks that the test suite turns
red. A surviving mutant is a line the suite ran but did not
verify.

## How to run locally

The `[tool.mutmut]` block in `pyproject.toml` already lists the
paths and runner. To run the full sweep:

```bash
python3 -m pip install 'mutmut>=2.4'
mutmut run
```

This walks `tools/` (minus the per-theorem sim runners and test
files), generates one mutant per source-level expression, runs
`pytest tools/sim/ -x -q` against each, and records survive vs.
kill. First run on a clean tree takes 10 to 30 minutes depending
on hardware; subsequent runs are incremental.

To inspect the surviving mutants:

```bash
mutmut results
mutmut show <id>
```

`mutmut results` prints a summary plus the IDs of every
surviving, killed, timed-out, and suspicious mutant. `mutmut show
<id>` prints the diff of one mutant so you can see what the
mutation actually was. If the diff describes a real bug the
test suite missed, write a test that catches it.

## The 75% kill-rate floor

The CI workflow `.github/workflows/mutation-tests.yml` fails if
more than 25% of mutants survive (kill rate below 75%). Rationale:

1. 100% kill rate is unrealistic. There are always a handful of
   true equivalent mutants (a mutation that produces semantically
   identical code, e.g. `range(0, n)` vs `range(n)`) that no
   test can catch.
2. 75% gives genuine signal: it is well above the 50% you get
   from a suite that only tests happy paths.
3. The workflow is advisory, not blocking. It runs on PR + manual
   dispatch only and is deliberately NOT in
   `required_status_checks`. A maintainer reviews the
   `mutmut-stats.txt` artifact alongside the diff before merge.

## How to suppress a true equivalent mutant

If you have inspected a surviving mutant via `mutmut show <id>`
and confirmed it is a true equivalent (the mutation does not
change observable behaviour), there are two suppression paths:

1. **Refactor the source.** Often the cleaner fix. If `range(0,
   n)` and `range(n)` are equivalent, drop the `0`. The mutant
   stops being generated because the literal it would mutate is
   gone.

2. **Add a `# pragma: no mutate` comment** at end of the line
   mutmut should skip. This mirrors the `# pragma: no cover`
   convention used by `coverage.py`. Use sparingly and pair every
   suppression with a one-line comment explaining why the
   mutation is a true equivalent.

When in doubt, write the test rather than suppress. A mutation
that "feels like" an equivalent is almost always actually a test
gap.

## Why mutmut and not cosmic-ray or mutpy

`mutmut` is the simplest of the three for our use case. It is
Python-native, uses pytest as the runner, and stores incremental
state so re-runs after a small source edit are fast. `cosmic-ray`
is a more general framework but adds operational overhead we do
not need yet (job-server setup, per-mutant config). `mutpy` is
less actively maintained. If we outgrow `mutmut` (project size,
CI budget, more sophisticated mutation operators), `cosmic-ray`
is the planned upgrade path.
