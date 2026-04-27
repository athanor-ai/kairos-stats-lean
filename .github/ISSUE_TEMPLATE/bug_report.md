---
name: Bug report
about: Report a problem with an existing theorem, runner, or tactic
title: "[bug] <module>: <one-line summary>"
labels: ["bug"]
---

## What broke

What you tried, what you expected, what actually happened.

## Reproduction

Minimal Lean snippet or runner invocation that reproduces. Paste the
full error / stderr.

```lean
import Pythia
example : ... := by pythia  -- reports: ...
```

or

```bash
python3 -m tools.sim.<domain>_<theorem>
# Output: ...
```

## Environment

- Lean toolchain (from `lean --version`):
- Mathlib commit (from `lake-manifest.json`):
- Pythia commit:
- Python version:
- OS:

## Suspected fix

If you've narrowed it down. Optional.
