/-
Pythia.HypothesisTest — hypothesis testing framework + multiple-testing
corrections.

Pythia's hypothesis-testing lane: named tests with formal α-bounds,
multiple-testing corrections, causal-inference primitives. Mathlib
has the central limit theorem + concentration but does not ship the
named hypothesis-test framework.

## Modules

- `Pythia.HypothesisTest.Wald`: Wald test α-bound under asymptotic
  normality (one-sided + two-sided).
- `Pythia.HypothesisTest.MultipleTesting`: Bonferroni / Holm /
  Benjamini-Hochberg corrections with FWER + FDR control theorems.

## Status

Scaffolds. Bonferroni is a one-line union-bound proof (easy close,
candidate for Sonnet subagent). Wald + Holm + BH are Aristotle queue
items 43-46.

## Future

- LRT (likelihood ratio test) chi-squared asymptotic distribution.
- Score test α-bound.
- KS / χ² goodness-of-fit α-bounds.
- Causal inference primitives (do-calculus, IV consistency).
-/

import Pythia.HypothesisTest.Wald
import Pythia.HypothesisTest.MultipleTesting
