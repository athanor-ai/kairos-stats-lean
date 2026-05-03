/-
Pythia.Bio — computational biology theorems + machinery.

Pythia's comp-bio lane: chemical reaction networks, phylogenetic
likelihood, population genetics, stochastic biology. Mathlib has none
of this; pythia is the first Lean library to surface these results
in applied form.

## Modules

- `Pythia.Bio.MassAction`: chemical reaction network ODEs under
  mass-action kinetics. Wellposedness, nonneg-orthant invariance,
  conservation laws, detailed-balance equilibrium.
- `Pythia.Bio.Phylogenetics`: phylogenetic likelihood, Felsenstein's
  pruning algorithm correctness, Jukes-Cantor substitution model.

## Status

Scaffolds. Theorem signatures defined; proofs scaffold-sorry pending
Aristotle queue items 37-42.
-/

import Pythia.Bio.MassAction
import Pythia.Bio.Phylogenetics
import Pythia.Bio.PKPD
import Pythia.Bio.PopGenetics
import Pythia.Bio.SEIR
import Pythia.Bio.RCT
