/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pythia.MechanismDesign — umbrella import

Mechanism-design theorems from auction theory and social choice.

## Modules

* `SecondPrice`      — SPA allocation efficiency + Vickrey individual rationality.
* `BulowKlemperer`   — Bulow-Klemperer augmented auction inequality.
* `VCGCounter`       — VCG budget-balance failure counter-example.

Note: `Basic` (vcg_efficiency closed by Aristotle run 8fa0bd39) is imported
separately via `Pythia.MechanismDesign.Basic` once that run completes.
-/
import Pythia.MechanismDesign.SecondPrice
import Pythia.MechanismDesign.BulowKlemperer
import Pythia.MechanismDesign.VCGCounter
