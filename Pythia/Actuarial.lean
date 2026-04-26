/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pythia.Actuarial: Actuarial Loss Distribution Library

Standard continuous loss distribution families used in non-life actuarial
science and risk management, with moment and tail formulas formalised in Lean.

## Modules

* `Pythia.Actuarial.Pareto`    -- Pareto Type-I: tail, mean, variance, median
* `Pythia.Actuarial.Weibull`   -- Weibull: tail, mean, variance, median
* `Pythia.Actuarial.LogNormal` -- Log-normal: mean, variance, median, Chebyshev tail

See each module for theorem status and Aristotle queue candidates.
-/

import Pythia.Actuarial.Pareto
import Pythia.Actuarial.Weibull
import Pythia.Actuarial.LogNormal
