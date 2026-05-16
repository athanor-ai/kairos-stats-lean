/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Credit Risk — complete toolkit

One import for credit risk modeling: CDS pricing, hazard rates,
credit spreads, Merton structural model, and default probability.

    import Pythia.Finance.CreditRisk

## Modules

* **CDS:** spread-hazard-recovery relationship, break-even pricing
* **Credit spread:** term structure, recovery rate monotonicity
* **Merton credit:** structural model (equity as call on firm value)
* **Default probability:** survival probability, hazard rate calibration
-/

import Pythia.Finance.Credit.CreditDefaultSwap
import Pythia.Finance.Credit.CreditSpread
import Pythia.Finance.Credit.CreditSpreadModel
import Pythia.Finance.Credit.MertonCredit
