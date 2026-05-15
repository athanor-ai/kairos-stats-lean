/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Corporate Finance Fundamentals — complete toolkit

One import for corporate finance building blocks: time value of money,
valuation models, capital structure, and cointegration.

    import Pythia.Finance.Fundamentals

## Modules

* **Time value:** compound interest, discount factor, NPV
* **Valuation:** Gordon growth, dividend discount model
* **Capital structure:** Modigliani-Miller
* **Econometrics:** cointegration residual, autocorrelation
-/

import Pythia.Finance.FixedIncome.CompoundInterest
import Pythia.Finance.Fundamentals.NetPresentValue
import Pythia.Finance.Fundamentals.GordonGrowth
import Pythia.Finance.Fundamentals.DividendDiscountModel
import Pythia.Finance.Fundamentals.ModiglianiMiller
import Pythia.Finance.Fundamentals.CointegrationResidual
import Pythia.Finance.Fundamentals.AutocorrelationReturn
