/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Fixed Income — complete toolkit

One import for bond pricing, yield curve construction, duration/convexity
risk, and interest rate models.

    import Pythia.Finance.FixedIncome

## Modules

* **Bond pricing:** zero-coupon, price-yield, yield from price
* **Yield curve:** bootstrap, forward rates, discount factors
* **Duration:** Macaulay duration, convexity, DV01
* **Interest rates:** compound interest, annuity factor, perpetuity
* **Rate models:** Vasicek short rate, Vasicek bond price
* **Forward:** forward price, forward rate parity, FX forward,
  continuous dividend forward
-/

import Pythia.Finance.FixedIncome.BondPriceYield
import Pythia.Finance.FixedIncome.BondZeroCoupon
import Pythia.Finance.FixedIncome.YieldFromPrice
import Pythia.Finance.FixedIncome.BootstrapYieldCurve
import Pythia.Finance.FixedIncome.DiscountFactor
import Pythia.Finance.FixedIncome.MacaulayDuration
import Pythia.Finance.FixedIncome.ConvexityDuration
import Pythia.Finance.Fundamentals.CompoundInterest
import Pythia.Finance.FixedIncome.AnnuityFactor
import Pythia.Finance.FixedIncome.Perpetuity
import Pythia.Finance.FixedIncome.VasicekShortRate
import Pythia.Finance.FixedIncome.VasicekBondPrice
import Pythia.Finance.FixedIncome.ForwardPrice
import Pythia.Finance.FixedIncome.ForwardRateParity
import Pythia.Finance.FixedIncome.FxForward
import Pythia.Finance.FixedIncome.ContinuousDividendForward
