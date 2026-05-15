/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option Pricing — complete toolkit

One import for everything you need to price, hedge, and analyze
options: Black-Scholes, Greeks, put-call parity, payoff bounds,
binomial trees, barrier/Asian/lookback exotics, and time premium.

    import Pythia.Finance.OptionPricing

## Modules

* **Payoffs:** vanilla call/put, max/min decomposition, payoff parity
* **Black-Scholes:** closed-form call, Greeks (delta, gamma, vega, theta, rho),
  intrinsic lower bound, futures variant, Bachelier (normal) model
* **Binomial:** CRR one-step replication with no-arb bounds
* **Put-call parity:** standard and dividend-adjusted
* **Bounds:** call price bounds, upper bounds, time premium
* **Exotics:** barrier (knock-in/out), Asian (arithmetic/geometric),
  lookback (floating-strike)
-/

import Pythia.Finance.OptionPayoff
import Pythia.Finance.BlackScholesCallClosedForm
import Pythia.Finance.BlackScholesGreeks
import Pythia.Finance.BlackScholesIntrinsicLower
import Pythia.Finance.BlackFuturesOption
import Pythia.Finance.BachelierTerminal
import Pythia.Finance.PutCallParity
import Pythia.Finance.PutCallParityDividend
import Pythia.Finance.CallPriceBounds
import Pythia.Finance.CallPriceUpperBound
import Pythia.Finance.CRRBinomialStep
import Pythia.Finance.OptionTimePremium
import Pythia.Finance.BarrierOption
import Pythia.Finance.AsianOption
import Pythia.Finance.LookbackOption
import Pythia.Finance.BlackScholesPDE
import Pythia.Finance.DeltaHedging
import Pythia.Finance.NoArbitrageBounds
