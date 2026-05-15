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

import Pythia.Finance.Options.OptionPayoff
import Pythia.Finance.Options.BlackScholesCallClosedForm
import Pythia.Finance.Options.BlackScholesGreeks
import Pythia.Finance.Options.BlackScholesIntrinsicLower
import Pythia.Finance.Options.BlackFuturesOption
import Pythia.Finance.Options.BachelierTerminal
import Pythia.Finance.Options.PutCallParity
import Pythia.Finance.Options.PutCallParityDividend
import Pythia.Finance.Options.CallPriceBounds
import Pythia.Finance.Options.CallPriceUpperBound
import Pythia.Finance.Options.CRRBinomialStep
import Pythia.Finance.Options.OptionTimePremium
import Pythia.Finance.Options.BarrierOption
import Pythia.Finance.Options.AsianOption
import Pythia.Finance.Options.LookbackOption
import Pythia.Finance.Options.BlackScholesPDE
import Pythia.Finance.Options.DeltaHedging
import Pythia.Finance.Options.NoArbitrageBounds
