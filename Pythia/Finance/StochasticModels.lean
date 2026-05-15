/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stochastic Models — complete toolkit

One import for stochastic process models used in quantitative finance:
geometric Brownian motion, Heston stochastic volatility, Merton
jump-diffusion, Ornstein-Uhlenbeck, and FTAP.

    import Pythia.Finance.StochasticModels

## Modules

* **GBM:** geometric Brownian motion (log-normal dynamics)
* **Heston:** stochastic volatility, long-run variance, CIR process
* **Merton:** jump-diffusion, compensated drift, total variance
* **OU:** Ornstein-Uhlenbeck mean-reversion
* **FTAP:** First Fundamental Theorem of Asset Pricing (no-arb → EMM)
* **Stochastic discount:** pricing kernel, risk-neutral valuation
-/

import Pythia.Finance.GeometricBrownianMotion
import Pythia.Finance.HestonLongRunVariance
import Pythia.Finance.MertonJumpDiffusion
import Pythia.Finance.OrnsteinUhlenbeck
import Pythia.Finance.FTAP
import Pythia.Finance.StochasticDiscount
import Pythia.Finance.ItoDiscrete
import Pythia.Finance.VarianceSwap
import Pythia.Finance.RiskNeutralMeasure
