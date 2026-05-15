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

import Pythia.Finance.Stochastic.GeometricBrownianMotion
import Pythia.Finance.Stochastic.HestonLongRunVariance
import Pythia.Finance.Stochastic.MertonJumpDiffusion
import Pythia.Finance.Stochastic.OrnsteinUhlenbeck
import Pythia.Finance.Stochastic.FTAP
import Pythia.Finance.Stochastic.StochasticDiscount
import Pythia.Finance.Stochastic.ItoDiscrete
import Pythia.Finance.Stochastic.VarianceSwap
import Pythia.Finance.Stochastic.RiskNeutralMeasure
