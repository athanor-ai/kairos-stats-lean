/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pythia.Finance — complete library

    import Pythia.Finance.All

imports every Finance workflow module. For targeted use, import
individual workflow modules instead:

* `Pythia.Finance.OptionPricing`  — BS, Greeks, exotics, payoff bounds
* `Pythia.Finance.PortfolioTheory` — CAPM, Markowitz, Kelly, risk parity
* `Pythia.Finance.RiskManagement`  — VaR, ES, vol, drawdown, kurtosis
* `Pythia.Finance.FixedIncome`     — bonds, yield curve, duration, rates
* `Pythia.Finance.StochasticModels` — GBM, Heston, Merton, FTAP
* `Pythia.Finance.CreditRisk`     — CDS, hazard rates, structural models
* `Pythia.Finance.Execution`      — Almgren-Chriss, impact, txn costs
* `Pythia.Finance.Fundamentals`   — NPV, Gordon growth, Modigliani-Miller
-/

import Pythia.Finance.OptionPricing
import Pythia.Finance.PortfolioTheory
import Pythia.Finance.RiskManagement
import Pythia.Finance.FixedIncome
import Pythia.Finance.StochasticModels
import Pythia.Finance.CreditRisk
import Pythia.Finance.Execution
import Pythia.Finance.Fundamentals
import Pythia.Finance.MovingAverage
import Pythia.Finance.Z3AuxiliaryDemo
import Pythia.Finance.HFT.FixedPoint
import Pythia.Finance.HFT.OrderBook
import Pythia.Finance.HFT.RiskGate
import Pythia.Finance.HFT.FastMath
import Pythia.Finance.HFT.Latency
import Pythia.Finance.HFT.Checksum
import Pythia.Finance.HFT.SPSCQueue
import Pythia.Finance.HFT.MatchingEngine
import Pythia.Finance.HFT.Microstructure
