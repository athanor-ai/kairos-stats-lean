/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Trade Execution — complete toolkit

One import for execution algorithms and transaction cost analysis:
Almgren-Chriss optimal execution, market impact models, transaction
costs, and currency hedging.

    import Pythia.Finance.Execution

## Modules

* **Almgren-Chriss:** optimal execution with linear temporary +
  permanent impact, antitone trajectory
* **Market impact:** square-root impact model, linear impact
* **Transaction costs:** proportional costs, bid-ask spread
* **Currency:** FX hedging, impermanent loss (DeFi)
-/

import Pythia.Finance.Execution.AlmgrenChrissExecution
import Pythia.Finance.Execution.MarketImpact
import Pythia.Finance.Execution.TransactionCost
import Pythia.Finance.Execution.CurrencyHedging
import Pythia.Finance.Execution.ImpermanentLoss
import Pythia.Finance.Execution.AlmgrenChrissOptimal
