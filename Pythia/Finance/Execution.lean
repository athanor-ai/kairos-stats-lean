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

import Pythia.Finance.AlmgrenChrissExecution
import Pythia.Finance.MarketImpact
import Pythia.Finance.TransactionCost
import Pythia.Finance.CurrencyHedging
import Pythia.Finance.ImpermanentLoss
import Pythia.Finance.AlmgrenChrissOptimal
