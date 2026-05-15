/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Portfolio Theory — complete toolkit

One import for portfolio construction, optimization, and performance
attribution: CAPM, Markowitz frontier, efficient frontier, Kelly
criterion, risk parity, factor models, and performance ratios.

    import Pythia.Finance.PortfolioTheory

## Modules

* **CAPM:** beta, security market line, zero-beta return, R-squared
* **Markowitz:** mean-variance frontier, efficient frontier
* **Kelly:** optimal position sizing for log-wealth maximization
* **Risk parity:** equal risk contribution, portfolio rebalancing
* **Factor models:** return attribution, beta decomposition
* **Performance:** Sharpe, Sortino, Treynor, Calmar, Jensen's alpha,
  information ratio, risk-adjusted return
* **Utility:** mean-variance utility, hedge ratio
-/

import Pythia.Finance.CAPMBeta
import Pythia.Finance.MarkowitzFrontier
import Pythia.Finance.EfficientFrontier
import Pythia.Finance.PortfolioVariance
import Pythia.Finance.Kelly
import Pythia.Finance.RiskParity
import Pythia.Finance.PortfolioRebalancing
import Pythia.Finance.FactorModel
import Pythia.Finance.ReturnAttribution
import Pythia.Finance.BetaFromCorrelation
import Pythia.Finance.MeanVarianceUtility
import Pythia.Finance.HedgeRatioMinVar
import Pythia.Finance.MarginalRisk
import Pythia.Finance.SharpeRatio
import Pythia.Finance.SortinoRatio
import Pythia.Finance.TreynorRatio
import Pythia.Finance.CalmarRatio
import Pythia.Finance.JensenAlpha
import Pythia.Finance.InformationRatio
import Pythia.Finance.RiskAdjustedReturn
import Pythia.Finance.RiskReturnTradeoff
import Pythia.Finance.SharpeBridge
import Pythia.Finance.MertonPortfolioInsurance
import Pythia.Finance.PortfolioOptimality
