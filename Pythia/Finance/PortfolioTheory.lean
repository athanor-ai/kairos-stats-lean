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

import Pythia.Finance.Portfolio.CAPMBeta
import Pythia.Finance.Portfolio.MarkowitzFrontier
import Pythia.Finance.Portfolio.EfficientFrontier
import Pythia.Finance.Portfolio.PortfolioVariance
import Pythia.Finance.Portfolio.Kelly
import Pythia.Finance.Portfolio.RiskParity
import Pythia.Finance.Portfolio.PortfolioRebalancing
import Pythia.Finance.Portfolio.FactorModel
import Pythia.Finance.Portfolio.ReturnAttribution
import Pythia.Finance.Portfolio.BetaFromCorrelation
import Pythia.Finance.Portfolio.MeanVarianceUtility
import Pythia.Finance.Portfolio.HedgeRatioMinVar
import Pythia.Finance.Portfolio.MarginalRisk
import Pythia.Finance.Portfolio.SharpeRatio
import Pythia.Finance.Portfolio.SortinoRatio
import Pythia.Finance.Portfolio.TreynorRatio
import Pythia.Finance.Portfolio.CalmarRatio
import Pythia.Finance.Portfolio.JensenAlpha
import Pythia.Finance.Portfolio.InformationRatio
import Pythia.Finance.Portfolio.RiskAdjustedReturn
import Pythia.Finance.Portfolio.RiskReturnTradeoff
import Pythia.Finance.Portfolio.SharpeBridge
import Pythia.Finance.Portfolio.MertonPortfolioInsurance
import Pythia.Finance.Portfolio.PortfolioOptimality
import Pythia.Finance.Portfolio.KellyOptimal
import Pythia.Finance.Portfolio.TangencyPortfolio
import Pythia.Finance.Portfolio.ConcentrationRisk
