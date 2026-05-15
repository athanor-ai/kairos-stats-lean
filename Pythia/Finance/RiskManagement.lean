/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Risk Management — complete toolkit

One import for risk measurement, tail analysis, and volatility
estimation: VaR, Expected Shortfall, drawdown, kurtosis bounds,
convex/entropic risk measures, and realized volatility.

    import Pythia.Finance.RiskManagement

## Modules

* **VaR / ES:** Value-at-Risk, Expected Shortfall, coherent axioms
* **Convex risk:** translation invariance, positive homogeneity,
  sub-additivity, diversification benefit
* **Entropic risk:** exponential utility, KL divergence duality
* **Tail risk:** kurtosis bounds, Chebyshev/Cantelli, Cornish-Fisher
* **Volatility:** realized vol (Cauchy-Schwarz bound), Garman-Klass,
  GARCH update, volatility scaling, volatility smile
* **Drawdown:** max drawdown, tracking error, log-return inequality
-/

import Pythia.Finance.Risk.ValueAtRisk
import Pythia.Finance.Risk.ExpectedShortfall
import Pythia.Finance.Risk.ConvexRiskMeasure
import Pythia.Finance.Risk.EntropyRisk
import Pythia.Finance.Risk.KurtosisRisk
import Pythia.Finance.Risk.RealisedVolatility
import Pythia.Finance.Risk.GarmanKlassVolatility
import Pythia.Finance.Risk.GARCHUpdate
import Pythia.Finance.Risk.VolatilityScaling
import Pythia.Finance.Risk.VolatilitySmile
import Pythia.Finance.Risk.MaxDrawdown
import Pythia.Finance.Risk.TrackingError
import Pythia.Finance.Risk.LogReturnInequality
import Pythia.Finance.Risk.LeverageDecay
import Pythia.Finance.Portfolio.ConcentrationRisk
