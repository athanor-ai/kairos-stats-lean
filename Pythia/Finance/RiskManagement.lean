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

import Pythia.Finance.ValueAtRisk
import Pythia.Finance.ExpectedShortfall
import Pythia.Finance.ConvexRiskMeasure
import Pythia.Finance.EntropyRisk
import Pythia.Finance.KurtosisRisk
import Pythia.Finance.RealisedVolatility
import Pythia.Finance.GarmanKlassVolatility
import Pythia.Finance.GARCHUpdate
import Pythia.Finance.VolatilityScaling
import Pythia.Finance.VolatilitySmile
import Pythia.Finance.MaxDrawdown
import Pythia.Finance.TrackingError
import Pythia.Finance.LogReturnInequality
import Pythia.Finance.LeverageDecay
import Pythia.Finance.ConcentrationRisk
