-- Pythia: top-level entry point.
-- Generated from `ls Pythia/*.lean`. Excludes AxiomAudit (which is a
-- runtime-only #print-axioms harness, not a library module) and
-- VilleMathlibPR (Mathlib-PR-style draft; intentionally namespaced under
-- MeasureTheory rather than Pythia).
import Pythia.API
import Pythia.BenchTargets
import Pythia.Basic
import Pythia.BenchDefs
import Pythia.BettingCS
import Pythia.BettingStrategy
import Pythia.DeploymentDesign
import Pythia.ElegantUnification
import Pythia.EquivalenceBreak
import Pythia.GaussianRandomWalk
import Pythia.GaussianSmallBall
import Pythia.HowardRamdasCS
import Pythia.InformationTheoretic
import Pythia.InputQuantization
import Pythia.MatchingConstants
import Pythia.NewTargetsStubs
import Pythia.PhiTransform
import Pythia.PowerAnalysis
import Pythia.Quantization
import Pythia.Sharpness
import Pythia.MasterUpperBound
import Pythia.MasterLowerBound
import Pythia.StoppingRule
import Pythia.SubGamma
import Pythia.SubGaussianMG
import Pythia.VectorSharpness
import Pythia.VilleSupermartingale
-- Phase C scaffolds (sorries — see module docstrings for status).
import Pythia.MGFBoundedSubGamma
import Pythia.Bernstein
import Pythia.BernsteinTest
import Pythia.PACBayesCS
import Pythia.TimeUniformCLT
-- Tier 2 sequential-stats scaffolds (sorries — see docstrings).
import Pythia.Frontier.WaldIdentity
import Pythia.SPRT
-- Paper Theorem 1 asymptotic sharpness scaffold (Aristotle target —
-- 2 honest sorries on headline statements; helpers closed locally).
import Pythia.AsymptoticSharpness
-- Tier 2 e-detector scaffold (sorries — see module docstring for closure plans).
import Pythia.EDetector
-- Tactic layer (Phase B+).
import Pythia.Tactic.AnytimeValid
import Pythia.Tactic.AnytimeValidRegistry
import Pythia.Tactic.CSFamilyAttr
import Pythia.Tactic.CSFamilyRegistry
import Pythia.Tactic.VilleCmd
-- Tier 8 headline tactic (v0.6.0 in flight).
import Pythia.Tactic.Pythia
-- Domain inequality hammer.
import Pythia.Tactic.StatsIneq
import Pythia.Tactic.StatsIneqRegistry
-- Probability normalization simp-set.
import Pythia.Tactic.ProbSimp
import Pythia.Tactic.ProbSimpRegistry
import Pythia.Tactic.ProbSimpTest
-- ENNReal / probability normal-form curated simp-set (ATH-754).
import Pythia.Tactic.StatSimp
import Pythia.Tactic.StatSimpRegistry
import Pythia.Tactic.StatSimpTest
-- Cross-prover hammer Phase 1 — z3_check.
import Pythia.Tactic.Z3Check
import Pythia.Tactic.Z3CheckTest
-- Cross-prover hammer Phase 2 — cvc5_check (QF_BV primary, QF_LRA backup).
import Pythia.Tactic.CVC5Check
import Pythia.Tactic.CVC5CheckTest
-- Cross-prover hammer Phase 5 — vampire_check / e_check (FOL oracles).
import Pythia.Tactic.TPTPEncode
import Pythia.Tactic.VampireCheck
import Pythia.Tactic.VampireCheckTest
import Pythia.Tactic.ECheck
import Pythia.Tactic.ECheckTest
-- Domain calculator typeclass: generic Param/Output/Family/report
-- abstraction shared by all domain calculators (TightTail, etc.).
import Pythia.Tactic.DomainCalculator
-- Tail-bound calculator: pick the sharpest registered concentration
-- bound at concrete parameters. Goes beyond a closure tactic; this
-- is a domain calculator.
import Pythia.Tactic.TightTail
-- LLM-defense layer (ATH-718 Layer 3): lemma-existence guard.
import Pythia.Tactic.ValidateInvokedLemmas
import Pythia.Tactic.ValidateInvokedLemmasTest
-- LLM-defense layer (ATH-718 Layer 3): parametricity / concretization guard.
import Pythia.Tactic.FlagConcreteConstants
import Pythia.Tactic.FlagConcreteConstantsTest
-- LLM-defense layer (ATH-724 Guard C): unused-hypothesis guard.
import Pythia.Tactic.MinimizeHypotheses
import Pythia.Tactic.MinimizeHypothesesTest
-- LLM-defense layer (ATH-725 Guard D): type-shape sanity guard.
import Pythia.Tactic.ValidateTypes
import Pythia.Tactic.ValidateTypesTest
-- LLM-defense layer 2 (post-build): elaboration-level vacuity detection.
-- Provides #check_vacuity and #audit_module commands.
import Pythia.Tactic.VacuityCheck
-- Counterexample-finder tactic — disprove (Phase 1, dual of z3_check).
import Pythia.Tactic.Disprove
import Pythia.Tactic.DisproveTest
-- Cascade routing regression suite (verifies pythia? rung naming).
import Pythia.Tactic.CascadeTest
-- Hammer ladder orchestrator: `pythia!` / `pythia?` (ATH-753 / ATH-756 / ATH-758).
import Pythia.Tactic.PythiaBang
-- Per-domain @[*_lemma] taxonomy (actuarial / numerical / bio /
-- bayes / control). Cross-cutting infra for v0.4+ domain expansion.
import Pythia.Tactic.DomainRegistry
-- Information theory (Bretagnolle-Huber binary form).
import Pythia.InfoTheory.BretagnolleHuberBinary
-- ATH-938: discrete information theory (channel capacity, mutual info).
-- Basic.lean (shannonEntropy_nonneg) pending Aristotle ec7f9f8e.
import Pythia.InformationTheory
-- Measure theory infra (own-implement Mathlib gap).
-- Bridge: ae equality on rationals + ae continuity ⟹ ae equality on reals.
import Pythia.MeasureTheory.AeRealExtension
-- Tier 7 scaffold — Tropp matrix Bernstein (sorries; see module
-- docstring for Lieb / Klein / matrix-MGF dependency roadmap).
import Pythia.Frontier.MatrixBernstein

-- Tier 7 + queueing + path-measure additions
import Pythia.Queueing.ErlangB
import Pythia.Frontier.MeasureTheory.PathMeasureRN
import Pythia.Frontier.MatrixBernsteinFull
import Pythia.Control.LyapunovDiscrete
import Pythia.Queueing.LittlesLaw
import Pythia.Frontier.MatrixLieb
import Pythia.Asymptotics.DeltaMethod
import Pythia.Asymptotics.DeltaMethodMulti
import Pythia.TimeSeries.WoldDecomposition
import Pythia.Risk.CVaR

-- MiniPythia benchmark suite (anytime-valid analogue of MiniF2F).
-- 30 theorems each closed by a single pythia tactic call. See
-- `Pythia/Bench/README.md` for the section breakdown and add-a-bench
-- recipe.
import Pythia.Bench.MiniPythia

-- ATH-718 Layer 1: actuarial loss distributions (Pareto, Weibull, LogNormal).
-- Moment + tail formulas; see each module for Aristotle queue candidates.
import Pythia.Actuarial
-- ATH-718 Layer 1: numerical methods (Picard-Lindelöf, Lyapunov,
-- Kahan summation, KKT, Forward Euler LTE). Theorem signatures + scaffold sorries.
import Pythia.Numerical
-- ATH-718 Layer 1: computational biology (mass-action CRN ODEs,
-- phylogenetic likelihood). Scaffolds + Aristotle queue candidates.
import Pythia.Bio
-- ATH-870 expansion: physical chemistry quantitative laws.
import Pythia.Chemistry
-- ATH-718 Layer 1: hypothesis testing + multiple-testing corrections
-- (Wald, Bonferroni, Holm, BH-FDR).
import Pythia.HypothesisTest
import Pythia.BDG
-- Aristotle batch (2026-04-26): concentration + KL data-processing.
import Pythia.Bennett
import Pythia.MeasureTheory.ConditionalJensen
import Pythia.InfoTheory.DataProcessing
-- Aristotle batch (2026-04-26): stochastic approximation.
import Pythia.StochasticApproximation.RobbinsSiegmund
import Pythia.StochasticApproximation.RobbinsMonro
import Pythia.StochasticApproximation.Dvoretzky
-- Aristotle batch (2026-04-26): cross-domain headlines.
import Pythia.TimeSeries.NeweyWest
import Pythia.Control.LyapunovODE
import Pythia.Risk.CoherentMeasures
-- ATH-1120: compression moves + per-optimization proof objects.
-- Networking / protocol verification (ported from bbr3-starvation-bench).
import Pythia.Networking
-- Language semantics / type soundness (ported from kairos-cedar).
import Pythia.LanguageSemantics
-- Theoretical / computational neuroscience (cable equation, Nernst,
-- LIF, Hodgkin-Huxley gating, Shannon-Hartley, dopamine credit
-- assignment from credit-assignment-formal-bench).
import Pythia.Neuroscience
-- ATH-895: clinical-trials theorem coverage. Bonferroni union-bound
-- combiner for K-arm anytime-valid CS.
import Pythia.ClinicalTrials.MultiArmCS
-- Picard-Lindelöf global existence + uniqueness (graduated from
-- Frontier 2026-04-30 after Aristotle 26156985 + research's Zorn-chain
-- hint closed the existence sorry).
import Pythia.Numerical.PicardLindelof
-- Aristotle batch integration 2026-04-30: 8 sorry-free results.
import Pythia.Concentration.Cantelli
import Pythia.Asymptotics.Slutsky
import Pythia.Asymptotics.DeltaMethodScalar
import Pythia.SPRT.GSPRT
import Pythia.ClinicalTrials.Pocock
import Pythia.ClinicalTrials.Stratified
-- ATH-894 cross-vertical MCP router strategy-layer API.
-- `Pythia.Lookup` is the structured-JSON registry the router queries
-- for goal-class → theorem-template dispatch.
import Pythia.Lookup
-- ATH-894 router structural-certificate gate. `#pythia_validate T`
-- composes the four LLM-defense validators (ValidateInvokedLemmas /
-- FlagConcreteConstants / MinimizeHypotheses / ValidateTypes) into
-- a single command for `kairos.explain` to shell out against.
import Pythia.Tactic.PythiaValidate

-- Frontier Networking leaves imported by other Frontier files; added so per-file sweep can find oleans.
import Pythia.Frontier.Networking.OnsetTheorem
-- Frontier Neuroscience CreditAssignment leaves imported by other Frontier files.
import Pythia.Frontier.Neuroscience.CreditAssignment.TD0
import Pythia.Frontier.Neuroscience.CreditAssignment.ActorCritic

-- Sparre Andersen renewal-theory generalization of Cramér-Lundberg.
import Pythia.SparreAndersen

-- Frontier survival analysis (Cox proportional hazards consistency).
import Pythia.Frontier.Survival.Defs
import Pythia.Frontier.Survival.CoxConsistency

-- Frontier Lundberg ruin (1 measure-theoretic sorry on supermartingale construction).
import Pythia.Frontier.Lundberg

-- Mechanism design: auction theory + social choice (ATH-939 easy tier).
import Pythia.MechanismDesign

-- ATH-940 distributed systems theorem library (Paxos, Lamport, 2PC).
-- Basic.lean (paxos_quorum_intersection) added when Aristotle starter returns.
import Pythia.Distributed

-- ATH-1267 quant-finance sprint (no-arb, derivatives, risk, capital
-- structure, CAPM, term structure). All sorry-free.
-- Finance (reorganized into workflow subfolders)
import Pythia.Finance.All
import Pythia.Finance.Credit.CreditDefaultSwap
import Pythia.Finance.Credit.CreditSpread
import Pythia.Finance.Credit.HazardRate
import Pythia.Finance.Credit.MertonCredit
import Pythia.Finance.CreditRisk
import Pythia.Finance.Execution
import Pythia.Finance.Execution.AlmgrenChrissExecution
import Pythia.Finance.Execution.AlmgrenChrissOptimal
import Pythia.Finance.Execution.CurrencyHedging
import Pythia.Finance.Execution.ImpermanentLoss
import Pythia.Finance.Execution.MarketImpact
import Pythia.Finance.Execution.TransactionCost
import Pythia.Finance.Execution.TWAPSchedule
import Pythia.Finance.FixedIncome
import Pythia.Finance.FixedIncome.AnnuityFactor
import Pythia.Finance.FixedIncome.BondPriceYield
import Pythia.Finance.FixedIncome.BondZeroCoupon
import Pythia.Finance.FixedIncome.BootstrapYieldCurve
import Pythia.Finance.FixedIncome.CompoundInterest
import Pythia.Finance.FixedIncome.ContinuousDividendForward
import Pythia.Finance.FixedIncome.ConvexityDuration
import Pythia.Finance.FixedIncome.DiscountFactor
import Pythia.Finance.FixedIncome.ForwardPrice
import Pythia.Finance.FixedIncome.ForwardRateParity
import Pythia.Finance.FixedIncome.FxForward
import Pythia.Finance.FixedIncome.MacaulayDuration
import Pythia.Finance.FixedIncome.Perpetuity
import Pythia.Finance.FixedIncome.VasicekBondPrice
import Pythia.Finance.FixedIncome.VasicekShortRate
import Pythia.Finance.FixedIncome.YieldFromPrice
import Pythia.Finance.FixedIncome.YieldCurveConstraints
import Pythia.Finance.Fundamentals
import Pythia.Finance.Fundamentals.AutocorrelationReturn
import Pythia.Finance.Fundamentals.CointegrationResidual
import Pythia.Finance.Fundamentals.DividendDiscountModel
import Pythia.Finance.Fundamentals.GordonGrowth
import Pythia.Finance.Fundamentals.ModiglianiMiller
import Pythia.Finance.Fundamentals.NetPresentValue
import Pythia.Finance.HFT.Checksum
import Pythia.Finance.HFT.FastMath
import Pythia.Finance.HFT.FixedPoint
import Pythia.Finance.HFT.AuctionMechanism
import Pythia.Finance.HFT.ChecksumSpec
import Pythia.Finance.HFT.FairValueEstimator
import Pythia.Finance.HFT.FixedPointStrong
import Pythia.Finance.HFT.LatencyBound
import Pythia.Finance.HFT.MarketMaking
import Pythia.Finance.HFT.FixedPointEMA
import Pythia.Finance.HFT.Latency
import Pythia.Finance.HFT.MatchingEngine
import Pythia.Finance.HFT.Microstructure
import Pythia.Finance.HFT.OrderBook
import Pythia.Finance.HFT.OrderBookStrong
import Pythia.Finance.HFT.PositionTracker
import Pythia.Finance.HFT.SignalCombination
import Pythia.Finance.HFT.SlippageModel
import Pythia.Finance.HFT.TradingSession
import Pythia.Finance.HFT.OrderBookInvariant
import Pythia.Finance.HFT.RiskGate
import Pythia.Finance.HFT.SPSCQueue
import Pythia.Finance.OptionPricing
import Pythia.Finance.Options.AsianOption
import Pythia.Finance.Options.BachelierTerminal
import Pythia.Finance.Options.BarrierOption
import Pythia.Finance.Options.BlackFuturesOption
import Pythia.Finance.Options.BlackScholesCallClosedForm
import Pythia.Finance.Options.BlackScholesGreeks
import Pythia.Finance.Options.GreeksBound
import Pythia.Finance.Options.BlackScholesIntrinsicLower
import Pythia.Finance.Options.BlackScholesPDE
import Pythia.Finance.Options.CRRBinomialStep
import Pythia.Finance.Options.CallPriceBounds
import Pythia.Finance.Options.CallPriceUpperBound
import Pythia.Finance.Options.DeltaHedging
import Pythia.Finance.Options.LookbackOption
import Pythia.Finance.Options.NoArbitrageBounds
import Pythia.Finance.Options.OptionPayoff
import Pythia.Finance.Options.OptionTimePremium
import Pythia.Finance.Options.PutCallParity
import Pythia.Finance.Options.PutCallParityDividend
import Pythia.Finance.Portfolio.BetaFromCorrelation
import Pythia.Finance.Portfolio.CAPMBeta
import Pythia.Finance.Portfolio.CalmarRatio
import Pythia.Finance.Portfolio.ConcentrationRisk
import Pythia.Finance.Portfolio.EfficientFrontier
import Pythia.Finance.Portfolio.FactorModel
import Pythia.Finance.Portfolio.FactorRiskModel
import Pythia.Finance.Portfolio.HedgeRatioMinVar
import Pythia.Finance.Portfolio.InformationRatio
import Pythia.Finance.Portfolio.JensenAlpha
import Pythia.Finance.Portfolio.Kelly
import Pythia.Finance.Portfolio.KellyOptimal
import Pythia.Finance.Portfolio.MarginalRisk
import Pythia.Finance.Portfolio.MarkowitzFrontier
import Pythia.Finance.Portfolio.MeanVarianceUtility
import Pythia.Finance.Portfolio.MertonPortfolioInsurance
import Pythia.Finance.Portfolio.PortfolioOptimality
import Pythia.Finance.Portfolio.PortfolioRebalancing
import Pythia.Finance.Portfolio.PortfolioVariance
import Pythia.Finance.Portfolio.ReturnAttribution
import Pythia.Finance.Portfolio.RiskAdjustedReturn
import Pythia.Finance.Portfolio.RiskParity
import Pythia.Finance.Portfolio.RiskParityOptimal
import Pythia.Finance.Portfolio.RiskReturnTradeoff
import Pythia.Finance.Portfolio.SharpeBridge
import Pythia.Finance.Portfolio.SharpeRatio
import Pythia.Finance.Portfolio.SortinoRatio
import Pythia.Finance.Portfolio.TangencyPortfolio
import Pythia.Finance.Portfolio.TreynorRatio
import Pythia.Finance.PortfolioTheory
import Pythia.Finance.Risk.ConvexRiskMeasure
import Pythia.Finance.Risk.EntropyRisk
import Pythia.Finance.Risk.ExpectedShortfall
import Pythia.Finance.Risk.GARCHUpdate
import Pythia.Finance.Risk.GarmanKlassVolatility
import Pythia.Finance.Risk.KurtosisRisk
import Pythia.Finance.Risk.LeverageDecay
import Pythia.Finance.Risk.LogReturnInequality
import Pythia.Finance.Risk.MaxDrawdown
import Pythia.Finance.Risk.MovingAverage
import Pythia.Finance.Risk.RealisedVolatility
import Pythia.Finance.Risk.TrackingError
import Pythia.Finance.Risk.ValueAtRisk
import Pythia.Finance.Risk.VolatilityScaling
import Pythia.Finance.Risk.VolatilitySmile
import Pythia.Finance.RiskManagement
import Pythia.Finance.Stochastic.FTAP
import Pythia.Finance.Stochastic.GeometricBrownianMotion
import Pythia.Finance.Stochastic.GBMProperties
import Pythia.Finance.Stochastic.HestonLongRunVariance
import Pythia.Finance.Stochastic.HestonProperties
import Pythia.Finance.Stochastic.ItoDiscrete
import Pythia.Finance.Stochastic.MertonJumpDiffusion
import Pythia.Finance.Stochastic.OrnsteinUhlenbeck
import Pythia.Finance.Stochastic.RiskNeutralMeasure
import Pythia.Finance.Stochastic.StochasticDiscount
import Pythia.Finance.Stochastic.VarianceSwap
import Pythia.Finance.StochasticModels
import Pythia.Finance.Z3AuxiliaryDemo
import Pythia.GameTheory.AuctionTheory
import Pythia.GameTheory.CooperativeGame
import Pythia.GameTheory.NashEquilibrium
import Pythia.LanguageSemantics.Palamedes.Data.Tree
import Pythia.Optimization.ADMM
import Pythia.Optimization.AcceleratedGradient
import Pythia.Optimization.CoordinateDescent
import Pythia.Optimization.InteriorPoint
import Pythia.Optimization.KKT
import Pythia.Optimization.LBFGS
import Pythia.Optimization.MirrorDescent
import Pythia.Optimization.ProjectedGradient
import Pythia.Optimization.StochasticGradient
import Pythia.Optimization.SubgradientMethod
-- Actuarial
import Pythia.Actuarial.Test
-- Biology / epidemiology
import Pythia.Bio.MichaelisMentenSaturation
import Pythia.Bio.Population
-- Control theory
import Pythia.Control.Lyapunov
-- Economics
import Pythia.Economics.CAPM
import Pythia.Economics.CRRA
import Pythia.Economics.CobbDouglas
import Pythia.Economics.RiskNeutralCall
import Pythia.Economics.Walras
-- Engineering
import Pythia.Engineering.PowerDissipation
import Pythia.Engineering.RCTimeConstant
import Pythia.Engineering.SignalEnergy
-- Frontier: biology
import Pythia.Frontier.Bio.SIRThreshold
import Pythia.Frontier.Bio.WrightFisher
-- Frontier: chemistry
import Pythia.Frontier.Chemistry.ClausiusClapeyron
import Pythia.Frontier.Chemistry.Eyring
import Pythia.Frontier.Chemistry.VantHoff
-- Frontier: matrix analysis
import Pythia.Frontier.GoldenThompsonCommutative
import Pythia.Frontier.LogSumExp
import Pythia.Frontier.PeierlsBogoliubov
import Pythia.Frontier.TraceInequalities
-- Frontier: networking
import Pythia.Frontier.Networking.Environment
import Pythia.Frontier.Networking.ExtendedStateMachine
import Pythia.Frontier.Networking.KernelFidelity
import Pythia.Frontier.Networking.MultiFlow
import Pythia.Frontier.Networking.OnsetTheoremTrace
import Pythia.Frontier.Networking.PatchedFilter
-- Frontier: neuroscience
import Pythia.Frontier.Neuroscience.CreditAssignment.DistinguishabilityMatrix
import Pythia.Frontier.Neuroscience.CreditAssignment.MetaAnneal
-- Game theory
import Pythia.GameTheory.MinimaxTwoStrategyBound
-- Hardware
import Pythia.Hardware
-- Information theory
import Pythia.InfoTheory.BinaryEntropy
import Pythia.InfoTheory.HammingDistanceTriangle
-- Language semantics (Palamedes.Data.Tree excluded: Tree.noConfusion conflicts with Mathlib)
import Pythia.LanguageSemantics.Palamedes.Support
-- Mathlib tags
import Pythia.MathlibTags
-- Mechanical
import Pythia.Mechanical.HookeSpring
-- Mechanism design
import Pythia.MechanismDesign.Basic
-- Numerical analysis
import Pythia.Numerical.ErrorPropagation
import Pythia.Numerical.FPAssociativity
import Pythia.Numerical.FPNoiseConvergence
import Pythia.Numerical.FixedPointArith
import Pythia.Numerical.GradientAccumulation
import Pythia.Numerical.InnerProductError
import Pythia.Numerical.NewtonQuadraticIterPos
import Pythia.Numerical.PicardLindelofHelpers
-- Optimization
import Pythia.Optimization.BarrierFunction
import Pythia.Optimization.ConjugateFunction
import Pythia.Optimization.ConvexCombination
import Pythia.Optimization.DualityGap
import Pythia.Optimization.GradientDescentRate
import Pythia.Optimization.LagrangianDuality
import Pythia.Optimization.ProximalOperator
import Pythia.Optimization.NewtonStep
import Pythia.Optimization.StrongConvexity
-- Operations research
import Pythia.OR.LittlesLaw
-- Optimal transport
import Pythia.OptimalTransport.WassersteinDistanceNonneg
-- Quantum
import Pythia.Quantum.VonNeumannEntropyNonnegTwoState
-- Stochastic
import Pythia.Stochastic.ItoIsometryFiniteDim
-- Security (Cedar policy Lean shadows)
import Pythia.Security.EnvAllowlistSpec
import Pythia.Security.HaltReasonSpec
import Pythia.Security.TransformationClassSpec
-- Thermodynamics
import Pythia.Thermodynamics.CarnotEfficiencyUpperBound
