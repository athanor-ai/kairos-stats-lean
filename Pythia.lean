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
-- Measure theory infra (own-implement Mathlib gap).
import Pythia.MeasureTheory.OptionalStoppingUnbounded
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
-- Kahan summation, KKT). Theorem signatures + scaffold sorries.
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
import Pythia.Hardware
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
-- ATH-894 cross-vertical MCP router strategy-layer API.
-- `Pythia.Lookup` is the structured-JSON registry the router queries
-- for goal-class → theorem-template dispatch.
import Pythia.Lookup
-- ATH-894 router structural-certificate gate. `#pythia_validate T`
-- composes the four LLM-defense validators (ValidateInvokedLemmas /
-- FlagConcreteConstants / MinimizeHypotheses / ValidateTypes) into
-- a single command for `kairos.explain` to shell out against.
import Pythia.Tactic.PythiaValidate
