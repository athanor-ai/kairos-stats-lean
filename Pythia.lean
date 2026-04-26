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
import Pythia.WaldIdentity
import Pythia.SPRT
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
-- Counterexample-finder tactic — disprove (Phase 1, dual of z3_check).
import Pythia.Tactic.Disprove
import Pythia.Tactic.DisproveTest
-- Cascade routing regression suite (verifies pythia? rung naming).
import Pythia.Tactic.CascadeTest
-- Per-domain @[*_lemma] taxonomy (actuarial / numerical / bio /
-- bayes / control). Cross-cutting infra for v0.4+ domain expansion.
import Pythia.Tactic.DomainRegistry
-- Information theory (Bretagnolle-Huber binary form).
import Pythia.InfoTheory.BretagnolleHuberBinary
-- Measure theory infra (own-implement Mathlib gap).
import Pythia.MeasureTheory.OptionalStoppingUnbounded
-- Tier 7 scaffold — Tropp matrix Bernstein (sorries; see module
-- docstring for Lieb / Klein / matrix-MGF dependency roadmap).
import Pythia.MatrixBernstein

-- Tier 7 + queueing + path-measure additions
import Pythia.Queueing.ErlangB
import Pythia.MeasureTheory.PathMeasureRN
import Pythia.MatrixBernsteinFull
import Pythia.Control.LyapunovDiscrete
import Pythia.Queueing.LittlesLaw
import Pythia.MatrixLieb
import Pythia.Asymptotics.DeltaMethod
import Pythia.Asymptotics.DeltaMethodMulti
import Pythia.TimeSeries.WoldDecomposition
import Pythia.Risk.CVaR

-- MiniPythia benchmark suite (anytime-valid analogue of MiniF2F).
-- 30 theorems each closed by a single pythia tactic call. See
-- `Pythia/Bench/README.md` for the section breakdown and add-a-bench
-- recipe.
import Pythia.Bench.MiniPythia
