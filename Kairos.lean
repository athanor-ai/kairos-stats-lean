-- Kairos-Stats: top-level entry point.
-- Generated from `ls Kairos/Stats/*.lean`. Excludes AxiomAudit (which is a
-- runtime-only #print-axioms harness, not a library module) and
-- VilleMathlibPR (Mathlib-PR-style draft; intentionally namespaced under
-- MeasureTheory rather than Kairos.Stats).
import Kairos.Stats.API
import Kairos.Stats.AristotleT0T1T2Bench
import Kairos.Stats.Basic
import Kairos.Stats.BenchDefs
import Kairos.Stats.BettingCS
import Kairos.Stats.BettingStrategy
import Kairos.Stats.DeploymentDesign
import Kairos.Stats.ElegantUnification
import Kairos.Stats.EquivalenceBreak
import Kairos.Stats.GaussianRandomWalk
import Kairos.Stats.GaussianSmallBall
import Kairos.Stats.HowardRamdasCS
import Kairos.Stats.InformationTheoretic
import Kairos.Stats.InputQuantization
import Kairos.Stats.MatchingConstants
import Kairos.Stats.NewTargetsStubs
import Kairos.Stats.PhiTransform
import Kairos.Stats.PowerAnalysis
import Kairos.Stats.Quantization
import Kairos.Stats.Sharpness
import Kairos.Stats.StoppingRule
import Kairos.Stats.SubGamma
import Kairos.Stats.SubGaussianMG
import Kairos.Stats.VectorSharpness
import Kairos.Stats.VilleSupermartingale
-- Phase C scaffolds (sorries — see module docstrings for status).
import Kairos.Stats.Bernstein
import Kairos.Stats.BernsteinTest
import Kairos.Stats.PACBayesCS
import Kairos.Stats.TimeUniformCLT
-- Tier 2 sequential-stats scaffolds (ATH-604/605, sorries — see docstrings).
import Kairos.Stats.WaldIdentity
import Kairos.Stats.SPRT
-- Tier 2 e-detector scaffold (ATH-606, sorries — see module docstring for closure plans).
import Kairos.Stats.EDetector
-- Tactic layer (Phase B+).
import Kairos.Stats.Tactic.AnytimeValid
import Kairos.Stats.Tactic.AnytimeValidRegistry
import Kairos.Stats.Tactic.CSFamilyAttr
import Kairos.Stats.Tactic.CSFamilyRegistry
import Kairos.Stats.Tactic.VilleCmd
-- Tier 8 headline tactic (ATH-608, v0.6.0 in flight).
import Kairos.Stats.Tactic.Pythia
-- Domain inequality hammer (ATH-628).
import Kairos.Stats.Tactic.StatsIneq
import Kairos.Stats.Tactic.StatsIneqRegistry
-- Probability normalization simp-set (ATH-630).
import Kairos.Stats.Tactic.ProbSimp
import Kairos.Stats.Tactic.ProbSimpRegistry
import Kairos.Stats.Tactic.ProbSimpTest
-- Cross-prover hammer Phase 1 — z3_check (ATH-633).
import Kairos.Stats.Tactic.Z3Check
import Kairos.Stats.Tactic.Z3CheckTest
-- Information theory (ATH-634-fallback: Bretagnolle-Huber binary form).
import Kairos.Stats.InfoTheory.BretagnolleHuberBinary
-- Measure theory infra (own-implement Mathlib gap, ATH-642).
import Kairos.Stats.MeasureTheory.OptionalStoppingUnbounded
-- Tier 7 scaffold — Tropp matrix Bernstein (sorries; see module
-- docstring for Lieb / Klein / matrix-MGF dependency roadmap).
import Kairos.Stats.MatrixBernstein
