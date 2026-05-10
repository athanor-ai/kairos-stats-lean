import Mathlib

-- Timing gate: reject optimizations that violate timing constraints.
-- Phase 2 infrastructure for kairos orchestrator.

structure TimingResult where
  critical_path_delay : ℝ
  timing_constraint : ℝ
  slack : ℝ
  h_slack : slack = timing_constraint - critical_path_delay

def meetsTiming (r : TimingResult) : Prop := r.slack ≥ 0

def timingImproves (before after : TimingResult) : Prop :=
  after.slack ≥ before.slack

/-
Optimization must not violate timing
-/
theorem timing_gate_rejects_violation (r : TimingResult) (h : r.slack < 0) :
    ¬meetsTiming r := by
  exact not_le_of_gt h

/-
If original meets timing and optimization improves slack, result meets timing
-/
theorem timing_gate_accepts_improvement (before after : TimingResult)
    (h_meets : meetsTiming before) (h_improves : timingImproves before after) :
    meetsTiming after := by
  exact le_trans h_meets h_improves

/-
Gate removal can only improve or maintain timing (never worsen)
-/
theorem gate_removal_timing_safe (original optimized : TimingResult)
    (h_fewer_gates : optimized.critical_path_delay ≤ original.critical_path_delay)
    (h_same_constraint : optimized.timing_constraint = original.timing_constraint)
    (h_meets : meetsTiming original) :
    meetsTiming optimized := by
  unfold meetsTiming at *;
  linarith [ original.h_slack, optimized.h_slack ]