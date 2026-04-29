/-
Basic types for the credit-assignment formal benchmark.

Defines: State, Action, Reward, Policy, ValueFn, QFn, environment MDP.
The goal is to be the thinnest possible scaffold on top of which each
rule (TD0, TDLambda, etc.) states its own update + invariants.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Pythia.Neuroscience.CreditAssignment

universe u v

/-- A finite state space for tabular analysis. -/
abbrev State := ℕ

/-- A finite action space. -/
abbrev Action := ℕ

/-- Real-valued reward. -/
abbrev Reward := ℝ

/-- A state-value function. -/
abbrev ValueFn := State → ℝ

/-- A state-action-value function. -/
abbrev QFn := State → Action → ℝ

/-- A policy is a mapping from states to probability distributions over
    actions. For the tabular case we treat it as a probability-mass
    function via `Mathlib.Probability.ProbabilityMassFunction`. -/
abbrev Policy := State → PMF Action

/-- Step size. Robbins-Monro conditions: `∑ α_t = ∞`, `∑ α_t² < ∞`.
    For a nonneg sequence, `¬ Summable seq` is equivalent to
    `∑' t, seq t = ∞`. -/
structure StepSize where
  seq      : ℕ → ℝ
  nonneg   : ∀ t, 0 ≤ seq t
  sumInf   : ¬ Summable seq
  sumSq    : Summable (fun t => seq t ^ 2)

/-- Discount factor, with the usual constraint `0 ≤ γ < 1`. -/
structure Discount where
  val      : ℝ
  nonneg   : 0 ≤ val
  lt_one   : val < 1

/-- Eligibility-trace decay parameter, `0 ≤ λ ≤ 1`. -/
structure Lambda where
  val       : ℝ
  nonneg    : 0 ≤ val
  le_one    : val ≤ 1

/-- A (discrete-time) trajectory of states, actions, and rewards. -/
structure Trajectory where
  states  : ℕ → State
  actions : ℕ → Action
  rewards : ℕ → Reward

/-- Bounded-reward assumption, used in every convergence proof. -/
structure BoundedReward (τ : Trajectory) where
  Rmax    : ℝ
  bound   : ∀ t, |τ.rewards t| ≤ Rmax

end Pythia.Neuroscience.CreditAssignment
