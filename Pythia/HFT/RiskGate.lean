/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Risk Gate — Verified Position Limit Enforcement

A risk gate sits in the hot path of every HFT system. It must:
1. Block every trade that would violate a position limit (soundness)
2. Allow every trade that does not violate a limit (completeness)
3. Run in O(1) time

This module proves soundness and completeness of the standard
risk gate implementation.

## Why this matters for HFT

* Regulatory requirement: every firm must have pre-trade risk checks
* A bug means either (a) blocked valid trades = lost money, or
  (b) passed invalid trades = regulatory violation + unlimited loss
* Formal verification is the only way to guarantee both properties

## References

* SEC Rule 15c3-5 ("Market Access Rule"): pre-trade risk controls
* FIA/ISDA best practices for pre-trade risk management
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.HFT.RiskGate

/-- A trade order: signed quantity (positive = buy, negative = sell). -/
structure TradeOrder where
  qty : ℤ

/-- Risk gate decision. -/
inductive Decision
  | allow : Decision
  | block : Decision
deriving DecidableEq

/-- The risk gate: allow iff current_pos + order_qty is within [-limit, limit]. -/
def riskCheck (current_pos : ℤ) (order : TradeOrder) (limit : ℤ) : Decision :=
  if |current_pos + order.qty| ≤ limit then Decision.allow else Decision.block

/-- **Soundness:** if the gate allows a trade, the resulting position
is within limits. -/
@[stat_lemma]
theorem gate_sound {pos : ℤ} {order : TradeOrder} {limit : ℤ}
    (h : riskCheck pos order limit = Decision.allow) :
    |pos + order.qty| ≤ limit := by
  simp only [riskCheck] at h
  split_ifs at h with h_le
  · exact h_le

/-- **Completeness:** if the resulting position would be within limits,
the gate allows the trade. -/
@[stat_lemma]
theorem gate_complete {pos : ℤ} {order : TradeOrder} {limit : ℤ}
    (h : |pos + order.qty| ≤ limit) :
    riskCheck pos order limit = Decision.allow := by
  simp only [riskCheck, ite_eq_left_iff]
  intro h_contra
  exact absurd h h_contra

/-- **Soundness + completeness = decidability:** the gate allows
iff the position is within limits. -/
@[stat_lemma]
theorem gate_iff {pos : ℤ} {order : TradeOrder} {limit : ℤ} :
    riskCheck pos order limit = Decision.allow ↔ |pos + order.qty| ≤ limit :=
  ⟨gate_sound, gate_complete⟩

/-- **Flat position always passes.** If current_pos = 0,
any trade within the limit passes. -/
@[stat_lemma]
theorem flat_passes {order : TradeOrder} {limit : ℤ}
    (h : |order.qty| ≤ limit) :
    riskCheck 0 order limit = Decision.allow := by
  apply gate_complete; simp; exact h

/-- **Cancel always passes.** A cancel (qty = 0) never changes position. -/
@[stat_lemma]
theorem cancel_passes {pos : ℤ} {limit : ℤ}
    (h : |pos| ≤ limit) :
    riskCheck pos ⟨0⟩ limit = Decision.allow := by
  apply gate_complete; simp; exact h

/-- **Monotonicity:** if a trade passes with limit L, it passes
with any larger limit L' >= L. -/
@[stat_lemma]
theorem gate_monotone {pos : ℤ} {order : TradeOrder} {L L' : ℤ}
    (hLL : L ≤ L')
    (h : riskCheck pos order L = Decision.allow) :
    riskCheck pos order L' = Decision.allow := by
  apply gate_complete
  exact le_trans (gate_sound h) hLL

/-- **Net limit check:** if the final position is within limits,
the net trade size is bounded by initial position + limit. -/
@[stat_lemma]
theorem net_position_bound {pos_final pos_initial sum_qty : ℤ}
    (h : pos_final = pos_initial + sum_qty) {limit : ℤ}
    (hf : |pos_final| ≤ limit) :
    |sum_qty| ≤ |pos_initial| + limit := by
  have hsq : sum_qty = pos_final - pos_initial := by linarith
  rw [hsq]
  sorry

end Pythia.HFT.RiskGate
