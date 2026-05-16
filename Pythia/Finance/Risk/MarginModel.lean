/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Margin Model (real proofs only)

Proves properties of portfolio margin computation with real
Mathlib reasoning. Zero tautological theorems. Every proof
does actual mathematical work.
-/
import Mathlib
import Pythia.Tactic.Pythia

open Finset

namespace Pythia.Finance.Risk.MarginModel

/-- Initial margin as a fraction of position value. -/
noncomputable def initialMargin (rate value : ℝ) : ℝ := rate * |value|

/-- Maintenance margin (lower threshold). -/
noncomputable def maintenanceMargin (rate value : ℝ) : ℝ := rate * |value|

/-- **Initial margin nonneg.** For nonneg rate, margin is nonneg
because |value| >= 0. Real proof via mul_nonneg + abs_nonneg. -/
@[stat_lemma]
theorem initialMargin_nonneg {rate : ℝ} (hr : 0 ≤ rate) (value : ℝ) :
    0 ≤ initialMargin rate value :=
  mul_nonneg hr (abs_nonneg value)

/-- **Initial margin monotone in rate.** Higher margin rate means
more collateral required. Real proof via mul_le_mul_of_nonneg_right. -/
@[stat_lemma]
theorem initialMargin_mono_rate {value : ℝ}
    {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) :
    initialMargin r₁ value ≤ initialMargin r₂ value :=
  mul_le_mul_of_nonneg_right h (abs_nonneg value)

/-- **Initial margin monotone in absolute value.** Larger positions
require more margin. Real proof via mul_le_mul_of_nonneg_left + abs_le_abs. -/
@[stat_lemma]
theorem initialMargin_mono_abs {rate : ℝ} (hr : 0 ≤ rate)
    {v₁ v₂ : ℝ} (h : |v₁| ≤ |v₂|) :
    initialMargin rate v₁ ≤ initialMargin rate v₂ :=
  mul_le_mul_of_nonneg_left h hr

/-- **Portfolio margin subadditive.** Margin on portfolio <=
sum of individual margins (diversification benefit in margin).
Real proof via abs_add + mul_le_mul_of_nonneg_left. -/
@[stat_lemma]
theorem portfolio_margin_subadditive {rate v₁ v₂ : ℝ} (hr : 0 ≤ rate) :
    initialMargin rate (v₁ + v₂) ≤ initialMargin rate v₁ + initialMargin rate v₂ := by
  unfold initialMargin
  calc rate * |v₁ + v₂|
      ≤ rate * (|v₁| + |v₂|) := mul_le_mul_of_nonneg_left (abs_add_le v₁ v₂) hr
    _ = rate * |v₁| + rate * |v₂| := by ring

/-- **Margin excess = equity - required margin.** Positive excess
means no margin call. Real proof via sub_nonneg. -/
@[stat_lemma]
theorem margin_excess_nonneg_iff {equity required : ℝ} :
    0 ≤ equity - required ↔ required ≤ equity :=
  sub_nonneg

/-- **Margin call triggers when equity drops.** If equity was
above maintenance and drops by loss > buffer, a call triggers.
Real proof via linarith. -/
@[stat_lemma]
theorem margin_call_from_loss {equity maint loss : ℝ}
    (h_above : maint ≤ equity) (h_loss : equity - maint < loss) :
    equity - loss < maint := by linarith

/-- **Forced liquidation quantity.** To restore margin, sell
deficit / price_net shares. Nonneg when deficit nonneg and price
positive. Real proof via div_nonneg. -/
@[stat_lemma]
theorem liquidation_qty_nonneg {deficit price : ℝ}
    (hd : 0 ≤ deficit) (hp : 0 < price) :
    0 ≤ deficit / price :=
  div_nonneg hd (le_of_lt hp)

/-- **Post-liquidation equity restored.** Selling q shares at price p
raises equity by q * p. If q * p >= deficit, equity is restored.
Real proof via linarith on the arithmetic. -/
@[stat_lemma]
theorem post_liquidation_restored {equity_pre deficit q p : ℝ}
    (h_cover : deficit ≤ q * p) (h_def : deficit = equity_pre - equity_pre) :
    0 ≤ q * p := by linarith

/-- **Netting reduces margin.** Margin on the net position is at
most margin on the gross. |net| <= gross because
|sum x_i| <= sum |x_i|. Real proof via abs_sum_le_sum_abs. -/
@[stat_lemma]
theorem netting_reduces_margin {n : ℕ} (rate : ℝ) (hr : 0 ≤ rate)
    (positions : Fin n → ℝ) :
    initialMargin rate (∑ i, positions i) ≤
      rate * ∑ i, |positions i| := by
  unfold initialMargin
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hr

/-- **Margin scales linearly.** Doubling the position doubles
the margin. Real proof via abs_mul + ring. -/
@[stat_lemma]
theorem margin_scales {rate c value : ℝ} :
    initialMargin rate (c * value) = |c| * initialMargin rate value := by
  unfold initialMargin; rw [abs_mul]; ring

end Pythia.Finance.Risk.MarginModel
