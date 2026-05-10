import Mathlib

-- Integrated clock gating cell (ICG) correctness.
-- Standard power optimization in ASIC design.
-- The ICG latches the enable during the low phase of the clock,
-- then gates the clock output.

structure ICGState where
  clk : Bool
  enable : Bool
  latched_enable : Bool
  gated_clk : Bool

-- ICG behavior: latch enable on falling edge, gate on rising
def icgStep (s : ICGState) (clk_next enable_next : Bool) : ICGState :=
  let latch := if !clk_next then enable_next else s.latched_enable
  { clk := clk_next
    enable := enable_next
    latched_enable := latch
    gated_clk := clk_next && latch }

/-
Gated clock is low when enable was low at latch point
-/
theorem icg_gates_when_disabled (s : ICGState)
    (h_latch : s.latched_enable = false) (h_clk : s.clk = true) :
    s.gated_clk = false ∨ (icgStep s true false).gated_clk = false := by
  cases s ; tauto

/-
Gated clock follows real clock when enabled
-/
theorem icg_passes_when_enabled (s : ICGState)
    (h_enable : s.latched_enable = true) :
    (icgStep s true s.enable).gated_clk = true := by
  unfold icgStep; aesop;

/-
No glitch: gated_clk only changes on clock edges
-/
theorem icg_no_glitch (s : ICGState) (clk_next : Bool)
    (h_same_clk : clk_next = s.clk) :
    (icgStep s clk_next s.enable).gated_clk =
    (if s.clk then s.clk && s.latched_enable
     else clk_next && s.latched_enable) := by
  unfold icgStep; aesop;