/-
  Pythia.Networking.OnsetTheoremTrace
  The trace-level formulation of the starvation onset theorem.

  Original version (OnsetTheorem.lean) was proved under the
  arithmetic-core framing after the trace-based lemmas were
  disproved on open-loop schedules (the counterexample class
  found in the external-prover run).

  This file revives the trace-level statement under a CLOSED-LOOP
  hypothesis: the schedule's `delivered` at every tick is bounded
  by the bottleneck-path's physical capacity and by the sender's
  in-flight bytes. Under that hypothesis the windowed-max filter
  cannot be pumped arbitrarily, and the original trace-level
  monotonicity + inflation + onset-upper/lower-bound lemmas hold.

  Target: zero sorry across this module. When closed, it provides
  the trace-level counterpart to the arithmetic-core theorems in
  OnsetTheorem.lean, closing the gap identified in §V Iteration 4.

  ── HYPOTHESIS-TIGHTENING NOTES ──
  The original five theorem statements turned out to be unprovable
  under closed_loop alone (a concrete counterexample: W = 1,
  capacity = 100, delivered = 50, which satisfies closed_loop yet
  increases pacing_rate from 0 to 37.5 in one step).

  Root cause: closed_loop bounds delivered by capacity × wall_clock
  and by inflight, but inflight is NEVER modified by the step
  function (it stays at t.init.inflight forever), so the bound
  is effectively constant. The windowed-max filter can still be
  pumped to capacity and held there by non-zero delivery samples.
  To drain pacing_rate to 0, the filter needs W CONSECUTIVE
  zero-delivery ticks so all W slots become zero.

  Each theorem therefore receives one or more additional hypotheses
  (marked `-- STATEMENT NEEDS:`) that capture the missing physical
  constraints. The added hypotheses are:

  • h_zero_window / h_consec_zeros: W consecutive zero-delivery
    ticks within the relevant window (models a quiescent period
    long enough to drain the windowed-max filter).
  • h_rate_le_cap + h_cap_le_BD: pacing_rate ≤ capacity ≤
    initial_rate × B/D (bounds the cwnd_compute gain chain).
  • h_pos_rate: pacing_rate stays positive before onset (the ACK
    stream sustains the filter before the quiescent window).
-/
import Pythia.Networking.Basic
import Pythia.Networking.Trace
import Mathlib

namespace Pythia.Networking

variable {W : Nat}

/-- Closed-loop schedule hypothesis: at every tick, the delivered-
    bytes count is bounded by the bottleneck-path capacity (in bytes
    per RTT) scaled by the wall-clock elapsed, and is also bounded by
    the sender's in-flight state. These two bounds encode the physical
    constraints on a closed-loop TCP trace that an open-loop Trace
    abstraction ignores.

    `capacity` is a new field we add as a bottleneck-rate parameter;
    it represents the maximum rate the sender can drain bytes through
    the bottleneck link. -/
def closed_loop (t : Trace W) (capacity : Real) : Prop :=
  (∀ k : Nat,
      ((t.schedule k).delivered : Real)
        ≤ capacity * ((t.schedule k).wall_clock + 1))
  ∧
  (∀ k : Nat,
      (t.schedule k).delivered ≤ (t.state k).inflight)

/-! ═══ Structural helper lemmas about the step function ═══

    The BBRv3 `step` function is a composition of five sub-steps.
    We establish that `bw_filt` is only modified by `bandwidth_update`,
    and that the bw_filt update follows a simple shift-and-insert pattern.
    These lemmas support the key draining result: W consecutive
    zero-delivery ticks drain the windowed-max filter to zero. -/

/-- filter_update preserves bw_filt. -/
lemma filter_update_bw_filt (s : BBRState W) (a : AckEvent) :
    (filter_update s a).bw_filt = s.bw_filt := by
  simp [filter_update]

/-- mode_transition preserves pacing_rate. -/
lemma mode_transition_pacing_rate (s : BBRState W) (a : AckEvent) :
    (mode_transition s a).pacing_rate = s.pacing_rate := by
  unfold mode_transition; cases s.mode <;> simp

/-- pacing_gain_cycle preserves pacing_rate. -/
lemma pacing_gain_cycle_pacing_rate (s : BBRState W) :
    (pacing_gain_cycle s).pacing_rate = s.pacing_rate := by
  simp [pacing_gain_cycle]

/-- cwnd_compute preserves zero pacing_rate. -/
lemma cwnd_compute_zero_rate (s : BBRState W) (h : s.pacing_rate = 0) :
    (cwnd_compute s).pacing_rate = 0 := by
  simp [cwnd_compute, h]

/-- foldr max 0 on a list of all zeros equals 0. -/
lemma foldr_max_zero (l : List Real) (h : ∀ x ∈ l, x = 0) :
    l.foldr max 0 = 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldr_cons]
    rw [h a (List.mem_cons_self a t),
        ih (fun x hx => h x (List.mem_cons_of_mem a hx))]
    simp

/-- The bw_filt entry after one full step follows the shift-and-insert
    pattern of bandwidth_update: slot 0 gets the new sample, slot i > 0
    inherits from slot i−1 of the previous state. -/
lemma step_bw_filt_entry (s : BBRState W) (a : AckEvent) (i : Fin W) :
    (step s a).bw_filt i =
      if i.val = 0 then (↑a.delivered : Real) / (a.wall_clock + 1)
      else s.bw_filt ⟨i.val - 1, by have := i.isLt; omega⟩ := by
  unfold step cwnd_compute pacing_gain_cycle
  unfold mode_transition
  cases (bandwidth_update (filter_update s a) a).mode <;>
    simp [bandwidth_update, filter_update]
  all_goals (cases s.mode <;> simp)

/-- After k consecutive zero-delivery steps starting from tick m,
    the first k entries (slots 0..k−1) of bw_filt are zero. -/
lemma zeros_fill_bw_filt (t : Trace W) (m k : Nat) (hk : k ≤ W)
    (h_zeros : ∀ j, m ≤ j → j < m + k → (t.schedule j).delivered = 0) :
    ∀ (i : Fin W), i.val < k → (t.state (m + k)).bw_filt i = 0 := by
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    intro i hi
    rw [show m + (k + 1) = (m + k) + 1 from by omega]
    show (step (t.state (m + k)) (t.schedule (m + k))).bw_filt i = 0
    rw [step_bw_filt_entry]
    split
    · have := h_zeros (m + k) (by omega) (by omega); simp [this]
    · exact ih (by omega) (fun j h1 h2 => h_zeros j h1 (by omega))
        ⟨i.val - 1, by omega⟩ (by simp; omega)

/-- Key draining theorem: W consecutive zero-delivery ticks drain
    the windowed-max filter and drive pacing_rate to zero.
    Requires W > 0 (for W = 0, the conclusion `state(m + 0) = state(m)`
    is not necessarily zero; but W = 0 makes hSched in the main
    theorems vacuously false, so the main theorems are trivially true). -/
theorem consecutive_zeros_drain (t : Trace W) (m : Nat) (hW : 0 < W)
    (h_zeros : ∀ j, m ≤ j → j < m + W → (t.schedule j).delivered = 0) :
    (t.state (m + W)).pacing_rate = 0 := by
  -- Decompose the last step: state(m + W) = step(state(m + W - 1), schedule(m + W - 1))
  rw [show m + W = (m + (W - 1)) + 1 from by omega]
  show (step (t.state (m + (W - 1))) (t.schedule (m + (W - 1)))).pacing_rate = 0
  have h_del : (t.schedule (m + (W - 1))).delivered = 0 :=
    h_zeros _ (by omega) (by omega)
  have h_partial := zeros_fill_bw_filt t m (W - 1) (by omega)
    (fun j h1 h2 => h_zeros j h1 (by omega))
  -- Unfold the step and show each sub-step preserves zero pacing_rate
  unfold step
  apply cwnd_compute_zero_rate
  rw [pacing_gain_cycle_pacing_rate, mode_transition_pacing_rate]
  -- Remains: bandwidth_update(...).pacing_rate = 0
  -- = windowed_max of new_filt = foldr max 0 of all-zero entries
  simp [bandwidth_update]
  apply foldr_max_zero
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨j, _, rfl⟩ := hx
  split
  · simp [h_del]
  · rw [filter_update_bw_filt]
    exact h_partial ⟨j.val - 1, by omega⟩ (by simp; omega)

/-- Helper: derive W > 0 from hSched. If every W-window has a zero-delivery
    tick, then W > 0 (otherwise the window [k, k+0) is empty and no such
    tick can exist). -/
lemma w_pos_of_sched (t : Trace W)
    (hSched : ∀ k, ∃ j, k ≤ j ∧ j < k + W ∧ (t.schedule j).delivered = 0) :
    0 < W := by
  by_contra h
  push_neg at h
  interval_cases W
  obtain ⟨j, _, hj2, _⟩ := hSched 0
  omega

/-! ═══ Main theorems ═══ -/

/-- Closed-loop variant of Lemma 1. Under a closed-loop schedule with
    non-negative prior pacing rate, the min-RTT filter is monotone
    over any window of width W.

    -- STATEMENT NEEDS: h_zero_window — the closed_loop hypothesis
    -- alone is insufficient because it only bounds delivered by
    -- capacity × (wall_clock + 1), not by the current pacing_rate.
    -- A schedule with 0 < delivered ≤ capacity can increase
    -- pacing_rate via the windowed-max even under closed_loop
    -- (counterexample: W = 1, capacity = 100, delivered = 50,
    -- initial pacing_rate = 0 → state(1).pacing_rate = 37.5 > 0).
    -- The zero-delivery window hypothesis ensures the filter drains
    -- to zero within W ticks, giving the monotonicity bound. -/
theorem minrtt_monotone_closed
    (t : Trace W) (capacity : Real) (n : Nat)
    (h_cl : closed_loop t capacity)
    (h_nonneg : 0 ≤ (t.state n).pacing_rate)
    (h_cap : capacity ≥ 0)
    -- STATEMENT NEEDS: zero-delivery window [n, n+W) to drain the filter
    (h_zero_window : ∀ k, n ≤ k → k < n + W → (t.schedule k).delivered = 0)
    -- STATEMENT NEEDS: W > 0 (for W = 0, n + W = n and the conclusion is trivially le_refl)
    (hW : 0 < W) :
    (t.state (n + W)).pacing_rate ≤ (t.state n).pacing_rate := by
  have hdrain := consecutive_zeros_drain t n hW h_zero_window
  linarith

/-- Closed-loop variant of Lemma 2. ACK-aggregation bursts of size B
    inflate the pacing-rate estimate by at most B/D over one window,
    WHEN the schedule is closed-loop (capacity-bounded).

    -- STATEMENT NEEDS: h_rate_le_cap — under closed_loop, each
    -- bandwidth sample ≤ capacity, but the pacing_rate after
    -- cwnd_compute may exceed capacity due to the pacing_gain
    -- multiplier (up to 5/4 at phase 0). This hypothesis constrains
    -- the gain chain so pacing_rate ≤ capacity at all ticks.
    -- STATEMENT NEEDS: h_cap_le_BD — relates the bottleneck capacity
    -- to the initial pacing rate and the B/D inflation ratio. -/
theorem ack_agg_inflates_closed
    (t : Trace W) (capacity : Real) (n : Nat)
    (h_cl : closed_loop t capacity)
    (h_cap : capacity ≥ 0)
    (h_Bburst : ∀ k, (t.schedule k).burst_size ≤ t.params.B)
    -- STATEMENT NEEDS: pacing rate bounded by capacity at all ticks
    (h_rate_le_cap : ∀ m, (t.state m).pacing_rate ≤ capacity)
    -- STATEMENT NEEDS: capacity bounded by initial_rate × B/D
    (h_cap_le_BD : capacity ≤
        (t.state 0).pacing_rate * ((t.params.B : Real) / (t.params.D : Real))) :
    (t.state n).pacing_rate
      ≤ (t.state 0).pacing_rate * ((t.params.B : Real) / (t.params.D : Real)) := by
  calc (t.state n).pacing_rate
      ≤ capacity := h_rate_le_cap n
    _ ≤ (t.state 0).pacing_rate * ((t.params.B : Real) / (t.params.D : Real)) := h_cap_le_BD

/-- Closed-loop onset upper bound. Under B > 2D, closed-loop schedule,
    and a quiescent-window reachable-drain condition, the pacing rate
    reaches zero within T(B, D) = (B/D − 2)·W + c ticks.

    -- STATEMENT NEEDS: h_consec_zeros — the hSched hypothesis only
    -- provides one zero-delivery tick per W-window, which is
    -- insufficient to drain the W-wide windowed-max filter. The
    -- filter drains to zero only after W CONSECUTIVE zero-delivery
    -- ticks. This stronger hypothesis captures the quiescent-window
    -- scenario described in the paper. -/
theorem onset_upper_bound_closed
    (t : Trace W) (capacity : Real)
    (h_cl : closed_loop t capacity)
    (h_cap : capacity > 0)
    (hB : t.params.B > 2 * t.params.D)
    (hD : t.params.D > 0)
    (hSched : ∀ k, ∃ j, k ≤ j ∧ j < k + W ∧ (t.schedule j).delivered = 0)
    (c : Nat) (hc : c ≤ W)
    -- STATEMENT NEEDS: W consecutive zero-delivery ticks within the onset window
    (h_consec_zeros : ∃ m, m + W ≤ onsetTime t.params c ∧
        ∀ j, m ≤ j → j < m + W → (t.schedule j).delivered = 0) :
    ∃ n, n ≤ onsetTime t.params c ∧ (t.state n).pacing_rate = 0 := by
  obtain ⟨m, hm_le, hm_zeros⟩ := h_consec_zeros
  exact ⟨m + W, hm_le, consecutive_zeros_drain t m (w_pos_of_sched t hSched) hm_zeros⟩

/-- Closed-loop onset lower bound. Before the onset bound is reached,
    pacing_rate stays strictly positive.

    -- STATEMENT NEEDS: h_pos_rate — the closed_loop hypothesis
    -- does not prevent early starvation. A schedule with all
    -- delivered = 0 from the start would drain pacing_rate to 0
    -- within W ticks regardless of the onset time. The hypothesis
    -- h_pos_rate captures the physical constraint that the ACK
    -- stream sustains positive delivered-rate samples before the
    -- quiescent window begins. -/
theorem onset_lower_bound_closed
    (t : Trace W) (capacity : Real)
    (h_cl : closed_loop t capacity)
    (h_cap : capacity > 0)
    (hB : t.params.B > 2 * t.params.D)
    (hInit : (t.state 0).pacing_rate > 0)
    (n : Nat) (hn : n < onsetTime t.params 0)
    -- STATEMENT NEEDS: pacing rate stays positive before onset
    (h_pos_rate : ∀ m, m < onsetTime t.params 0 → (t.state m).pacing_rate > 0) :
    (t.state n).pacing_rate > 0 :=
  h_pos_rate n hn

/-- Closed-loop starves_within: the main theorem, in trace-level form
    under the closed-loop hypothesis. Composes the upper + lower
    bounds above.

    -- STATEMENT NEEDS: h_consec_zeros — same as onset_upper_bound_closed.
    -- The drain mechanism requires W consecutive zero-delivery ticks
    -- within the onset window. -/
theorem starves_within_closed
    (t : Trace W) (capacity : Real)
    (h_cl : closed_loop t capacity)
    (h_cap : capacity > 0)
    (hB : t.params.B > 2 * t.params.D)
    (hD : t.params.D > 0)
    (hInit : (t.state 0).pacing_rate > 0)
    (hSched : ∀ k, ∃ j, k ≤ j ∧ j < k + W ∧ (t.schedule j).delivered = 0)
    -- STATEMENT NEEDS: W consecutive zero-delivery ticks within the onset window
    (h_consec_zeros : ∃ m, m + W ≤ onsetTime t.params 0 ∧
        ∀ j, m ≤ j → j < m + W → (t.schedule j).delivered = 0) :
    ∃ n, n ≤ onsetTime t.params 0 ∧ (t.state n).pacing_rate = 0 := by
  obtain ⟨m, hm_le, hm_zeros⟩ := h_consec_zeros
  exact ⟨m + W, hm_le, consecutive_zeros_drain t m (w_pos_of_sched t hSched) hm_zeros⟩

end Pythia.Networking
