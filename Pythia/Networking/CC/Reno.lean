/-
  CC.Reno
  Positive theorem: Reno (AIMD) never starves on any bounded
  ACK schedule.

  Matches dsl/examples/reno.yaml (telos verify target). Same
  structural-induction pattern as CC.Cubic: the `cwnd_floor`
  substep enforces cwnd >= MSS at the end of every step, so the
  subsequent `pacing_compute` publishes cwnd as pacing_rate,
  ruling out starvation.

  Acceptance gate: zero unproved obligations, only axioms
  {propext, Classical.choice, Quot.sound}.
-/

namespace CC.Reno

abbrev Real := Int

structure State where
  cwnd           : Real
  ssthresh       : Real
  pacing_rate    : Real
  srtt           : Real
  in_slow_start  : Bool

structure Params where
  MSS : Real

/-- Substep `cwnd_floor`: RFC 5681 requires cwnd >= 1 MSS always. -/
def cwnd_floor (s : State) (p : Params) : State :=
  { s with cwnd := if s.cwnd < p.MSS then p.MSS else s.cwnd }

/-- Substep `pacing_compute`: pacing_rate := cwnd. -/
def pacing_compute (s : State) : State :=
  { s with pacing_rate := s.cwnd }

/-- One Reno step (positivity-relevant substeps only). -/
def step (s : State) (p : Params) : State :=
  pacing_compute (cwnd_floor s p)

/-- Substep lemma: cwnd_floor guarantees cwnd >= MSS. -/
theorem cwnd_floor_cwnd_ge_MSS
    (s : State) (p : Params) :
    (cwnd_floor s p).cwnd >= p.MSS := by
  unfold cwnd_floor
  by_cases hc : s.cwnd < p.MSS
  · simp [hc]
  · simp [hc]; exact Int.not_lt.mp hc

/-- Every step ends with cwnd >= MSS. -/
theorem step_cwnd_ge_MSS
    (s : State) (p : Params) :
    (step s p).cwnd >= p.MSS := by
  show (pacing_compute (cwnd_floor s p)).cwnd >= p.MSS
  simp [pacing_compute]
  exact cwnd_floor_cwnd_ge_MSS s p

/-- Every step ends with pacing_rate >= MSS. -/
theorem step_pacing_rate_ge_MSS
    (s : State) (p : Params) :
    (step s p).pacing_rate >= p.MSS := by
  show (pacing_compute (cwnd_floor s p)).pacing_rate >= p.MSS
  simp [pacing_compute]
  exact cwnd_floor_cwnd_ge_MSS s p

/-- Iterated step. -/
def iterate : State -> Params -> Nat -> State
  | s, _, 0     => s
  | s, p, n + 1 => step (iterate s p n) p

/-- Main positive theorem (spec: no_starvation_under_bounded_ack).
    For every n >= 1, Reno's pacing_rate is at least MSS. -/
theorem no_starvation
    (s0 : State) (p : Params) (n : Nat) :
    (iterate s0 p (n + 1)).pacing_rate >= p.MSS := by
  induction n with
  | zero =>
      show (step s0 p).pacing_rate >= p.MSS
      exact step_pacing_rate_ge_MSS s0 p
  | succ k _ =>
      show (step (iterate s0 p (k + 1)) p).pacing_rate >= p.MSS
      exact step_pacing_rate_ge_MSS (iterate s0 p (k + 1)) p

end CC.Reno
