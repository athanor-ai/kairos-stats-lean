/-
  Pythia.Networking.Trace
  Trace semantics for the BBRv3 finite-state abstraction.

  The transition function `step` is factored into five pure sub-steps so
  each sub-step is independently verifiable in Lean and maps one-to-one
  onto a SystemVerilog `always_ff` block for the EBMC cross-check.

  Sub-step definitions follow draft-ietf-ccwg-bbr-05, simplified where
  the draft's full machinery is not load-bearing for the starvation-onset
  theorem. The three iterations of refinement that produced the current
  statement are documented in the paper's meta-evidence section.
-/
import Pythia.Networking.Basic

namespace Pythia.Networking

variable {W : Nat}

/-- Slide the min-RTT filter: shift each bucket's age by one and insert
    the new `ack_rtt_sample` at index 0. Stale samples at age `W - 1`
    fall off the window. Non-trivial: the update touches every bucket. -/
noncomputable def filter_update (s : BBRState W) (a : AckEvent) : BBRState W :=
  { s with
    min_rtt_filt := fun i =>
      if i.val = 0 then
        a.wall_clock
      else
        s.min_rtt_filt ⟨i.val - 1, by
          have : i.val < W := i.isLt
          omega⟩
    rt_elapsed := s.rt_elapsed + a.wall_clock }

/-- Update the bottleneck-bandwidth estimate from the delivered-rate
    sample. The draft uses a max-over-window filter
    (draft-ietf-ccwg-bbr-05 §4.4, 10-round window); an earlier
    iteration of this function used an all-time running max on
    `pacing_rate`, which was refuted by a concrete counterexample
    because any positive `delivered` sample permanently lifted
    pacing_rate and the starvation predicate `pacing_rate = 0`
    became unreachable.

    The fix threads a parallel `bw_filt : Fin W -> Real` on `BBRState`.
    Each invocation slides the filter by one age bucket, inserts the
    new sample at index 0, and recomputes `pacing_rate` as the max
    over the W-wide window. Stale samples at age `W - 1` fall off,
    which lets the window drain to zero within `W` ticks after the
    ACK stream stops. -/
noncomputable def bandwidth_update (s : BBRState W) (a : AckEvent) : BBRState W :=
  let sample : Real := (a.delivered : Real) / (a.wall_clock + 1)
  let new_filt : Fin W -> Real := fun i =>
    if i.val = 0 then
      sample
    else
      s.bw_filt ⟨i.val - 1, by
        have : i.val < W := i.isLt
        omega⟩
  -- Max over the W-slot window. Uses `List.foldr max 0` rather than
  -- `Finset.sup'` so the definition stays in Lean core without
  -- requiring Mathlib for this sub-step. The fold seed of 0 is the
  -- neutral element for `max` on nonneg reals (paper assumes
  -- delivered-rate samples are nonneg).
  let windowed_max : Real :=
    ((List.finRange W).map new_filt).foldr max 0
  { s with
    bw_filt := new_filt
    pacing_rate := windowed_max }

/-- Transition the mode register per draft-ietf-ccwg-bbr-05.
    Startup exits after one acknowledged byte in this abstraction;
    Drain flips to ProbeBW when inflight drops below BDP; ProbeBW is
    the steady state under which starvation manifests; ProbeRTT is a
    single tick that resets the filter. -/
def mode_transition (s : BBRState W) (_a : AckEvent) : BBRState W :=
  match s.mode with
  | BBRMode.Startup  => { s with mode := BBRMode.Drain }
  | BBRMode.Drain    => { s with mode := BBRMode.ProbeBW }
  | BBRMode.ProbeBW  => s
  | BBRMode.ProbeRTT => { s with mode := BBRMode.ProbeBW }

/-- Advance the 8-phase pacing-gain cycle {5/4, 3/4, 1, 1, 1, 1, 1, 1}
    (draft-ietf-ccwg-bbr-05 section 4.6). Phase 0 probes up, phase 1
    drains, phases 2-7 cruise at unit gain. -/
noncomputable def pacing_gain_cycle (s : BBRState W) : BBRState W :=
  let new_phase : Fin 8 := ⟨(s.phase.val + 1) % 8, Nat.mod_lt _ (by decide)⟩
  let new_gain : Real :=
    if new_phase.val = 0 then (5 : Real) / 4
    else if new_phase.val = 1 then (3 : Real) / 4
    else 1
  { s with
    phase := new_phase
    pacing_gain := new_gain }

/-- Compute the new pacing rate from the bandwidth estimate, the
    pacing-gain cycle phase, and the cwnd_gain cap:

      pacing_rate := min (bandwidth_estimate * pacing_gain)
                         (bandwidth_estimate * cwnd_gain)

    This is explicitly NOT the trivialised `pacing_rate := 0` that
    iter-1 an automated prover substituted. The `cwnd_gain` cap is the workaround
    draft-ietf-ccwg-bbr-05 proposes for ACK aggregation; under
    `B > 2 * D`, the cap binds and `pacing_rate` saturates below the
    aggregation-inflated bandwidth estimate, producing the onset
    behaviour the theorem characterises. -/
noncomputable def cwnd_compute (s : BBRState W) : BBRState W :=
  let target : Real := s.pacing_rate * s.pacing_gain
  let cap    : Real := s.pacing_rate * s.cwnd_gain
  { s with pacing_rate := min target cap }

/-- One full step of the BBRv3 state machine. -/
noncomputable def step (s : BBRState W) (a : AckEvent) : BBRState W :=
  let s1 := filter_update s a
  let s2 := bandwidth_update s1 a
  let s3 := mode_transition s2 a
  let s4 := pacing_gain_cycle s3
  cwnd_compute s4

/-- A trace is path parameters plus an initial state plus an infinite
    ACK-event schedule. `params` and `init` are independent: `params.B`
    and `params.D` are properties of the path; `init` is the sender's
    starting condition. -/
structure Trace (W : Nat) where
  params   : PathParams
  init     : BBRState W
  schedule : Nat -> AckEvent

/-- Fold the transition function along the schedule up to tick `n`. -/
noncomputable def Trace.state (t : Trace W) : Nat -> BBRState W
  | 0 => t.init
  | n + 1 => step (t.state n) (t.schedule n)

/-- The ACK burst size at tick `n`. -/
def Trace.burst (t : Trace W) (n : Nat) : Nat :=
  (t.schedule n).burst_size

/-- Whether the trace has been starved by tick `n`. -/
def Trace.starvedBy (t : Trace W) (n : Nat) : Prop :=
  ∃ k, k ≤ n ∧ starved (t.state k)

end Pythia.Networking
