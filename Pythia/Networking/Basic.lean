/-
  Pythia.Networking.Basic
  Types and constants for the BBRv3 finite-state abstraction.

  State vector and input event are small so the EBMC dual in
  `verilog/bbr3.sv` maps one-to-one. Each field is bounded so the state
  space is finite under k-induction at bound K = 64 RTTs.

  The four verification layers share this type hierarchy verbatim:
    - Lean 4 proofs close the theorems in `OnsetTheorem.lean`.
    - `scripts/lean_to_sv.py` emits the SystemVerilog dual.
    - Hypothesis strategies in `experiments/hypothesis_sweep.py` instantiate
      the `BBRState` / `AckEvent` algebraically.
    - The packet simulator (bundled in the replication package)
      runs the same transition function in Python.
-/
import Mathlib.Data.Real.Basic

namespace Pythia.Networking

/-- BBR's mode register. Startup, Drain, ProbeBW, ProbeRTT per Cardwell et al.
    (IETF CCWG draft-ietf-ccwg-bbr-05, 2025). -/
inductive BBRMode where
  | Startup
  | Drain
  | ProbeBW
  | ProbeRTT
  deriving DecidableEq, Repr

/-- Parameters of the path under test. Fixed across a trace. -/
structure PathParams where
  /-- Equilibrium path delay range in RTT units. -/
  D : Nat
  /-- min-RTT filter window, draft default 10 s expressed in RTTs. -/
  W : Nat
  /-- Maximum ACK aggregation burst magnitude the path admits. -/
  B : Nat
  deriving Repr

/-- BBRv3 finite-state abstraction.
    min-RTT filter is a `Fin W -> Real` function, indexed by age in RTTs.
    bw_filt is a parallel windowed max filter for the bandwidth
    estimate (draft-ietf-ccwg-bbr-05 §4.4). The all-time running max
    in `pacing_rate` alone was refuted in a counterexample construction
    because it makes the starvation predicate unreachable; adding a
    windowed max so old-sample contributions drain within `W` ticks
    is the fix. `phase : Fin 8` tracks the ProbeBW pacing-gain cycle.
-/
structure BBRState (W : Nat) where
  mode         : BBRMode
  pacing_rate  : Real
  inflight     : Nat
  min_rtt_filt : Fin W -> Real
  /-- Windowed bandwidth filter. Age-indexed ring; `bw_filt 0` is the
      most-recent delivered-rate sample, `bw_filt (W-1)` is the
      oldest. Pacing-rate target is the max over this filter and
      drains within `W` ticks after the ACK stream stops. -/
  bw_filt      : Fin W -> Real
  cwnd_gain    : Real
  pacing_gain  : Real
  phase        : Fin 8
  rt_elapsed   : Real

/-- One ACK event visible to the sender: size of the burst, how much
    application data it acknowledged, elapsed wall-clock time. -/
structure AckEvent where
  burst_size  : Nat
  delivered   : Nat
  wall_clock  : Real
-- `deriving Repr` omitted: `Real` has no safe `Repr` instance
-- (Real is defined via Cauchy equivalence classes).

/-- A complete reachable state for analysis: parameters + state. -/
structure World (W : Nat) where
  params : PathParams
  state  : BBRState W
-- `deriving Repr` omitted for the same reason as AckEvent.

/-- Closed-form onset-time law. `c` is derived from BBRv3's state-machine
    constants; `OnsetTheorem.c_derivation` pins its value. -/
def onsetTime (p : PathParams) (c : Nat) : Nat :=
  (p.B / p.D - 2) * p.W + c

/-- A state is starved if its pacing rate has collapsed to zero. -/
def starved {W : Nat} (s : BBRState W) : Prop :=
  s.pacing_rate = 0

end Pythia.Networking
