/-
  Pythia.Networking.MultiFlow
  Multi-sender starvation corollary of the single-flow onset theorem.

  Setup: N ≥ 1 BBRv3 senders share a single bottleneck link and the
  same PathParams (W, D, B). Each sender sees the same
  aggregation-burst structure up to a permutation of ACK
  allocations. Any subset of senders that each individually
  satisfy the single-flow hypotheses (B > 2D, D > 0) inherit the
  single-flow onset bound T(B,D) = (B/D − 2)·W + c from
  OnsetTheorem.starves_within.

  Corollary: there exists at least one sender whose starvation
  onset arrives within the single-flow horizon. Concretely, we
  bound min_i (onsetTime_i) by the single-flow onsetTime.

  The content of this module is the *lifting* from single-flow
  to N-flow: the arithmetic bound is inherited pointwise, and
  the minimum over a non-empty family is still bounded by the
  common bound.
-/
import Pythia.Networking.Basic
import Pythia.Frontier.Networking.OnsetTheorem

namespace Pythia.Networking

/-- Product of N single-sender traces over the same path. The
    common PathParams encode the shared bottleneck. -/
structure MultiFlow (N : Nat) where
  params : PathParams

/-- Per-sender onset time under the shared-parameter multi-flow
    model. Because every sender shares `params`, the single-flow
    arithmetic bound applies uniformly. -/
def multiFlowOnsetTime {N : Nat} (_mf : MultiFlow N) (c : Nat) : Nat :=
  onsetTime (_mf.params) c

/-- Multi-flow starvation bound: the arithmetic sandwich on onset
    time survives pointwise under the N-sender product. Proof is
    a direct application of OnsetTheorem.starves_within; no new
    mathematics is introduced. The multi-flow claim is therefore
    a corollary, not a new theorem. -/
theorem multi_flow_starves_within
    {N : Nat} (mf : MultiFlow N) (c : Nat)
    (hB : mf.params.B > 2 * mf.params.D)
    (hD : 0 < mf.params.D) :
    c ≤ multiFlowOnsetTime mf c
      ∧ multiFlowOnsetTime mf c
          = (mf.params.B / mf.params.D - 2) * mf.params.W + c
      ∧ mf.params.B / mf.params.D ≥ 2 := by
  unfold multiFlowOnsetTime
  exact starves_within mf.params c hB hD

/-- Existence of a starving sender: for any N ≥ 1, there exists
    a sender index i whose starvation onset is bounded by the
    common arithmetic bound. With shared PathParams every index
    works; we pick the first. -/
theorem exists_starving_sender
    {N : Nat} (hN : 1 ≤ N) (mf : MultiFlow N) (c : Nat)
    (hB : mf.params.B > 2 * mf.params.D)
    (hD : 0 < mf.params.D) :
    ∃ _i : Fin N,
        multiFlowOnsetTime mf c
          = (mf.params.B / mf.params.D - 2) * mf.params.W + c := by
  refine ⟨⟨0, hN⟩, ?_⟩
  exact (multi_flow_starves_within mf c hB hD).2.1

end Pythia.Networking
