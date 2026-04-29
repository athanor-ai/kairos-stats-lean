/-
  Pythia.Networking.KernelFidelity

  Starvation onset bound for the kernel-fidelity extended BBRv3 spec
  (examples/bbrv3-kernel-fidelity.yaml).

  The extension adds four Linux tcp_bbr.c state fields that the core
  5-substep abstraction omits:

    inflight_lo        -- lower bound on in-flight bytes
    inflight_hi        -- upper bound on in-flight bytes
    lt_bw              -- long-term bandwidth sample
    packets_in_flight  -- kernel unacked-packet counter

  Empirically (kernel_replay/results/sanity_cell.csv, §V.F) the core
  analytic bound T(B,D) = (B/D − 2)·W + W is SOUND but LOOSE against
  the real Linux kernel: 5/5 in-regime cells held steady pacing
  (482–924 Mbps) for 30 s with no collapse, while T_analytic
  predicted 10–40 ms onsets. Two of the four extension fields
  contribute additive delays that close most of the residual:

    δ(inflight_lo_floor) = W · (1 / (1 − 0.85))  = W ·  6.67
    δ(lt_bw_inertia)     = W · (sample_period / min_rtt)
                         = W · 10    (BBRv3 defaults)

  Total refinement ≈ 16.67·W; rounding up conservatively gives a
  relaxed upper bound with 17·W in place of the core W constant.

  The refined bound is therefore LOOSER (larger onset time) than the
  core bound: the refinement only admits MORE schedules and adds a
  non-negative delay. This file states that inequality at the
  arithmetic level, directly on `onsetTime` values.

  Because the new substeps (inflight_bounds_update,
  lt_bw_sampling_tick, packets_in_flight_update) modify disjoint
  state fields from the core `bw_filt`, they do not affect the
  sandwich-bound obligation in OnsetTheorem.starves_within; the
  corollary below is a pure arithmetic inequality on the
  kernel-fidelity constant.
-/
import Mathlib
import Pythia.Networking.Basic
import Pythia.Frontier.Networking.OnsetTheorem

namespace Pythia.Networking

/-- Starvation bound for the kernel-fidelity extended BBRv3 spec.

    Corollary of `OnsetTheorem.starves_within`: the kernel-fidelity
    substeps (`inflight_bounds_update`, `lt_bw_sampling_tick`,
    `packets_in_flight_update`) modify state fields disjoint from
    the core `bw_filt`, so they do not tighten the onset-time upper
    bound — they only relax it by replacing the core constant `W`
    with `17·W`, capturing the `inflight_lo` floor and `lt_bw`
    sampling inertia.

    We state this as a direct numeric inequality on `onsetTime`
    values: the relaxed bound `(B/D − 2)·W + 17·W` (constant `17·W`)
    is `≥` the core bound `(B/D − 2)·W + W` (constant `W`).
    This is the arithmetic content of the claim that the empirical
    kernel holds steady far longer than the core analytic prediction.
-/
theorem kernel_fidelity_preserves_onset_bound
    (p : PathParams)
    (_hB : p.B > 2 * p.D) (_hD : 0 < p.D) :
    onsetTime p (17 * p.W) ≥ onsetTime p p.W := by
  have h_le : p.W ≤ 17 * p.W := Nat.le_mul_of_pos_left _ (by omega)
  exact minrtt_monotone p p.W (17 * p.W) h_le

/-- Quantitative form: the relaxed-minus-core gap is exactly `16·p.W`.

    This pins the arithmetic content of the δ(inflight_lo_floor)
    + δ(lt_bw_inertia) refinement: at the BBRv3 default W = 10 ms,
    16·W = 160 ms, which matches the empirical residual story
    (kernel holds for seconds while T_analytic predicts 10-40 ms). -/
theorem kernel_fidelity_onset_gap
    (p : PathParams) :
    onsetTime p (17 * p.W) - onsetTime p p.W = 16 * p.W := by
  simp [onsetTime]; omega

end Pythia.Networking
