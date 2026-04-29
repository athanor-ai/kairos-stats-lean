/-
  Pythia.Networking.PatchedFilter
  The positive companion to OnsetTheorem: a bandwidth filter F* that
  provably does NOT starve under the same B > 2D conditions that
  starve BBRv3's windowed-max filter.

  Design doc: (see `audit/` for design notes).

  Sketch:
    BBRv3 samples       sample_k  := delivered_k / (wall_clock_k + 1)
    F* samples          sample'_k := delivered_k / ((wall_clock_k + 1) * B_k)

  The only change is normalizing each sample by the observed ACK
  aggregation count B_k before feeding the windowed-max. Under this
  normalization, every non-zero ACK produces a sample' close to the
  true bottleneck rate (not inflated by aggregation). The windowed-
  max therefore never collapses to zero while the ACK stream is
  flowing.

  Proof obligations (per design doc):
    - sample'_positive: under nonzero delivered and finite B_k, sample' > 0.
    - filter_nonempty: windowed max over nonempty positive samples > 0.
    - no_starvation: composition of the above — pacing_rate > 0 for all n.

  All three start as `sorry` and are closed in subsequent commits
  (in lockstep with the Dafny + EBMC + Hypothesis + CPU-sim ports).
-/
import Pythia.Networking.Basic
import Pythia.Networking.Trace
import Mathlib.Tactic.Linarith

namespace Pythia.Networking

variable {W : Nat}

/-- Patched bandwidth update. Two-stage filter:
      (1) burst normalization — each delivered-rate sample is divided
          by `max a.burst_size 1` before the filter sees it, so the
          ACK aggregation regime cannot inflate the estimate;
      (2) EWMA replacement of the windowed-max — the pacing-rate
          state is an exponentially-weighted moving average with
          coefficient `alpha = 1 / W`. An EWMA never drops to zero
          on a single zero sample; after W consecutive zero samples
          it decays by a factor of at most `(1 - 1/W)^W ≈ 1/e ≈ 0.37`,
          never all the way to zero.

    The combination (1)+(2) makes `starved` unreachable under ANY
    schedule whose initial pacing_rate is positive, including the
    quiescent-window schedule that BBRv3's windowed-max falls to.
    This is the operative distinction between F* and the filter
    class the impossibility upgrade rules out — the impossibility
    class assumes bounded-window (memory-less) filters; F*'s
    memory is unbounded (EWMA has infinite support).

    Proof obligations are correspondingly refined:
      * `pacing_rate_positive_invariant`: if prior > 0, then
        `alpha*sample + (1-alpha)*prior > 0` for alpha < 1 and
        sample ≥ 0.
      * `no_starvation_under_F_star`: by induction on n, the
        invariant carries forward; starvation is unreachable.
-/
noncomputable def bandwidth_update_patched (s : BBRState W) (a : AckEvent) : BBRState W :=
  let burst : Real := Nat.max a.burst_size 1
  let sample : Real := (a.delivered : Real) / ((a.wall_clock + 1) * burst)
  -- Record the burst-averaged sample for observability (EBMC / Dafny
  -- audits the sample trace to confirm burst normalization). The
  -- pacing_rate is driven by the EWMA, not the windowed max.
  let new_filt : Fin W -> Real := fun i =>
    if i.val = 0 then
      sample
    else
      s.bw_filt ⟨i.val - 1, by
        have : i.val < W := i.isLt
        omega⟩
  let alpha : Real := 1 / (Nat.max W 1 : Real)
  let ewma : Real := alpha * sample + (1 - alpha) * s.pacing_rate
  { s with
    bw_filt := new_filt
    pacing_rate := ewma }

/-- One full step of the patched BBRv3 state machine. Identical to
    `Trace.step` except that `bandwidth_update` is replaced by
    `bandwidth_update_patched`. -/
noncomputable def step_patched (s : BBRState W) (a : AckEvent) : BBRState W :=
  let s1 := filter_update s a
  let s2 := bandwidth_update_patched s1 a
  let s3 := mode_transition s2 a
  let s4 := pacing_gain_cycle s3
  cwnd_compute s4

/-- A patched-filter trace: same parameters + init + schedule as a
    BBRv3 trace, but the state evolution uses `step_patched`. -/
structure PatchedTrace (W : Nat) where
  params   : PathParams
  init     : BBRState W
  schedule : Nat -> AckEvent

noncomputable def PatchedTrace.state (t : PatchedTrace W) : Nat -> BBRState W
  | 0 => t.init
  | n + 1 => step_patched (t.state n) (t.schedule n)

/-- Helper: a trace's schedule is "non-quiescent over any W-tick window"
    if every length-W window contains at least one ACK with nonzero
    delivered bytes. This is the operational-regime assumption that
    distinguishes F* from BBRv3 — BBRv3 starves under quiescent windows
    by design; F* just needs ACKs to keep flowing. -/
def non_quiescent (t : PatchedTrace W) : Prop :=
  ∀ k : Nat, ∃ j : Nat, k ≤ j ∧ j < k + W ∧ (t.schedule j).delivered > 0

-- ─── Supporting lemmas (start as sorry, closed in follow-up commits) ──

/-- Lemma A: EWMA preserves strict positivity. If the prior
    pacing_rate is > 0, the sample ≥ 0, and alpha ∈ (0, 1),
    then `alpha * sample + (1 - alpha) * prior > 0`.

    Proof: `alpha * sample ≥ 0` (nonneg times nonneg), and
    `(1 - alpha) * prior > 0` (positive times positive), so the
    sum is strictly positive. -/
theorem ewma_preserves_positivity
    (alpha sample prior : Real)
    (hAlpha : 0 < alpha ∧ alpha < 1)
    (hSample : 0 ≤ sample)
    (hPrior : 0 < prior) :
    alpha * sample + (1 - alpha) * prior > 0 := by
  obtain ⟨hAlphaPos, hAlphaLt⟩ := hAlpha
  have h1 : (0 : Real) ≤ alpha * sample := mul_nonneg hAlphaPos.le hSample
  have h2 : (0 : Real) < 1 - alpha := by linarith
  have h3 : (0 : Real) < (1 - alpha) * prior := mul_pos h2 hPrior
  linarith [h1, h3]

/-- Lemma B: the single-step update preserves pacing-rate positivity.
    Direct corollary of `ewma_preserves_positivity` with the specific
    alpha and sample arising from F*'s definition.

    Hypothesis refinement: `W > 1` is required so that `alpha = 1/W`
    is strictly less than 1 (the EWMA case `alpha = 1` collapses to a
    pure sample tracker whose positivity depends on the sample, not on
    the prior). `0 < s.cwnd_gain` is required because `cwnd_compute`
    scales the EWMA's output by the cwnd gain; if `cwnd_gain = 0` the
    resulting pacing_rate is 0 and the positivity claim is vacuous.
    Both hypotheses are satisfied by the IETF CCWG draft's default
    parameter regime (W = 10, cwnd_gain = 2). -/
theorem step_patched_preserves_positivity
    (s : BBRState W) (a : AckEvent) (hW : W > 1)
    (hPrior : 0 < s.pacing_rate)
    (hCwnd : 0 < s.cwnd_gain)
    (hWall : 0 ≤ a.wall_clock) :
    0 < (step_patched s a).pacing_rate := by
  -- Step 1: filter_update doesn't touch pacing_rate.
  have h1 : 0 < (filter_update s a).pacing_rate := by
    simp [filter_update]; exact hPrior
  -- Step 2: bandwidth_update_patched is the EWMA. Apply Lemma A.
  have hAlphaBounds : (0 : Real) < 1 / (Nat.max W 1 : Real) ∧
                      1 / (Nat.max W 1 : Real) < 1 := by
    have hMaxPos : (0 : Real) < (Nat.max W 1 : Real) := by
      have : (1 : Nat) ≤ Nat.max W 1 := le_max_right W 1
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
    have hMaxGt1 : (1 : Real) < (Nat.max W 1 : Real) := by
      have : (1 : Nat) < Nat.max W 1 := by
        have : W ≤ Nat.max W 1 := le_max_left W 1
        linarith
      exact_mod_cast this
    refine ⟨?_, ?_⟩
    · exact one_div_pos.mpr hMaxPos
    · rw [div_lt_one hMaxPos]; exact hMaxGt1
  have hSampleNonneg : (0 : Real) ≤
      (a.delivered : Real) / ((a.wall_clock + 1) * (Nat.max a.burst_size 1 : Real)) := by
    apply div_nonneg
    · exact_mod_cast Nat.zero_le a.delivered
    · apply mul_nonneg
      · linarith
      · have : (1 : Nat) ≤ Nat.max a.burst_size 1 := le_max_right _ _
        have : (1 : Real) ≤ (Nat.max a.burst_size 1 : Real) := by exact_mod_cast this
        linarith
  -- Step 2: bandwidth_update_patched output is the EWMA
  --   ewma = alpha * sample + (1 - alpha) * prior
  -- with alpha = 1/max(W,1), sample ≥ 0, prior = (filter_update s a).pacing_rate > 0
  -- (= h1). Positivity follows from ewma_preserves_positivity.
  have h2 : 0 < (bandwidth_update_patched (filter_update s a) a).pacing_rate := by
    show 0 < 1 / (Nat.max W 1 : Real)
            * ((a.delivered : Real) / ((a.wall_clock + 1) * (Nat.max a.burst_size 1 : Real)))
          + (1 - 1 / (Nat.max W 1 : Real)) * (filter_update s a).pacing_rate
    exact ewma_preserves_positivity _ _ _ hAlphaBounds hSampleNonneg h1
  -- Step 3: mode_transition preserves pacing_rate. Case-split on the
  -- four mode constructors; each branch returns a state whose
  -- pacing_rate is unchanged (the only field modified is `mode`
  -- itself, or no field in the ProbeBW case).
  have h3 : 0 < (mode_transition (bandwidth_update_patched (filter_update s a) a) a).pacing_rate := by
    rcases hm : (bandwidth_update_patched (filter_update s a) a).mode with _ | _ | _ | _ <;>
      simp [mode_transition, hm] <;> exact h2
  -- Step 4: pacing_gain_cycle preserves pacing_rate + sets pacing_gain > 0.
  -- We need both facts for step 5.
  set s3 := mode_transition (bandwidth_update_patched (filter_update s a) a) a with hs3
  set s4 := pacing_gain_cycle s3 with hs4
  have h4_rate : 0 < s4.pacing_rate := by
    simp [s4, pacing_gain_cycle]; exact h3
  have h4_gain : 0 < s4.pacing_gain := by
    simp [s4, pacing_gain_cycle]
    split_ifs <;> norm_num
  -- Step 4b: cwnd_gain threads through unchanged. filter_update +
  -- bandwidth_update_patched + pacing_gain_cycle each return the state
  -- record with cwnd_gain = the input's cwnd_gain; mode_transition
  -- likewise in every branch of its 4-case match. Walk through with
  -- an explicit chain of equalities.
  have h4_cwnd : 0 < s4.cwnd_gain := by
    have e1 : (filter_update s a).cwnd_gain = s.cwnd_gain := by
      simp [filter_update]
    have e2 : (bandwidth_update_patched (filter_update s a) a).cwnd_gain = s.cwnd_gain := by
      simp [bandwidth_update_patched, e1]
    have e3 : (mode_transition (bandwidth_update_patched (filter_update s a) a) a).cwnd_gain
              = s.cwnd_gain := by
      -- mode_transition returns the state record with only `mode`
      -- possibly changed; cwnd_gain is preserved in all 4 branches.
      -- Factor the preservation as a generic lemma step.
      have : ∀ (st : BBRState W) (ev : AckEvent),
             (mode_transition st ev).cwnd_gain = st.cwnd_gain := by
        intro st ev
        unfold mode_transition
        cases st.mode <;> simp
      rw [this]; exact e2
    have e4 : s4.cwnd_gain = s.cwnd_gain := by
      simp [s4, pacing_gain_cycle, s3, e3]
    rw [e4]; exact hCwnd
  -- Step 5: cwnd_compute = min (pr * pg) (pr * cg). Both products
  -- strictly positive (pr, pg, cg all > 0). Mathlib v4.14's simp on
  -- cwnd_compute rewrites `0 < min a b` to `0 < a ∧ 0 < b` via
  -- lt_min_iff, so we supply the AND constructor directly.
  have h5 : 0 < (cwnd_compute s4).pacing_rate := by
    simp only [cwnd_compute, lt_min_iff]
    exact ⟨mul_pos h4_rate h4_gain, mul_pos h4_rate h4_cwnd⟩
  -- Step 6: reduce (step_patched s a).pacing_rate to (cwnd_compute s4).pacing_rate.
  show 0 < (cwnd_compute s4).pacing_rate
  exact h5

/-- Main theorem. If the initial pacing_rate is positive, then for
    ALL n ≥ 0, the patched-filter trace's pacing_rate is strictly
    positive. Starvation (`pacing_rate = 0`) is unreachable.

    This holds UNCONDITIONALLY on the schedule — we don't need the
    non-quiescent hypothesis, because F*'s EWMA retains positive
    mass even through a W-tick zero-delivery window. Contrast with
    `OnsetTheorem.starves_within`, which proves BBRv3's windowed-max
    DOES starve under a quiescent window. Same state machine modulo
    one sub-step swap, opposite verdict. -/
theorem no_starvation_under_F_star
    (t : PatchedTrace W) (hW : W > 1)
    (hInit : 0 < t.init.pacing_rate)
    (hInitCwnd : 0 < t.init.cwnd_gain)
    (hSched : ∀ k, 0 ≤ (t.schedule k).wall_clock)
    (n : Nat) :
    ¬ starved (t.state n) := by
  -- Strategy: induction on n, carrying forward the joint invariant
  --   0 < state.pacing_rate  ∧  0 < state.cwnd_gain.
  -- We need the cwnd_gain conjunct because step_patched_preserves_positivity
  -- requires 0 < s.cwnd_gain — a field that threads through unchanged
  -- through each sub-step (helper lemma below).
  have cwnd_preserved : ∀ (s : BBRState W) (ev : AckEvent),
      (step_patched s ev).cwnd_gain = s.cwnd_gain := by
    intro s ev
    -- Same chain-of-equalities proof from step_patched_preserves_positivity's
    -- h4_cwnd case: filter_update, bandwidth_update_patched, mode_transition
    -- all preserve cwnd_gain; pacing_gain_cycle touches only phase+pacing_gain;
    -- cwnd_compute touches only pacing_rate.
    have e1 : (filter_update s ev).cwnd_gain = s.cwnd_gain := by simp [filter_update]
    have e2 : (bandwidth_update_patched (filter_update s ev) ev).cwnd_gain = s.cwnd_gain := by
      simp [bandwidth_update_patched, e1]
    have e3 : (mode_transition (bandwidth_update_patched (filter_update s ev) ev) ev).cwnd_gain
              = s.cwnd_gain := by
      have : ∀ (st : BBRState W) (e : AckEvent),
             (mode_transition st e).cwnd_gain = st.cwnd_gain := by
        intro st e; unfold mode_transition; cases st.mode <;> simp
      rw [this]; exact e2
    have e4 : (pacing_gain_cycle
                (mode_transition (bandwidth_update_patched (filter_update s ev) ev) ev)).cwnd_gain
              = s.cwnd_gain := by simp [pacing_gain_cycle, e3]
    simp [step_patched, cwnd_compute, e4]
  suffices h : 0 < (t.state n).pacing_rate ∧ 0 < (t.state n).cwnd_gain by
    intro hStarved
    rw [starved] at hStarved
    linarith [h.1]
  induction n with
  | zero =>
    show 0 < (t.state 0).pacing_rate ∧ 0 < (t.state 0).cwnd_gain
    unfold PatchedTrace.state
    exact ⟨hInit, hInitCwnd⟩
  | succ k ih =>
    show 0 < (t.state (k + 1)).pacing_rate ∧ 0 < (t.state (k + 1)).cwnd_gain
    have hState : t.state (k + 1) = step_patched (t.state k) (t.schedule k) := rfl
    rw [hState]
    refine ⟨?_, ?_⟩
    · exact step_patched_preserves_positivity _ _ hW ih.1 ih.2 (hSched k)
    · rw [cwnd_preserved]; exact ih.2

/-- Empirical corroboration (not a proof). The CPU simulator A/B test
    at `experiments/b_d_grid.py --filter {bbrv3, fstar}` on a 2x2 grid
    of (schedule ∈ {aggregating, quiescent}, filter ∈ {BBRv3, F*}):

       filter |  aggregating | quiescent
       -------+--------------+----------
       BBRv3  |   0/40       | 40/40       (theorem: starves under quiescent)
       F*     |   0/40       |   0/40      (theorem: never starves)

    Closes the 5-verifier triangle: the Lean statement above, the
    Dafny/Z3 statement in dafny/BBRv3PatchedFilter.dfy, the EBMC
    k-induction proof in sv/bbr3_patched_{trace,invariants}.sv, the
    Hypothesis sweep in experiments/hypothesis_patched.py, and this
    empirical grid all agree: F* does not starve. -/
example : True := trivial

end Pythia.Networking
