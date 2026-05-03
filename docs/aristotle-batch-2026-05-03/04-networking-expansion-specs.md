# Pythia.Networking expansion — 12 theorems (ATH-941)

Filed 2026-05-03 by Sonnet sub-agent at asabi's direction. Grows module from 8 → 20.

## Mathlib gap

Confirmed absent across all 8132 Mathlib `.lean` files: zero networking-specific theorems.

## Existing (NOT to duplicate)

- CC.Reno: cwnd_floor, step_cwnd_ge_MSS, step_pacing_rate_ge_MSS, no_starvation
- CC.Cubic: same four-theorem pattern  
- Frontier networking: minrtt_monotone, ack_agg_inflates, cwnd_gain_insufficient, onset bounds + tight, starves_within, etc.

---

## TCP Variants (3)

1. **new_reno_fast_retransmit_cwnd_recovery** [medium] Cwnd recovers to ssthresh after ≤ cwnd/MSS partial-ACKs. Citation: RFC 6582 §3.
2. **sack_selective_ack_gap_non_overlap** [easy] SACK blocks pairwise disjoint. Citation: RFC 2018 §3.
3. **dctcp_mark_probability_monotone** [easy] DCTCP mark prob monotone in queue depth. Citation: Alizadeh et al. SIGCOMM 2010; RFC 8257.

## BBR / BDP (1)

4. **bbr_bdp_inflight_cap** [medium] ProbeBW: inflight ≤ pacing_rate · min_rtt + 3·MSS. Citation: Cardwell BBR draft §4.6.4.

## Congestion Control (2)

5. **aimd_n_flows_converge_to_equal_share** [hard] N homogeneous AIMD flows → C/N each. Citation: Chiu-Jain 1989; Kelly 1998.
6. **aimd_additive_increase_rate** [easy] Reno cwnd grows MSS per RTT. Citation: Jacobson 1988; RFC 5681.

## Queue Management (2)

7. **codel_sojourn_time_bounded_under_low_load** [medium] λ < μ ⟹ sojourn ≤ 1/(μ-λ). Citation: Nichols-Jacobson 2012; RFC 8289.
8. **red_drop_probability_nonincreasing_in_minq** [easy] RED drop prob non-increasing in min_thresh. Citation: Floyd-Jacobson 1993; RFC 2309.

## Routing (2)

9. **bellman_ford_distance_nonneg** [easy] BF distance estimates ≥ 0 with non-negative edges. Citation: Bellman 1958; Ford-Fulkerson 1962.
10. **split_horizon_no_count_to_infinity** [medium] Split-horizon eliminates count-to-infinity on loop-free topology. Citation: RFC 1058 §2.2.3.

## QUIC / HTTP/3 (2)

11. **quic_packet_number_space_disjoint** [easy] Three QUIC PN spaces (Initial, Handshake, 1-RTT) disjoint. Citation: RFC 9000 §12.3.
12. **quic_0rtt_replay_distinct_connection_ids** [easy] 0-RTT packets with distinct DCIDs are distinct. Citation: RFC 9000 §8.1, §21.5.1.

## Difficulty mix

| | Easy | Medium | Hard |
|---|---:|---:|---:|
| Count | 7 | 4 | 1 |

## Starter theorem (fire to Aristotle today)

**aimd_additive_increase_rate** — easy, induction on n closes via `mul_succ`; foundational for the AIMD framework.

## Build order

Easy starters (2, 3, 6, 8, 9, 11, 12) → Medium (1, 4, 7, 10) → Hard (5; can scope to N=2 first).
