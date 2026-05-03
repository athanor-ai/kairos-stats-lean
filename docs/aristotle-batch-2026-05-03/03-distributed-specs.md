# Pythia.Distributed  -  20 theorem specs (ATH-940)

Filed 2026-05-03 by Sonnet sub-agent at asabi's direction.

## Mathlib gap (verified absent)

`grep -rn "consensus|Paxos|FLP|Fischer|Byzantine|byzantine|quorum|two_phase_commit|Raft|raft|vector_clock|lamport_timestamp|happens_before|fault.tolerant|BFT|bft|impossibility.*consensus|async.*fault|distributed.*protocol"` → 0 hits in any distributed-systems context.

Mathlib HAS: `Finset.card_union_add_card_inter` (combinatorial primitive), `Relation.TransGen`, `IsLinearOrder`, `Fintype.card`. None applied to distributed events.



## Paxos / Single-Decree Consensus (6)

1. **paxos_quorum_intersection** [easy] Two majorities of finite node set share a member. Citation: Lamport 2001 §2.
2. **paxos_single_decree_safety** [medium] Two chosen values must be equal. Citation: Lamport 1998 Theorem 1.
3. **paxos_no_two_leaders** [easy-medium] At most one leader per ballot. Corollary of #1.
4. **paxos_value_locked_across_ballots** [medium] Higher ballots propose previously-chosen values. Citation: Lamport 1998 Invariant P2c.
5. **paxos_prepare_response_uniqueness** [easy] Phase-1b function is well-defined. Citation: Lamport 2001.
6. **multi_paxos_state_machine_replication_safety** [easy] Multi-Paxos safety = slot-wise single-decree safety. Citation: Lamport 2001 §3.

## FLP / Impossibility (3)

7. **flp_bivalent_initial_configuration** [hard] Bivalent initial configuration exists. Citation: FLP 1985 Lemma 2.
8. **flp_impossibility** [hard] No async deterministic consensus with 1 fault. Citation: FLP 1985 Theorem 1.
9. **cap_impossibility_linearizable_partition** [hard] No linearizable + available + partition-tolerant. Citation: Gilbert-Lynch 2002.

## Byzantine / BFT (4)

10. **byzantine_quorum_intersection** [medium] n>3f ⟹ any two Byz quorums share correct member. Citation: Lamport-Shostak-Pease 1982; Castro-Liskov 1999.
11. **pbft_safety** [med-hard] PBFT prepare-commit safety: agreement on requests. Citation: Castro-Liskov 1999 Theorem 1.
12. **byzantine_generals_lower_bound** [hard] n ≤ 3f ⟹ no Byz agreement. Citation: Lamport-Shostak-Pease 1982 Theorem 1.
13. **digital_signature_bft_threshold** [hard] Authenticated messages reduce threshold to 2f+1. Citation: Dolev-Strong 1983.

## Time / Clocks / Causal Ordering (4)

14. **lamport_clock_monotone** [easy] Local-event Lamport clock strictly increasing. Citation: Lamport 1978 Rule 1.
15. **lamport_clock_happens_before** [medium] Clock condition: happens-before ⟹ clock<. Citation: Lamport 1978 Theorem 1.
16. **vector_clock_causality_completeness** [medium] Vector clocks: hb iff componentwise < (sound + complete). Citation: Fidge 1988; Mattern 1989.
17. **lamport_total_order_extends_happens_before** [easy-medium] Lamport total order is a linear extension of hb. Citation: Lamport 1978 §3.

## Atomic Commit / 2PC (3)

18. **two_phase_commit_agreement** [easy] If any commits, no aborts. Direct from hypotheses.
19. **two_phase_commit_validity** [easy] All-yes ⟹ commit; any-no ⟹ all abort. Citation: Gray-Reuter 1992 §7.4.2.
20. **two_phase_commit_blocking_under_coordinator_failure** [medium] Cohort blocks indefinitely without coordinator. Citation: Bernstein-Hadzilacos-Goodman 1987 §7.4.3.

## Difficulty mix

| | Easy | Medium | Hard |
| - | - :| - :| - :|
| Count | 7 | 6 | 7 |

## Starter theorem (fire to Aristotle today)

**paxos_quorum_intersection**  -  easy, reduces to `Finset.card_union_add_card_inter` + Nat arithmetic, foundational for Paxos chain.

## Build order

#1 → #3, #5; #1+#4 → #2; #2 → #6; #10 → #11; #14+#15 → #17; #18 → #20. Theorems #7, #8 require their own Configuration machinery; #9, #12, #13 each need separate adversary-model infrastructure.
