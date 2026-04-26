# Sledgehammer: goal-shape dispatch

How `pythia` decides which OSS oracle to fire for a given goal.

## Why this exists

`pythia` orchestrates a small pool of open-source provers. Each oracle
has a tight competence band: Z3 closes linear-real arithmetic, EBMC
closes bit-vector / hardware assertions, Vampire and E close
first-order logic without arithmetic. Firing the wrong oracle wastes
the timeout budget; firing none falls back to Mathlib's standard
automation. The dispatch table below records how `pythia` picks the
right one.

The pattern is the Coq Sledgehammer's: `Hammer` (Czajka & Kaliszyk,
JAR 2018) for Coq, `sledgehammer` (Paulson & Susanto, ITP 2007;
Blanchette et al. 2016) for Isabelle/HOL. We adapt the discipline for
Lean 4's CIC + Mathlib.

## Architectural rule

External provers are **oracles, not trusted**. Every verdict is
reconstructed into a Lean tactic script that the kernel checks against
`{propext, Classical.choice, Quot.sound}`. Same axiom budget as
Mathlib. No claim escapes the kernel. The dispatch table only chooses
which oracle to query first; the answer it gives is never the proof.

## Goal-shape pattern → oracle

| Goal shape                                        | Logic     | Primary  | Backup     | Reconstruction          |
|---------------------------------------------------|-----------|----------|------------|-------------------------|
| `a ≤ b`, `a < b`, `a = b` linear over `ℝ`         | QF_LRA    | Z3       | CVC5       | `linarith`              |
| Linear over `ℤ` / `ℕ`                              | QF_LIA    | Z3       | CVC5       | `omega`                 |
| Polynomial inequalities over `ℝ`                  | QF_NRA    | Z3       | CVC5       | `polyrith` / `nlinarith` |
| Mixed integer + real                              | QF_LIRA   | Z3       | CVC5       | `linarith` + cast lemmas |
| Bit-vector equalities / inequalities              | QF_BV     | CVC5     | Z3         | `bv_decide` / `decide`  |
| Hardware assertion: clocked signal property       | LTL/CTL   | EBMC     | n/a          | `decide` + circuit lemma |
| C-style invariant / loop assertion                | software  | CBMC     | n/a          | reflective decision proc |
| First-order logic, no arithmetic                  | FOL       | Vampire  | E          | `aesop` premise selection |
| Method pre/postcondition (Hoare-style)            | Dafny FOL | Dafny    | n/a          | extraction adapter       |
| Probability / measure-theoretic                   | (none)    | n/a        | n/a          | `pythia` aesop ruleset   |
| Anytime-valid Ville-bound shape                   | (none)    | n/a        | n/a          | `anytime_valid` tactic   |
| Concentration / sub-Gaussian / sub-gamma tail     | (none)    | n/a        | n/a          | `stats_ineq` tactic      |
| Probability rewriting (pushforward, conditional)  | (none)    | n/a        | n/a          | `prob_simp` tactic       |

Goal shapes that fall through every band drop into `pythia`'s aesop
ruleset (the registered `@[stat_lemma]` library), then into Mathlib's
standard automation chain (`simp`, `omega`, `linarith`, `positivity`).

## Recognition: how `pythia` matches a shape

The matcher is a small list of syntactic predicates run on the
elaborated `Expr` of the goal and the local context, in order:

1. **Anytime-valid Ville shape**: target matches
   `μ {ω | ∃ t, f t ω ≥ c} ≤ _ / _`. Fired by the `anytime_valid`
   tactic. Highest priority because it's the most specific shape
   pythia is built for.
2. **Concentration tail**: target matches
   `μ {ω | f ω ≥ c} ≤ exp(-_)` or `≤ 2 * exp(-_)` with `f` a partial
   sum or mean. Routed to `stats_ineq`.
3. **Probability rewriting**: target contains `μ.map`, `condExp`,
   `MeasureTheory.lintegral`. Routed to `prob_simp`.
4. **Pure linear real arithmetic**: every leaf is `ℝ`, every operator
   is `+`, `-`, `*` (with at least one literal factor), `≤ < = ≥ >`.
   Routed to `z3_check`. (CVC5 backup once `cvc5_check` lands.)
5. **Pure linear integer / natural arithmetic**: every leaf is `ℤ` or
   `ℕ`. Routed to `omega` directly (Lean's built-in is usually faster
   than the Z3 round-trip).
6. **Polynomial real arithmetic**: linear-real check fails because of
   a multiplication of two non-literal subterms. Routed to `polyrith`,
   then `nlinarith`. Phase 3 adds Z3 with the QF_NRA logic.
7. **Bit-vector**: target has `BitVec n` or `UInt8/16/32/64` operands.
   Routed to `cvc5_check` (Phase 4 adds the adapter).
8. **Hardware**: target lives under the `Kairos.SV` namespace or has a
   clocked-signal hypothesis. Routed to `ebmc_check` (paid-tier
   adapter; OSS).
9. **Software invariant**: target has a `@[loop_invariant]` annotation.
   Routed to `cbmc_check` (paid-tier adapter; OSS).
10. **First-order, no arithmetic**: target and hypotheses are pure
    Prop / Sort with quantifiers but no arithmetic operators. Routed
    to `vampire_check`, then `e_check` (Phase 5).
11. **Hoare triple**: target is `_ ⊢ {P} c {Q}`. Routed to
    `dafny_check` (Phase 6).
12. **Fallback**: aesop with the `Pythia` ruleset, then
    `simp; omega; linarith; positivity`.

The matcher is deliberately syntactic. We never call an oracle
optimistically. If the shape doesn't match, we don't pay the
SMT-encoding cost.

## Status (2026-04-26)

| Phase | Oracle    | Status                                    |
|-------|-----------|-------------------------------------------|
| 1     | Z3        | shipped (`Pythia.Tactic.Z3Check`)         |
| 2     | CVC5      | qa scaffolding (`Pythia.Tactic.CVC5Check`) |
| 3     | EBMC      | adapter pending                            |
| 4     | CBMC      | adapter pending                            |
| 5     | Vampire/E | adapter pending                            |
| 6     | Dafny     | adapter pending                            |

Phases 3-6 follow the Z3Check template: SMT/TPTP/asgn encoding,
then `IO.Process.run`, then verdict parsing, then Lean reconstruction.
The dispatcher in `Pythia.Tactic.Pythia` pattern-matches and fires.
There is no global "try every oracle" loop; that would burn CI time
and mask which adapter actually closed the goal.

## What `pythia` does NOT do

- Run multiple oracles in parallel and take the first verdict. Each
  oracle has a competence band; we route by band, not by race.
- Trust an oracle's verdict to close the goal. The kernel reconstructs.
- Hold the customer's LLM key for autoformalization. BYO-LLM only;
  see README "Bring-your-own LLM".
- Guess. If no shape matches, fall through to aesop + Mathlib chain
  and surface a clear error message naming what was tried.

## References

- Czajka & Kaliszyk, *Hammer for Coq: Automation for Dependent Type
  Theory*, JAR 2018.
- Blanchette, Bulwahn, Nipkow, *Automatic Proof and Disproof in
  Isabelle/HOL*, FroCoS 2011.
- Paulson, *Three Years with Sledgehammer*, PAAR 2010.
- Czajka, *Practical proof search for Coq by type inhabitation*, IJCAR 2020.
