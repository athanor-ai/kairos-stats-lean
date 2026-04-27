# Reflective oracles: EBMC, CBMC, Dafny

How the kernel-clean reconstruction story works for oracles whose
native logic is not directly expressible as a Lean tactic.

## The reconstruction problem

Z3, CVC5, Vampire, and E all answer `unsat` on a goal that maps
cleanly to a Lean fragment with a built-in proof-producing decision
procedure: `linarith` for QF_LRA, `bv_decide` for QF_BV, `aesop` with
premise selection for FOL. The oracle's verdict tells us "this goal
is provable in Lean's logic"; the existing Lean tactic then
constructs the kernel-checked proof term.

EBMC, CBMC, and Dafny are different. They run model-checking against
languages with their own operational semantics: EBMC checks LTL/CTL
properties on SystemVerilog circuits, CBMC checks assertions on C
programs, Dafny checks Hoare triples on Dafny methods. Their verdicts
do not map directly to a Lean tactic. There is no
`systemverilog_decide` or `c_decide` in Mathlib, and embedding the
operational semantics of SystemVerilog or C in Lean is a multi-year
formalization project (cf. CompCert for C, FLOWHOOK for Verilog).

Pythia's architectural rule is unambiguous: **every public theorem
closes against `{propext, Classical.choice, Quot.sound}`. No external
verdict can close a Lean goal**. So how do EBMC / CBMC / Dafny ever
contribute?

## Reflective restriction

The kernel-clean route is to restrict each oracle to goals whose
*Lean shadow* admits a reflective decision procedure. The shadow is
the Lean version of the same property, written in a fragment where
Lean's `decide` tactic (or a domain-specific reflective tactic)
already produces a kernel-checked proof term.

### EBMC: clocked `Decidable BitVec` properties

Scope: a SystemVerilog assertion of the form

```
assert property (@(posedge clk) p);
```

where `p` is a Boolean combination of bit-vector equalities and
inequalities over signals of bounded width. The Lean shadow is

<!-- doctest: skip-reason: depends on user-defined p_lean / CircuitState -->
```lean
theorem my_assertion : ∀ (s : Σ (n : ℕ), CircuitState n), p_lean s := by
  decide
```

EBMC's role: confirm the assertion holds on the bounded model. If
EBMC says `unsat` for the negation, pythia's `ebmc_check` adapter
reconstructs the proof via `Pythia.SV.decide_circuit_assertion`, a
Lean tactic that unfolds the SystemVerilog-to-Lean translation
(maintained in the `kairos.sv` adapter, which is OSS) and asks
`decide` to close. The tactic is sound by construction: it never
trusts EBMC's verdict, only uses it as a hint that `decide` will
succeed. If `decide` fails, the tactic fails loudly.

Out of scope: continuous-time properties, unbounded counters,
properties with quantifier alternation over unbounded domains. These
fall out of fragment and the matcher routes them elsewhere (or to the
fallback chain).

### CBMC: bounded loop invariants

Scope: a C function with a loop annotated `@[loop_invariant]` whose
invariant is a quantifier-free predicate over machine integers, and
whose loop bound is a small literal (so reflection terminates). The
Lean shadow is a `BoundedLoop.simulate` call that unfolds the loop
into a finite `Nat.rec` and asks `decide` to verify the invariant at
each step.

CBMC's role: confirm the invariant holds for the actual C
semantics. The adapter reconstructs via the same
`BoundedLoop.simulate` Lean term: CBMC's verdict is a hint, not the
proof. The reflective decision procedure handles the kernel-checked
side.

Out of scope: unbounded loops, pointer aliasing, dynamic memory.
These fall through to the standard chain.

### Dafny: extracted Hoare triples

Scope: a Dafny method with pre/postcondition expressed in a fragment
that maps to Lean's `Hoare` predicate (over a small imperative
language whose operational semantics IS formalized in Lean: assign,
sequence, conditional, bounded while). The Lean shadow is a
`Hoare.derive` call that constructs the proof tree directly via the
Hoare rules.

Dafny's role: confirm the triple holds. The adapter reconstructs via
`Hoare.derive`, which is a kernel-checked tactic that builds the
derivation tree from the program syntax. Dafny's verdict is a hint.

Out of scope: programs with features outside the embedded fragment
(arrays, recursion, classes). These fall through.

## Why bother?

If reconstruction does the real work, why query the oracle at all?
Two reasons:

1. *Filter*. The oracle is faster than Lean's reflection on large
   bit-widths or deep loop unrolls. Querying first lets us skip the
   reflective step when the oracle says `sat` (the goal is unprovable
   in the underlying logic, no point asking Lean to try).

2. *Scope discipline*. The oracle's shape requirements force the
   user to write goals in the reflective fragment. If a goal doesn't
   encode to SystemVerilog / C / Dafny, the oracle says `outOfFragment`
   and the matcher routes elsewhere. This keeps the reflective
   decision procedures from being used on goals they can't handle.

## Status

| Oracle | Reflective fragment           | Adapter status    | Decision proc                        |
|--------|-------------------------------|-------------------|--------------------------------------|
| EBMC   | bounded BitVec circuit assert | design only       | `Pythia.SV.decide_circuit_assertion` |
| CBMC   | bounded-loop invariants       | design only       | `Pythia.C.BoundedLoop.simulate`      |
| Dafny  | embedded Hoare fragment       | design only       | `Pythia.Hoare.derive`                |

These three adapters do not yet ship in pythia. The reflective
decision procedures are the gating dependency: without
`Pythia.SV.decide_circuit_assertion` etc., the adapters cannot
reconstruct kernel-clean proofs and would have to inject custom
axioms, which violates the axiom-budget rule. Phase 6+ work.

For the v1 scope of pythia's cross-prover hammer, the realistic
oracle coverage is Z3 + CVC5 + Vampire + E. EBMC / CBMC / Dafny are
documented here so the architecture story is complete and the route
to land them is clear.
