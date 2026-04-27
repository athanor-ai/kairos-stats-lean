# `pythia!`: hammer ladder orchestrator

`pythia!` is the headline one-call closer for the pythia library.
Given any goal in scope, it walks a 9-rung ladder of closure tactics
in priority order and reports success on the first rung that closes
the goal. The verbose variant `pythia?` reports the closing rung plus
per-rung wall-clock timing so you can see what paid off.

## Naming history (ATH-756)

The tactic shipped originally as `pythia!!` in ATH-753 / PR #48.
ATH-756 / PR #51 renamed it to `pythia!` to match the Lean idiom
(`simp!`, `field_simp!` use a single bang for the "more aggressive"
variant). The verbose form moved from `pythia!?` to `pythia?` to
match `apply?` / `rw?` / `simp?` / `aesop?` (the `?` suffix
universally means "show me what you did").

The legacy spellings `pythia!!` and `pythia!?` survive as deprecated
aliases for one minor version and emit a warning on use. Migrate to
`pythia!` / `pythia?` everywhere; the semantics are identical.

## What `pythia!` is

A single-tactic gateway to the full pythia closer surface. Use it when
you are not sure which tactic will close your goal and want the system
to try every plausible one without writing a long `first | ... | ...`
chain by hand.

## What `pythia!` is not

Not a proof-search engine. Not a hammer in the Sledgehammer sense.
Each rung is a fail-fast attempt at an existing closure tactic. There
is no premise selection, no LLM-driven exploration, and no automatic
hypothesis generalization. Use `pythia` (the shape-dispatch tactic)
for goals where you want the cheap path, and write tactics by hand
when you already know what closes your goal.

## The ladder

| Rung | Tactic                                  | Typical budget | Notes                                            |
|------|-----------------------------------------|----------------|--------------------------------------------------|
| 1    | `stat_simp` then `simp only [stat_simp]` then `simp` | < 50ms | ATH-754 / ATH-758 `@[stat_simp]` curated set first, falls through to bare simp |
| 2    | `linarith` / `nlinarith` / `polyrith`   | 50-300ms       | numeric arithmetic; tried in ascending cost order |
| 3    | `positivity`                            | < 50ms         | non-negativity goals                             |
| 4    | `aesop` on the `Pythia` ruleset         | 100-500ms      | every `@[stat_lemma]` registered theorem         |
| 5    | `pythia`                                | 200-800ms      | shape-dispatch cascade plus `@[stat_lemma]`      |
| 6    | `z3_check`                              | 200-1000ms     | QF_LRA over ℝ via Z3 + `linarith` reconstruction |
| 7    | `cvc5_check`                            | 200-1000ms     | QF_BV via CVC5 + `bv_decide`; QF_LRA backup      |
| 8    | `vampire_check` / `e_check`             | 500-2000ms     | first-order logic via Vampire and E              |
| 9    | `disprove`                              | 200-800ms      | counterexample finder; useful to catch vacuous statements |

Each rung runs under a per-rung heartbeat budget (default 500ms). On
exception or budget exhaustion the ladder advances to the next rung.
The first rung to close the goal wins.

## Rung 1: the `@[stat_simp]` hook (ATH-758)

Rung 1 wires the `@[stat_simp]` curated simp set in front of bare
`simp`. The `@[stat_simp]` set (ATH-754) carries roughly 39
probability + ENNReal normal-form lemmas: `ENNReal.toReal_ofReal`
round-trips, `Set.indicator_of_mem` / `_of_notMem` / `_univ` /
`_empty` rewrites, `Measure.real` ↔ `(μ s).toReal` bridging,
`condExp_const` push-throughs, and the `IsProbabilityMeasure` axiom
`μ Set.univ = 1`.

Because rung 1 fires first, every downstream rung (linarith, aesop,
oracles, disprove) sees a goal already in the canonical form. A
goal like `(ENNReal.ofReal x).toReal = x` (which bare `simp` does
NOT close on its own) is closed by rung 1 directly; a goal like
`0 ≤ a.toReal + 1` is normalized at rung 1 and closed by linarith
at rung 2. See `Pythia/Tactic/PythiaBangTest.lean` Section 15 for
representative regression cases.

The fall-through inside rung 1 is `stat_simp` (the wrapper tactic),
then `simp only [stat_simp]` (raw simp set without the wrapper's
discharger), then bare `simp` (full general simp). Each fallthrough
is gated with `done` so partial progress that does not close the
goal does not commit the rung.

## Why no neural rung?

`pythia!` is deliberately LLM-free. The pythia library is offline-
first and kernel-clean per CONTRIBUTING rule 4: no HTTP clients, no
model APIs, no cloud keys. Adding an LLM rung would couple the public
Apache-2.0 library to a model endpoint and break the offline-build
guarantee that lets reviewers run `lake build` without network access.

The deterministic external oracles on rungs 6-9 (`z3_check`,
`cvc5_check`, `vampire_check`, `e_check`) are NOT language models.
They are SMT and first-order ATP solvers (Z3, CVC5, Vampire, E) that
return either a proof certificate or `unsat` and whose results are
reconstructed inside Lean by `linarith`, `bv_decide`, or `aesop`.
A wrong oracle answer cannot land an unsound proof: the kernel
re-checks every step.

LLM-augmented closure (DSPv2 inline drafters, Aristotle remote queue,
multi-agent cycle proving, premise retrieval, and so on) lives in the
companion `kairos-sdk` package under `kairos.lean_cycle.cycle_prove`.
That package is the right place for model coupling: it talks to model
endpoints, manages async queues, and ships proof candidates back into
this library where the deterministic ladder + the Lean kernel give
the final yes / no. If you want the full LLM-augmented surface, call
`kairos.lean_cycle.cycle_prove` from your sdk-side tooling and feed
its outputs to `pythia!` for kernel re-verification.

## When to use `pythia!`

Use `pythia!` when:

* You are writing a fresh proof and want a fast smoke check that the
  goal is closable by any registered tactic.
* You are porting a paper and want to see what the library can do
  before reaching for hand-written automation.
* You want a single failure mode: either the goal closes or no rung
  works, with the verbose variant telling you what was tried.

Use plain `pythia` instead when:

* You know your goal matches a specific shape (Ville-bound,
  concentration tail, probability rewriting). `pythia!` will get
  there too but pays for the cheaper rungs first.
* You are inside a tight loop and want predictable timing.

Write tactics by hand when:

* You know the exact closer (`linarith`, `simp [foo, bar]`, etc.).
* You need to thread auxiliary lemmas or hypotheses into the closer.

## How to extend (add a new rung)

1. Open `Pythia/Tactic/PythiaBang.lean`.
2. In `buildRungs`, declare a new ``TSyntax `tactic`` literal naming
   the closure tactic (must end with `done` so partial closures do
   not commit the rung). The closer must be deterministic and
   offline-runnable; LLM-coupled closers belong in the kairos-sdk
   companion, not here.
3. Append a new `Rung` row to the returned array at the slot that
   matches the rung's expected cost. Cheaper rungs go first.
4. Add a regression case in `Pythia/Tactic/PythiaBangTest.lean`: a
   tiny example where the new rung is the one that closes (verifies
   dispatch correctness).
5. Run `lake build Pythia.Tactic.PythiaBang` and
   `lake build Pythia.Tactic.PythiaBangTest`. Both must be green.
6. Update the table above with the rung's typical budget.

## Axiom audit

A `pythia!`-closed example reduces to a kernel term against the
Mathlib axiom budget `{propext, Classical.choice, Quot.sound}`. The
orchestrator itself adds no axioms: it merely picks which existing
tactic ran. If a closing rung's underlying tactic is itself axiom
clean, so is the `pythia!` close. The regression suite ships
`#print axioms` attestation lines for one example per major rung
family.

## Verbose mode example

```lean
import Pythia
open Pythia
example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by pythia?
```

Emits an info message:

```
pythia? — closed by `linarith_chain`. Ladder timing:
  stat_simp: failed — @[stat_simp] (ATH-754) + core simp closure
  linarith_chain: CLOSED in 8ms — linarith / nlinarith / polyrith arithmetic
  positivity: skipped (already closed)
  aesop_pythia: skipped (already closed)
  ...
```

Per-rung timing is wall-clock measured via `IO.monoMsNow`; the
budget cap is enforced via `withMaxHeartbeats` so a runaway tactic
cannot stall the ladder.

The legacy `pythia.machineFormat` option that fed agent-loop tagged
log lines moved to `pythia.bang.machineFormat` in ATH-756. Toggle
via `set_option pythia.bang.machineFormat true in pythia?` to emit
`[pythia.bang.result] {"rung": ..., "ms": ...}` (success) or
`[pythia.bang.failure] {"reason": ...}` (failure) in addition to
the human-readable summary.

## Status

ATH-753, ATH-756 (rename), ATH-758 (stat_simp hook). All 9 rungs
exercise existing tactics in the library. There are no LLM rungs
and no placeholder rungs: the ladder is the full surface. LLM-
augmented closure lives in the `kairos-sdk` companion under
`kairos.lean_cycle.cycle_prove`.
