# LLM-defense layer

How pythia + kairos catch LLM hallucinations when the customer is using
an LLM (Claude / GPT / Gemini) to generate Lean.

The realistic 2026 customer journey: applied scientist asks their LLM
"prove Bernstein's inequality for n=1000 i.i.d. Bernoulli trials,"
LLM emits Lean, customer wants confidence the result is correct. The
bottleneck is no longer "I can't write Lean," it's "the LLM
hallucinated and I can't tell." Pythia + kairos together close that
gap.

## Architecture: engine vs dashboard

**Pythia = engine.** Owns every primitive that needs MetaM /
elab / kernel access (Lean tactics, registries, axiom audits).

**Kairos = dashboard.** Owns the customer-facing orchestration:
natural-language autoformalization, dispatch, trace, audit log,
certify-composite, Vercel-side dashboard.

There is no shared code. The boundary is a `lake build` subprocess:
kairos invokes pythia tactics by writing a `.lean` file, calling
`lake build`, parsing structured output. Lean kernel stays the trusted
source of truth.

## The 8 hallucination failure modes + per-mode tools

| Mode | Failure | Tool | Home |
|------|---------|------|------|
| A | Statement hallucination (false claim that looks plausible) | counterexample-first prepass | kairos (existing cvc5 dispatcher) |
| B | Lemma hallucination (invokes nonexistent symbol) | `#validate_invoked_lemmas` | pythia (Lean meta-tactic) |
| C | Hypothesis under/over-specification | `#minimize_hypotheses` | pythia (Lean meta-tactic) |
| D | Type mismatch (wrong Lean type for stated quantity) | `#validate_types` | pythia (Lean meta-tactic) |
| E | Specification drift (Lean term differs from user intent) | NL-roundtrip generator | kairos (LLM call) |
| F | Vacuous proof (closes via False.elim from contradicted hypotheses) | vacuous-truth refusal | kairos surface (detector ladder) |
| G | Axiom smuggling (custom axiom added) | axiom-budget gate | kairos surface (allowlist) |
| H | Parameter-vs-constant confusion (LLM hard-codes literals) | `#flag_concrete_constants` | pythia (Lean meta-tactic) |

Net split: 4 of 8 land in pythia as Lean meta-tactics (B, C, D, H),
all of which need MetaM / elab / kernel access. 4 of 8 land in kairos
(A, E, F, G), which are LLM-call or orchestration shape.

## The composite: `kairos certify`

The customer-facing surface is a single command:

```
kairos certify <theorem.lean>
  ✓ Statement counterexample search: PASS
  ✓ Lemma existence: 4/4 invoked lemmas found
  ✓ Hypothesis minimization: all hypotheses load-bearing
  ✓ Type sanity: PASS
  ⚠ Spec round-trip drift: LLM said 'CI' but Lean says 'CredibleInterval'
  ✓ Vacuous-truth refusal: PASS
  ✓ Axiom audit: depends only on {propext, Classical.choice, Quot.sound}
  ⚠ Parametricity: theorem fixes n=1000; flag for user confirmation
```

Kairos wraps each pythia Lean meta-tactic via `lake build` subprocess,
parses structured output, aggregates into the 8-check JSON, surfaces
via CLI, writes to audit log.

This composite **lives entirely in kairos**. Pythia ships only the
Lean meta-tactic primitives.

## Pythia-side tactics shipped

As of pythia main `9ad09c9`:

- `#validate_invoked_lemmas <ThmName>` (Guard B): `Pythia.Tactic.ValidateInvokedLemmas`. Walks the proof term, checks every invoked declaration name against the current environment.
- `#flag_concrete_constants <ThmName>` (Guard H): `Pythia.Tactic.FlagConcreteConstants`. Walks the theorem type, detects fixed numerical literals (n=100, σ=0.5).

Pending pythia-side: `#minimize_hypotheses` (Guard C, ATH-724) and
`#validate_types` (Guard D, ATH-725).

## Kairos-side tickets

Tracked under qa's epic ATH-719 with sub-tickets:

- ATH-720: surface vacuous-truth + axiom-budget verdicts in `simple_prove`
  output (Guards F + G; existing kairos infrastructure, low-risk
  wiring).
- ATH-721: pre-pass counterexample via the existing Sledgehammer SAT
  path (Guard A; reuses cvc5 dispatcher).
- ATH-722: NL-roundtrip generator (Guard E; uses BYO-LLM for the
  reverse direction Lean -> English).
- ATH-723: `lake build` wrappers for each pythia meta-tactic (Guards
  B/C/D/H). Already unblocked for B + H since pythia main `9ad09c9`.

## Why this works

The LLM does the high-bandwidth low-trust work (English to Lean,
generating proof attempts, summarizing). Pythia does the low-bandwidth
high-trust work (kernel-checked validation, axiom audit, decidable
reflection). Kairos does the orchestration glue.

The customer never has to read Lean to know whether their LLM-emitted
proof is sound. The structured certify report is the customer-facing
surface; the Lean kernel is the trusted source.

## References

- ATH-718: pythia next-phase epic (this is where the layer split is
  recorded).
- ATH-719: kairos certify composite CLI (parent for the kairos-side
  work).
- `Pythia.Tactic.ValidateInvokedLemmas` (commit `ebb35cb`).
- `Pythia.Tactic.FlagConcreteConstants` (commit `9ad09c9`).
