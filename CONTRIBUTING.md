# Contributing to pythia

Thanks for your interest. Pythia is the Lean 4 stats automation library
that wants to be aesop-comparable for everything statistics. Every PR
should make a working statistician's day faster.

## What pythia is, and is not

**Pythia is** an Apache-2.0 Lean 4 + Mathlib v4.28.0 library:
- Theorems Mathlib doesn't (yet) cover — anytime-valid CS, sequential
  testing, e-detectors, Bernstein/Bennett/Freedman, empirical processes,
  stochastic approximation, info-theoretic divergences, modern
  high-dim probability, conformal prediction.
- Tactics for stats reasoning — `pythia` (domain hammer), `stats_ineq`
  (inequality hammer), `pdf_simp` (probability normalization),
  `anytime_valid` (Ville closer), `sequential_stats` (planned).
- Attributes + commands for discoverability — `@[stat_lemma]`,
  `@[cs_family]`, `@[stats_ineq]`, `@[prob_simp]`, `#stat_lemmas`,
  `#cs_families`, `#concentration` (planned).

**Pythia is NOT** an LLM library. No machine-learning runtime, no
cloud calls, no external API keys, no auto-formalization endpoints. It
runs entirely offline against any Lean 4 + Mathlib install.

LLM-driven autoformalization, multi-prover swarm orchestration, and
Aristotle integration live separately in
[`athanor-sdk`](https://github.com/athanor-ai/athanor-sdk) (the
companion `athanor-kairos` PyPI package).

## Hard rules

These come from the project's safety-critical mandate. Pull requests
that don't comply will be sent back regardless of how clever the
content is.

### 1. Never push if Lean doesn't compile

`lake build` must succeed before any push to any branch. The
`tools/pre-push.sh` hook enforces this locally; install with:

```bash
ln -s ../../tools/pre-push.sh .git/hooks/pre-push
```

CI runs the same check on every branch push, so a broken push fails
status visibly. Fix the build before pushing again. Don't push and
"hope CI catches it later" — that pattern is what the hook prevents.

### 2. Axiom-clean against the trusted triple

Every theorem that joins `Kairos.Stats.API` must depend only on
`{propext, Classical.choice, Quot.sound}` — the standard Lean kernel
axiom set. Anything else (a lingering `sorryAx`, a custom `axiom Foo`
declaration, a `@[implemented_by]` shortcut on theorem-level defs)
fails the audit. Audit a single theorem with:

```lean
#print axioms Kairos.Stats.your_theorem
```

`Kairos/Stats/AxiomAudit.lean` runs the audit across the public API
on every commit; CI enforces.

Sorries on scaffold files (clearly flagged in the module docstring +
excluded from the audit's import list) are acceptable as in-flight
markers, *with a tracking ticket and an active path to closure*.
Indefinite sorries decay into lies as readers forget the provisional
status — close them or remove them.

### 3. No fake closures, no vacuous lemmas

If a tactic fires `rfl` / `unfold; grind` / `decide` and closes the
goal, the goal might have been trivial as stated. Don't ship the
proof — restate the lemma as a *by-construction invariant* or raise
the claim. We've been bitten by this before; reviewers will push back.

### 4. No LLM coupling in the library

Pythia is offline-first. If your contribution imports an HTTP client,
calls a model API, or requires a cloud key, it belongs in
[`athanor-sdk`](https://github.com/athanor-ai/athanor-sdk), not here.
The Lean kernel must accept your work without internet access.

The cross-prover hammer (Z3/Dafny/EBMC/CBMC/Vampire — see ROADMAP) is
an exception: those are *deterministic external solvers*, not LLMs.
Their certificates always reconstruct into Lean tactic syntax checked
by the kernel.

### 5. Native UX, not library-shaped

Tactics should read as Lean syntax, not as third-party invocations.
The bar is `aesop` / `simp` / `linarith`. Examples of what we mean:

- ✅ `by pythia` (reads as a Lean tactic)
- ❌ `by Pythia.run config.default` (reads as a library call)
- ✅ `@[stat_lemma]` (reads like `@[simp]`)
- ❌ `@[Pythia.Tactic.Decoration.statLemma]` (reads like a Java
  classpath)

Error messages match Mathlib's tone — terse, actionable, no
project-specific jargon. Documentation goes in `docs/` mirroring the
Mathlib `Mathlib/Tactic/Foo.lean` ↔ `docs/foo.md` convention.

## How to add a new theorem

1. **Read the [`ROADMAP.md`](ROADMAP.md)** — the multi-tier plan
   already lists the priority candidates. If your theorem is on the
   roadmap, claim it on the relevant Linear ticket (ATH-591/*) before
   starting.
2. **Pick the right module**. Concentration → `Kairos.Stats.SubGaussianMG` or `SubGamma`. CS family → `Kairos.Stats.HowardRamdasCS` etc. Pure measure-theory infra → `Kairos.Stats.MeasureTheory.<topic>`. Information theory → `Kairos.Stats.InfoTheory.<topic>`.
3. **State the theorem first**. Open a *scaffold PR* with the statement + an honest sorry + a closure plan in the docstring. Mark the module excluded from `AxiomAudit` until closure lands.
4. **Tag it for the tactic suite**. Concentration / inequality / closing-form lemmas get `@[stat_lemma]` (pythia hammer). Monotonicity / nonneg / ranking lemmas get `@[stats_ineq]`. Probability-normalization simp lemmas get `@[prob_simp]`. Aesop ruleset name `Kairos.Stats` is the umbrella.
5. **Close the proof**. Local Mathlib first (linarith / nlinarith /
   gcongr / aesop / fun_prop / measurability). External-prover hammer
   (Z3, EBMC, etc.) when the goal is in their wheelhouse. If you need
   Aristotle for a hard structural piece, that's fine — the
   reconstruction must compile in Lean kernel.
6. **Wire to `Kairos.Stats.API`**. Once axiom-clean, add the theorem
   name to the audit list + the public API umbrella.
7. **Add tests**. At least 1 regression test that the `pythia` tactic
   closes the headline goal in 1 line; 1 example using the theorem
   directly.
8. **Update [`ROADMAP.md`](ROADMAP.md)** to check off the entry and
   note the version it landed in.
9. **PR review**: per the Aidan 2026-04-25 fleet rule, one peer LGTM
   from any other agent (`research`, `qa`, `platform`, `cto`)
   unblocks admin-merge. CI must be green; the merge state must be
   `MERGEABLE`.

## How to add a new tactic

Same as theorems, plus:

10. **Document the tactic** in a `docs/<tactic>.md` page mirroring
    Mathlib's tactic-doc style.
11. **Ship a test file** at `Kairos/Stats/Tactic/<Foo>Test.lean` with
    at least 5 worked examples. Tests must close in <500ms each on
    CI runner hardware.
12. **Add an `examples/` entry** for copy-paste-ready user code. The
    bar is "a new user can lift this snippet into their project and
    it works."

## Coordination protocol

Most-active channel: `#dev-research` for research work,
`#dev-platform` for SDK/platform infra, `#agent-founder` for founder
asks. Linear ATH-591/* tickets track all pythia work.

Pinging conventions:
- *Cross-fleet* discussion (research / qa / platform / cto): same
  channel + same thread, `<@UID>` mentions in body.
- *Founder asks*: never repost to `#agent-founder` unless the
  founder is the audience; default to the dev-* channel that
  matches the topic.

## Reading list

- [`ROADMAP.md`](ROADMAP.md) — the multi-tier theorem plan + cross-domain candidate pool.
- [`docs/lean_lsp_mcp_setup.md`](docs/lean_lsp_mcp_setup.md) — sub-second LSP feedback for serious users.
- [`demo/README.md`](demo/README.md) — 5-minute walkthrough.
- [`examples/`](examples/) — copy-paste user code.

## License

Apache-2.0. By submitting a PR you license your contribution under
Apache-2.0 to the project.

## Acknowledgments

This library would not exist in its current form without
[Harmonic](https://harmonic.fun) and the Aristotle theorem prover.
See the README "Acknowledgments" section for details.
