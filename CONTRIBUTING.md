# Contributing to pythia

Thanks for your interest. Pythia is the Lean 4 stats automation library
that wants to be aesop-comparable for everything statistics. Every PR
should make a working statistician's day faster.

By participating, you agree to abide by the
[Code of Conduct](CODE_OF_CONDUCT.md).

## What pythia is, and is not

**Pythia is** an Apache-2.0 Lean 4 + Mathlib v4.28.0 library:
- Theorems Mathlib doesn't (yet) cover: anytime-valid CS, sequential
  testing, e-detectors, Bernstein/Bennett/Freedman, empirical processes,
  stochastic approximation, info-theoretic divergences, modern
  high-dim probability, conformal prediction.
- Tactics for stats reasoning: `pythia` (domain hammer), `stats_ineq`
  (inequality hammer), `prob_simp` (probability normalization),
  `anytime_valid` (Ville closer), `z3_check` (Z3 oracle + reconstruction).
- Attributes + commands for discoverability: `@[stat_lemma]`,
  `@[cs_family]`, `@[stats_ineq]`, `@[prob_simp]`, `#stat_lemmas`,
  `#cs_families`.

**Pythia is NOT** an LLM library. No machine-learning runtime, no
cloud calls, no external API keys, no auto-formalization endpoints. It
runs entirely offline against any Lean 4 + Mathlib install.

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
"hope CI catches it later": that pattern is what the hook prevents.

### 2. Axiom-clean against the trusted triple

Every theorem that joins `Pythia.API` must depend only on
`{propext, Classical.choice, Quot.sound}`: the standard Lean kernel
axiom set. Anything else (a lingering `sorryAx`, a custom `axiom Foo`
declaration, a `@[implemented_by]` shortcut on theorem-level defs)
fails the audit. Audit a single theorem with:

```lean
#print axioms Pythia.your_theorem
```

`Pythia/AxiomAudit.lean` runs the audit across the public API
on every commit; CI enforces.

Sorries on scaffold files (clearly flagged in the module docstring +
excluded from the audit's import list) are acceptable as in-flight
markers, *with a tracking issue and an active path to closure*.
Indefinite sorries decay into lies as readers forget the provisional
status: close them or remove them.

### 3. No fake closures, no vacuous lemmas

If a tactic fires `rfl` / `unfold; grind` / `decide` and closes the
goal, the goal might have been trivial as stated. Don't ship the
proof: restate the lemma as a *by-construction invariant* or raise
the claim. We've been bitten by this before; reviewers will push back.

### 4. No LLM coupling in the library

Pythia is offline-first. If your contribution imports an HTTP client,
calls a model API, or requires a cloud key, it does not belong here.
The Lean kernel must accept your work without internet access.

The cross-prover hammer (Z3 today; Dafny / EBMC / CBMC / Vampire planned)
is an exception: those are *deterministic external solvers*, not LLMs.
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

Error messages match Mathlib's tone: terse, concrete, no
project-specific jargon. Documentation goes in `docs/` mirroring the
Mathlib `Mathlib/Tactic/Foo.lean` ↔ `docs/foo.md` convention.

## How to add a new theorem

There are two tracks. Pick the one that matches your contribution.

### Track A: cross-domain closed-form fact (the quick path)

For a single named fact from chemistry, biology, economics, engineering,
mechanics, control, OR, signal processing, or similar fields. One Lean
file, one Python runner. Most community contributions fit here.

1. **Pick a target.** A textbook fact that closes in one screen of Lean
   and isn't in mathlib by name. Examples already shipped:
   Cobb-Douglas constant returns to scale, Arrhenius rate positivity,
   Hardy-Weinberg conservation, Lotka-Volterra equilibrium positivity,
   risk-neutral call non-negativity, Hooke spring potential energy
   non-negativity, scalar Lyapunov stability.

2. **Scaffold via the CLI.** The `tools/add_theorem.py` script writes
   the Lean module + the Python runner skeleton + appends a manifest
   entry in one command:

   ```bash
   python3 tools/add_theorem.py \
       --domain Mechanical \
       --name bernoulli_invariant \
       --statement '...your full Lean theorem statement...' \
       --summary 'one-sentence customer-facing description' \
       --strategy 'p1=floats(0,1e6),v1=floats(0,100),...' \
       --reference 'Bernoulli, D. Hydrodynamica (1738)'
   ```

   This creates `Pythia/Mechanical/BernoulliInvariant.lean`,
   `tools/sim/mechanical_bernoulli_invariant.py`, and patches
   `tools/sim/theorem_manifest.py`. Add `--dry-run` to preview.

3. **Fill in the proof.** Replace `by sorry` with a real tactic. Most
   targets close in 1-3 tactics: `positivity`, `linarith`, `nlinarith`,
   `ring`, `field_simp`, `mul_pos`, `div_nonneg`, etc. Tag with
   `@[stat_lemma]` so the cascade picks it up.

4. **Fill in the runner.** Implement the spec body (the empirical
   form returning `True` when the bound holds within `rtol=1e-9`) and
   add 3 mutations from `tools/sim/mutations.py`:

   - `negate_value` flips the verdict
   - `drop_factor` pins one parameter to a constant
   - `swap_inequality` is an alias for `negate_value`
   - `strict_bound_below` / `strict_bound_above` strengthen the bound
   - `custom_transform` is the escape hatch for domain-shaped mutations

5. **Verify locally.**

   ```bash
   lake build Pythia.<Domain>.<Name>
   python3 -m tools.sim.<domain>_<name>
   python3 tools/run_pythia_sim.py
   ```

   The first builds the Lean proof + the axiom audit. The second runs
   the runner with full 10 000-draw PBT + sweep + mutations. The
   third runs every manifest-listed runner (regression sweep).

6. **Open the PR.** CI runs `Lean Build + Axiom Audit` and the
   `Pythia simulation sweep`. Both must pass before a maintainer can
   admin-merge.

### Track B: statistics-spine theorem (the deep path)

For larger contributions inside the statistics core: anytime-valid
confidence sequences, concentration inequalities, e-detectors,
information-theoretic divergences, sequential testing, conformal
prediction, etc. These typically live in `Pythia.SubGaussianMG`,
`Pythia.SubGamma`, `Pythia.HowardRamdasCS`, `Pythia.InfoTheory.<topic>`,
or `Pythia.MeasureTheory.<topic>`.

1. **Open an issue first** to scope the change and avoid duplicate work.
2. **Pick the right module.** Concentration → `Pythia.SubGaussianMG` or
   `SubGamma`. CS family → `Pythia.HowardRamdasCS` etc. Pure
   measure-theory infra → `Pythia.MeasureTheory.<topic>`. Information
   theory → `Pythia.InfoTheory.<topic>`.
3. **State the theorem first.** Open a *scaffold PR* with the statement
   + an honest sorry + a closure plan in the docstring. Mark the module
   excluded from `AxiomAudit` until closure lands.
4. **Tag it for the tactic suite.** Concentration / inequality /
   closing-form lemmas get `@[stat_lemma]` (pythia hammer). Monotonicity
   / nonneg / ranking lemmas get `@[stats_ineq]`. Probability-
   normalization simp lemmas get `@[prob_simp]`. Aesop ruleset name
   `Pythia` is the umbrella.
5. **Close the proof.** Local Mathlib first (linarith / nlinarith /
   gcongr / aesop / fun_prop / measurability). External-prover hammer
   (Z3 etc.) when the goal is in their wheelhouse. The reconstruction
   must compile in Lean kernel.
6. **Wire to `Pythia.API`.** Once axiom-clean, add the theorem name to
   the audit list + the public API umbrella.
7. **Add tests.** At least 1 regression test that the `pythia` tactic
   closes the headline goal in 1 line; 1 example using the theorem
   directly.
8. **PR review.** One approving review from any other contributor +
   green CI before merge.

## How to add a new tactic

Same as theorems, plus:

9. **Document the tactic** in a `docs/<tactic>.md` page mirroring
   Mathlib's tactic-doc style.
10. **Ship a test file** at `Pythia/Tactic/<Foo>Test.lean` with
    at least 5 worked examples. Tests must close in <500ms each on
    CI runner hardware.
11. **Add an `examples/` entry** for copy-paste-ready user code. The
    bar is "a new user can lift this snippet into their project and
    it works."

## Reading list

- [`docs/lean_lsp_mcp_setup.md`](docs/lean_lsp_mcp_setup.md): sub-second LSP feedback for serious users.
- [`demo/README.md`](demo/README.md): 5-minute walkthrough.
- [`examples/`](examples/): copy-paste user code.

## License

Apache-2.0. By submitting a PR you license your contribution under
Apache-2.0 to the project.

## Acknowledgments

See the README "Acknowledgments" section.
