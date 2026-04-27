<!--
Thanks for sending a PR. The checklist below mirrors the CI checks the
repo enforces; tick what applies. New theorems usually fit the
"new theorem" section; everything else picks the "general" section.
-->

## Summary

What changed and why, in 2-3 sentences.

## New theorem (Track A: cross-domain quick path)

If this PR adds a single closed-form fact via `tools/add_theorem.py`:

- [ ] `Pythia/<Domain>/<Name>.lean` builds clean (`lake build Pythia.<Domain>.<Name>`)
- [ ] `tools/sim/<domain>_<name>.py` harness passes (`python3 -m tools.sim.<domain>_<name>`)
- [ ] All 3 mutations caught (0 missed)
- [ ] `tools/sim/theorem_manifest.py` patched with the new entry
- [ ] `python3 tools/run_pythia_sim.py` (full manifest sweep) green
- [ ] References cited in the Lean module docstring + the manifest entry
- [ ] Theorem tagged `@[stat_lemma]` (or appropriate alternative)
- [ ] Axiom-clean (the `Pythia/AxiomAudit.lean` job in CI passes)

## New theorem (Track B: statistics-spine)

If this PR adds a deeper concentration / anytime-valid / info-theory /
measure-theory result:

- [ ] Issue opened first to scope (linked below)
- [ ] Statement + honest `sorry` scaffold submitted before the proof
- [ ] Tagged for the tactic suite (`@[stat_lemma]` / `@[stats_ineq]` /
      `@[prob_simp]` as appropriate)
- [ ] `Pythia.API` umbrella + `AxiomAudit` list updated when proof closes
- [ ] At least 1 regression test in `Pythia/Tactic/<Foo>Test.lean`
- [ ] At least 1 reviewing approval

## General PR (tactic, tool, docs, infra)

- [ ] `lake build` green
- [ ] README updated if the change affects the public surface
- [ ] Tests added for any behavior change

## Linked issues

Closes #...
