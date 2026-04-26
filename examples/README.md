# Examples

End-to-end working code that downstream Lean projects can copy-paste.
Every example here builds against the pinned library
(`require pythia from git ".../pythia" @ "main"`) and closes the goal
with no `sorry`. Each file is a single self-contained `example` block
with the imports it actually needs.

| File | What it shows |
|------|---------------|
| `01_pythia_smoke.lean` | The headline `pythia` tactic on a trivial registered lemma + a Mathlib fall-through goal. |
| `02_anytime_valid_smoke.lean` | The `anytime_valid` tactic closing both the countable-time and finite-horizon Ville bounds. |
| `03_cs_families_introspection.lean` | The `#cs_families` and `#ville` commands listing the registered CS families. |
| `04_betting_cs_admissibility.lean` | Full betting-CS admissibility theorem invocation with the recommended hypothesis order. |

All files build via `lake build Pythia` (transitively via `import Pythia`).

To run a single file as a smoke test:

```bash
lake env lean examples/01_pythia_smoke.lean
```

Exit code 0 + no `[error]` lines = the example builds.
