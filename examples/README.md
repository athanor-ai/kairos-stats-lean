# Examples

End-to-end working code that downstream Lean projects can copy-paste.
Every example here builds against the pinned library
(`require pythia from git ".../pythia" @ "main"`) and closes the goal
with no `sorry`. Each file is a single self-contained `example` block
with the imports it actually needs.

## Tactic + library smoke tests

| File | What it shows |
|------|---------------|
| `01_pythia_smoke.lean` | The `pythia` tactic on a trivial registered lemma + a Mathlib fall-through goal. |
| `02_anytime_valid_smoke.lean` | The `anytime_valid` tactic closing both the countable-time and finite-horizon Ville bounds. |
| `03_cs_families_introspection.lean` | The `#cs_families` and `#ville` commands listing the registered CS families. |
| `04_betting_cs_admissibility.lean` | Full betting-CS admissibility theorem invocation with the recommended hypothesis order. |

## Domain starter packs

Per-field minimal examples showing how `pythia!` (or the per-domain
`@[stat_lemma]`) closes representative goals. Each starter pack is a
single Lean file under `examples/<domain>/`.

| Folder | Domain | What it shows |
|--------|--------|---------------|
| `examples/bio/` | population dynamics | Hardy-Weinberg conservation, Lotka-Volterra positivity, SIR conservation |
| `examples/economics/` | production functions | Cobb-Douglas constant returns to scale, output positivity |
| `examples/control/` | control theory | Scalar Lyapunov non-negativity, stable-decreasing condition |
| `examples/optimal_transport/` | discrete optimal transport | Wasserstein non-negativity, identical-distribution zero |
| `examples/quantum/` | quantum information | Two-state von Neumann entropy non-negativity |

Add a starter pack for your field by dropping a file at
`examples/<your-domain>/01_<topic>.lean` with three rules:

1. Single import of the relevant `Pythia.<Domain>` module
2. 1-3 `example` blocks, each closed by `pythia!` or by an explicit
   `@[stat_lemma]` invocation
3. Brief docstring above each `example` explaining the textbook
   identity being shown

All files build via `lake build Pythia` (transitively via `import Pythia`).

To run a single file as a smoke test:

```bash
lake env lean examples/01_pythia_smoke.lean
```

Exit code 0 + no `[error]` lines = the example builds.
