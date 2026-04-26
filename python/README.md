# athanor-pythia


This is the Python-side companion to the
[`pythia`](https://github.com/athanor-ai/pythia) Lean 4 statistics
library. **The real product is the Lean tactic + theorem library**
in that repository; this package currently exists as a name reservation
on PyPI (v0.0.1 placeholder).

## Status

- **Pre-release** (v0.0.1). Name reservation only.
- The Lean side ships the `pythia` tactic + the `Pythia.*` namespace + the registered lemma library.
- Future Python-side surface (planned): LSP-driven proof-closure helpers, multi-prover swarm orchestration, lean-lsp-mcp self-hosting glue. None of that lives here today; for the LLM-driven side see [`athanor-sdk`](https://github.com/athanor-ai/athanor-sdk).

## Install the Lean library

```lean
-- in your lakefile.lean
require pythia from git
  "https://github.com/athanor-ai/pythia.git" @ "main"
```

Then `import Pythia` (umbrella) or any individual `Pythia.*`
module. Toolchain pinned to Lean 4.28.0 + Mathlib v4.28.0.

## License

Apache-2.0.

## Links

- Lean library: https://github.com/athanor-ai/pythia
- Companion SDK (LLM-driven side): https://github.com/athanor-ai/athanor-sdk
- Athanor: https://athanor-ai.com
