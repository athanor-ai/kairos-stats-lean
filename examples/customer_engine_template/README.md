# Customer Engine Verification Template

Prove your custom verification engine is sound, and kairos certs
will automatically cite your proof.

## Quick start

1. Copy `MyEngine.lean` to your project
2. Replace `myEngineSpec` with your engine's specification
3. Prove `EngineSoundness` for your engine
4. Run `lake build` to verify the proof compiles
5. Your kairos cert now cites the proof object

## What you need to provide

- **EngineSpec**: what your engine takes as input, what it produces,
  and how it runs. See `myEngineSpec` in `MyEngine.lean`.

- **EngineSoundness**: a proof that when your engine returns PROVED,
  the design property actually holds. This is the soundness contract.

## What you get for free

Once your engine satisfies `EngineSoundness`, Pythia gives you:

- `engine_cert_valid`: your cert claims are backed by the proof
- `two_engine_stronger`: combining your engine with another gives
  redundant confirmation
- `engine_composition`: pipeline your engine with others soundly

## Files

- `MyEngine.lean`: starter template with inline comments
- `README.md`: this file

## Dependencies

```lean
require pythia from git
  "https://github.com/athanor-ai/pythia.git" @ "main"
```
