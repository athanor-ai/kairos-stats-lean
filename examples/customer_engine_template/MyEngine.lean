/-
Customer Engine Verification Template

Copy this file, replace the placeholders with your engine's
specifics, and prove soundness. Once it compiles, kairos certs
will cite your proof object.
-/
import Pythia.Hardware.EngineContract

open Pythia.Hardware.EngineContract

/-! ## Step 1: Define your engine

Replace these types and the `run` function with your engine's
actual behavior. -/

-- What your engine takes as input (e.g., two Verilog files)
structure MyInput where
  gold_design : String
  gate_design : String

-- What your engine produces
inductive MyVerdict
  | proved    -- engine verified equivalence
  | unknown   -- engine could not decide
  deriving DecidableEq

-- Your engine specification
def myEngineSpec : EngineSpec := {
  name := "my_custom_engine"
  Input := MyInput
  Output := MyVerdict
  run := fun _input =>
    -- Replace with your engine's actual logic.
    -- For now, this is a placeholder that always returns unknown.
    MyVerdict.unknown
}

/-! ## Step 2: Define the soundness contract

You need to specify:
- When is your engine's output considered "proved"?
- What does "gold equals gate" mean for your inputs?
- A proof that proved → gold_eq_gate -/

instance : EngineSoundness myEngineSpec where
  -- When does your engine say PROVED?
  is_proved := fun output => output = MyVerdict.proved

  -- What property does PROVED guarantee?
  gold_eq_gate := fun input => input.gold_design = input.gate_design

  -- The soundness proof: if your engine says PROVED, the property holds.
  --
  -- For the placeholder engine (always returns unknown), this is
  -- vacuously true because `run` never returns `proved`.
  -- Replace with your real proof when you implement `run`.
  soundness := fun input h_proved => by
    -- The placeholder engine never returns `proved`, so this
    -- case is impossible. Your real engine will need a real proof.
    simp [myEngineSpec] at h_proved

/-! ## Step 3: Use the free theorems

Once the above compiles, you get these for free: -/

-- Your cert is valid when your engine says PROVED
example (input : myEngineSpec.Input)
    (output : myEngineSpec.Output)
    (h_run : myEngineSpec.run input = output)
    (h_proved : EngineSoundness.is_proved output) :
    EngineSoundness.gold_eq_gate input :=
  engine_cert_valid myEngineSpec input output h_run h_proved

/-! ## Step 4: Verify

Run `lake build` in your project. If it compiles with no errors,
your soundness proof is machine-checked.

Then register your engine with kairos:

```python
from kairos.engine_registry import register_engine

register_engine(
    name="my_custom_engine",
    lean_module="MyEngine",
    lean_soundness_theorem="EngineSoundness",
)
```

Your kairos certs will now cite your Lean proof object. -/
