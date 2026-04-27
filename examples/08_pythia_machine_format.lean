/-
examples/08_pythia_machine_format.lean — agent-loop output sample.

`pythia?` always emits a human-readable "closed by <rung>" message.
When the `pythia.bang.machineFormat` Lean option is set, it ALSO emits a
tagged log line `[pythia.bang.result] {"rung": ...}` (success) or
`[pythia.bang.failure] {"reason": ...}` (failure) carrying structured
JSON for agent-loop consumption.

Pattern lifted from rustc's `--error-format=json` and lean-lsp-mcp's
tagged-log-line outputs: single output stream, dual-purpose tags,
friendly to interactive `pythia?` users + parseable from kairos's
`lake build` subprocess wrapper.

The kairos MCP server (ATH-727) greps `^\[pythia\.(result|failure)\] `
on the build output and parses the JSON tail; older pythia versions
without the tag degrade gracefully.

## How to consume

Agent / SDK side:

```python
import re, json
# Run lake build, capture stdout
RESULT_LINE = re.compile(r"^\[pythia\.(result|failure)\] (.*)$", re.MULTILINE)
for kind, payload in RESULT_LINE.findall(build_output):
    record = json.loads(payload)  # {"rung": "anytime_valid"} etc.
    ...  # decide refinement next_action
```

Interactive Lean / human side:

```lean
example : 0 ≤ 1 := by pythia?
-- "closed by ..." message; ignore the tagged line
```

The structured log line is only emitted under
`set_option pythia.bang.machineFormat true`, so interactive sessions
stay clean by default.
-/
import Pythia.Tactic.Pythia
import Pythia.Tactic.PythiaBang

namespace Pythia.Examples.MachineFormat

/-! ### Default mode — only the human-readable line. -/

example : (1 : ℝ) ≤ 1 := by pythia?

/-! ### Machine-format mode — tagged log line emitted alongside. -/

set_option pythia.bang.machineFormat true in
example : (1 : ℝ) ≤ 1 := by pythia?

set_option pythia.bang.machineFormat true in
example (a b : ℝ) (h1 : a ≤ b) : a ≤ b := by pythia?

set_option pythia.bang.machineFormat true in
example (n : ℕ) : n + 0 = n := by pythia?

end Pythia.Examples.MachineFormat
