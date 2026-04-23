/-
Kairos.Stats.Basic — foundational types for finite-precision statistics.

`BitPrecision` describes a fixed-point representation: bit-width `b`,
fractional scale `s`, accumulator `modelWidth`. `Time := ℕ` is the step
index. `slackFn` composes a scalar quantization-transport bound with a
family-specific `eta` to produce the deployment-slack term.
-/

import Mathlib

namespace Kairos.Stats

open scoped Classical BigOperators

/-- Time index for a discrete-time confidence sequence. -/
abbrev Time := ℕ

/-- Fixed-point representation parameters.  Internal-to-Kairos analogue
of the `BitPrecision` type used in the NeurIPS 2026 deployment-slack
paper.  `bits` is the full word-width; `scale` is the fractional-bit
count; `modelWidth` bounds the accumulator. -/
structure BitPrecision where
  bits : ℕ
  scale : ℕ
  modelWidth : ℕ
  bits_pos : 0 < bits
  scale_le_bits : scale ≤ bits

end Kairos.Stats
