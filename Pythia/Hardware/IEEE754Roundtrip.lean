/-
IEEE-754 round-trip headline.

For a finite, normal IEEE-754 floating-point value x, the round-trip
decode(encode(x)) equals x. Encode produces the canonical bit pattern;
decode interprets it back as a real value (or rather, the
representable rational).

DO NOT restructure files or change namespaces. The expected output
is a sorry-free Lean file declaring
`Pythia.Hardware.IEEE754.decode_encode_id` for normal floats.
-/
import Mathlib
import Pythia.Hardware.IEEE754

namespace Pythia.Hardware.IEEE754

/-! ## Helper lemmas for the bit-packing round-trip -/

/-
Unpacking the mantissa from a packed bit pattern recovers the original mantissa.
-/
lemma unpackMant_pack (s : FloatSpec) (sign : Bool) (exp mant : ℕ)
    (hm : mant < 2 ^ s.mw) :
    s.unpackMant (s.pack sign exp mant) = mant := by
  unfold FloatSpec.unpackMant FloatSpec.pack;
  norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_add ];
  exact Nat.mod_eq_of_lt hm

/-
Unpacking the exponent from a packed bit pattern recovers the original exponent.
-/
lemma unpackExp_pack (s : FloatSpec) (sign : Bool) (exp mant : ℕ)
    (he : exp < 2 ^ s.ew) (hm : mant < 2 ^ s.mw) :
    s.unpackExp (s.pack sign exp mant) = exp := by
  unfold FloatSpec.unpackExp FloatSpec.pack;
  norm_num [ Nat.add_div, Nat.mul_div_assoc, pow_add ];
  norm_num [ Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hm ];
  split_ifs <;> simp_all +decide [ Nat.div_eq_of_lt, Nat.mod_eq_of_lt ];
  linarith

/-
Unpacking the sign from a packed bit pattern recovers the original sign.
-/
lemma unpackSign_pack (s : FloatSpec) (sign : Bool) (exp mant : ℕ)
    (he : exp < 2 ^ s.ew) (hm : mant < 2 ^ s.mw) :
    s.unpackSign (s.pack sign exp mant) = sign := by
  unfold FloatSpec.unpackSign FloatSpec.pack;
  cases sign <;> simp +decide [ *, pow_add ];
  · nlinarith;
  · grind

/-- Round-trip identity for normal floats: every finite normal float
value encodes to a bit pattern that decodes back to the same value.
The statement is parameterized over the FloatSpec; concrete instances
include fp32, fp16, bf16. -/
theorem decode_encode_id
    (s : FloatSpec)
    (sign : Bool) (exp mant : ℕ)
    (he : exp < 2 ^ s.ew) (hm : mant < 2 ^ s.mw)
    (_h_normal_lo : 0 < exp)
    (_h_normal_hi : exp < 2 ^ s.ew - 1) :
    s.decode (s.encode sign exp mant) = s.toReal sign exp mant := by
  unfold FloatSpec.decode FloatSpec.encode
  rw [unpackMant_pack s sign exp mant hm,
      unpackExp_pack s sign exp mant he hm,
      unpackSign_pack s sign exp mant he hm]

end Pythia.Hardware.IEEE754