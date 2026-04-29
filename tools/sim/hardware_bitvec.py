"""PBT sim for Pythia.Hardware.BitVec.

Cross-checks the bit-vector modular arithmetic lemmas against Python's
native integer operations. Every theorem in BitVec.lean has a paired
Hypothesis test here that fuzzes random inputs and verifies the
identity holds.

Paired with: Pythia/Hardware/BitVec.lean
  - add_mod_eq, mul_mod_eq (proved)
  - unsigned_add_overflow_iff (sorry)
  - arith_shift_right_eq_div (proved)
  - gray_adjacent_hamming_one (sorry)
  - fifo_empty_iff, fifo_full_iff (sorry)
"""
from __future__ import annotations

from hypothesis import given, settings, assume
from hypothesis import strategies as st


@given(
    n=st.integers(min_value=1, max_value=64),
    a=st.integers(min_value=0, max_value=2**64),
    b=st.integers(min_value=0, max_value=2**64),
)
@settings(max_examples=1000)
def test_add_mod_eq(n: int, a: int, b: int):
    """(a + b) % 2^n == ((a % 2^n) + (b % 2^n)) % 2^n"""
    mod = 2 ** n
    assert (a + b) % mod == ((a % mod) + (b % mod)) % mod


@given(
    n=st.integers(min_value=1, max_value=32),
    a=st.integers(min_value=0, max_value=2**32),
    b=st.integers(min_value=0, max_value=2**32),
)
@settings(max_examples=1000)
def test_mul_mod_eq(n: int, a: int, b: int):
    """(a * b) % 2^n == ((a % 2^n) * (b % 2^n)) % 2^n"""
    mod = 2 ** n
    assert (a * b) % mod == ((a % mod) * (b % mod)) % mod


@given(
    n=st.integers(min_value=1, max_value=32),
    a=st.integers(min_value=0, max_value=2**32 - 1),
    b=st.integers(min_value=0, max_value=2**32 - 1),
)
@settings(max_examples=500)
def test_unsigned_overflow_iff(n: int, a: int, b: int):
    """Unsigned overflow: a + b ≥ 2^n iff (a + b) % 2^n < a."""
    assume(a < 2**n and b < 2**n)
    mod = 2 ** n
    overflows = (a + b) >= mod
    wrapped_less = ((a + b) % mod) < a
    assert overflows == wrapped_less, (
        f"n={n}, a={a}, b={b}: overflow={overflows}, wrapped<a={wrapped_less}"
    )


@given(
    m=st.integers(min_value=0, max_value=30),
    v=st.integers(min_value=0, max_value=2**31),
)
@settings(max_examples=500)
def test_arith_shift_right(m: int, v: int):
    """v // 2^m == v >> m for non-negative v."""
    assert v // (2 ** m) == v >> m


def _to_gray(v: int) -> int:
    return v ^ (v >> 1)


def _popcount(x: int) -> int:
    return bin(x).count("1")


@given(
    v=st.integers(min_value=0, max_value=2**16 - 2),
)
@settings(max_examples=1000)
def test_gray_adjacent_hamming_one(v: int):
    """Adjacent Gray code values differ in exactly one bit."""
    g1 = _to_gray(v)
    g2 = _to_gray(v + 1)
    diff = g1 ^ g2
    assert _popcount(diff) == 1, (
        f"v={v}: gray({v})={g1:#b}, gray({v+1})={g2:#b}, "
        f"diff={diff:#b}, popcount={_popcount(diff)}"
    )


@given(
    n=st.integers(min_value=1, max_value=16),
    rd=st.integers(min_value=0, max_value=2**16),
    wr=st.integers(min_value=0, max_value=2**16),
)
@settings(max_examples=500)
def test_fifo_empty_iff(n: int, rd: int, wr: int):
    """FIFO empty: rd % 2^n == wr % 2^n iff (wr - rd) % 2^n == 0."""
    mod = 2 ** n
    lhs = (rd % mod) == (wr % mod)
    rhs = ((wr - rd) % mod) == 0
    assert lhs == rhs, f"n={n}, rd={rd}, wr={wr}"


@given(
    n=st.integers(min_value=2, max_value=16),
    rd=st.integers(min_value=0, max_value=2**16),
    wr=st.integers(min_value=0, max_value=2**16),
)
@settings(max_examples=500)
def test_fifo_full_iff(n: int, rd: int, wr: int):
    """FIFO full: (wr + 1) % 2^n == rd % 2^n iff (wr - rd) % 2^n == 2^n - 1."""
    mod = 2 ** n
    lhs = ((wr + 1) % mod) == (rd % mod)
    rhs = ((wr - rd) % mod) == (mod - 1)
    assert lhs == rhs, f"n={n}, rd={rd}, wr={wr}"


if __name__ == "__main__":
    test_add_mod_eq()
    print("✓ add_mod_eq")
    test_mul_mod_eq()
    print("✓ mul_mod_eq")
    test_unsigned_overflow_iff()
    print("✓ unsigned_overflow_iff")
    test_arith_shift_right()
    print("✓ arith_shift_right")
    test_gray_adjacent_hamming_one()
    print("✓ gray_adjacent_hamming_one")
    test_fifo_empty_iff()
    print("✓ fifo_empty_iff")
    test_fifo_full_iff()
    print("✓ fifo_full_iff")
    print("\nAll hardware_bitvec PBT passed.")
