"""PBT sim for Pythia.Hardware.ECC (Hamming distance / error correction).

Tests error detection/correction capacity by constructing small codes
and verifying the Hamming-distance guarantees with random error patterns.

Paired with: Pythia/Hardware/ECC.lean
  - hamming_triangle (sorry)
  - hamming_symm (sorry)
  - detection_capacity (sorry)
  - correction_capacity (sorry)
  - singleton_bound (sorry)
"""
from __future__ import annotations

from hypothesis import given, settings, assume
from hypothesis import strategies as st


def popcount(x: int) -> int:
    return bin(x).count("1")


def hamming_dist(x: int, y: int) -> int:
    return popcount(x ^ y)


@given(
    x=st.integers(min_value=0, max_value=2**16),
    y=st.integers(min_value=0, max_value=2**16),
    z=st.integers(min_value=0, max_value=2**16),
)
@settings(max_examples=500)
def test_hamming_triangle(x, y, z):
    """Hamming distance satisfies the triangle inequality."""
    assert hamming_dist(x, z) <= hamming_dist(x, y) + hamming_dist(y, z)


@given(
    x=st.integers(min_value=0, max_value=2**16),
    y=st.integers(min_value=0, max_value=2**16),
)
@settings(max_examples=500)
def test_hamming_symm(x, y):
    """Hamming distance is symmetric."""
    assert hamming_dist(x, y) == hamming_dist(y, x)


# --- Detection / correction with known codes ---

# Hamming(7,4) code: minimum distance 3 → detects 2, corrects 1
HAMMING_74 = [
    0b0000000,
    0b1101001,
    0b0101010,
    0b1000011,
    0b1001100,
    0b0100101,
    0b1100110,
    0b0001111,
    0b1110000,
    0b0011001,
    0b1011010,
    0b0110011,
    0b0111100,
    0b1010101,
    0b0010110,
    0b1111111,
]


def test_hamming_74_min_distance():
    """Verify Hamming(7,4) has minimum distance 3."""
    min_d = 999
    for i, c1 in enumerate(HAMMING_74):
        for j, c2 in enumerate(HAMMING_74):
            if i != j:
                d = hamming_dist(c1, c2)
                min_d = min(min_d, d)
    assert min_d == 3, f"Expected min distance 3, got {min_d}"


@given(
    cw_idx=st.integers(min_value=0, max_value=15),
    error_bit=st.integers(min_value=0, max_value=6),
)
@settings(max_examples=200)
def test_detection_1bit(cw_idx, error_bit):
    """Hamming(7,4) detects all 1-bit errors (d=3 → detects ≤2)."""
    cw = HAMMING_74[cw_idx]
    corrupted = cw ^ (1 << error_bit)
    assert corrupted not in HAMMING_74, (
        f"1-bit error at bit {error_bit} of codeword {cw:#09b} = {corrupted:#09b} "
        f"is still a valid codeword — detection failed"
    )


@given(
    cw_idx=st.integers(min_value=0, max_value=15),
    error_bit=st.integers(min_value=0, max_value=6),
)
@settings(max_examples=200)
def test_correction_1bit(cw_idx, error_bit):
    """Hamming(7,4) corrects all 1-bit errors (d=3 → corrects ≤1).
    Nearest-codeword decoding uniquely recovers the original."""
    cw = HAMMING_74[cw_idx]
    corrupted = cw ^ (1 << error_bit)

    # Find nearest codeword
    best_cw = min(HAMMING_74, key=lambda c: hamming_dist(corrupted, c))
    assert best_cw == cw, (
        f"1-bit error at bit {error_bit}: corrupted={corrupted:#09b}, "
        f"decoded to {best_cw:#09b} instead of {cw:#09b}"
    )


def test_singleton_bound_hamming_74():
    """Hamming(7,4) with d=3: |C| ≤ 2^(7-3+1) = 32. We have 16 ≤ 32."""
    n, d = 7, 3
    assert len(HAMMING_74) <= 2 ** (n - d + 1)


if __name__ == "__main__":
    test_hamming_triangle()
    print("✓ hamming_triangle")
    test_hamming_symm()
    print("✓ hamming_symm")
    test_hamming_74_min_distance()
    print("✓ hamming_74_min_distance")
    test_detection_1bit()
    print("✓ detection_1bit")
    test_correction_1bit()
    print("✓ correction_1bit")
    test_singleton_bound_hamming_74()
    print("✓ singleton_bound")
    print("\nAll hardware_ecc PBT passed.")
