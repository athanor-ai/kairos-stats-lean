"""v2 PoC: Hardy-Weinberg allele-frequency conservation sim (ATH-791).

Lean side: ``Pythia/Bio/Population.lean::hardy_weinberg_conservation``
proves:  p² + 2pq + q² = 1 for p + q = 1.

This is the v2 port of ``tools/sim/bio_hardy_weinberg.py``.
Do NOT modify the v1 file — this lives alongside it.
"""
from __future__ import annotations

import hypothesis.strategies as st

from tools.sim.harness.v2 import Sim
from tools.sim.harness.v2.generators import real_in
from tools.sim.harness.v2.metamorphic import limit_case, permutation_invariant
from tools.sim.harness.v2.properties import identity


# ── property ─────────────────────────────────────────────────────────────

def _hw_lhs(p: float) -> float:
    """p² + 2pq + q² where q = 1 - p."""
    q = 1.0 - p
    return p ** 2 + 2 * p * q + q ** 2


def _hw_rhs(p: float) -> float:
    """Constant 1.0 (Hardy-Weinberg conservation)."""
    return 1.0


def hardy_weinberg_property(sample: dict) -> bool:
    """Identity: p² + 2pq + q² == 1.0 within 1e-9 relative tolerance."""
    return identity(
        lhs_fn=lambda p: _hw_lhs(p),
        rhs_fn=lambda p: _hw_rhs(p),
        inputs=sample,
        tolerance=1e-9,
    )


# ── generator ────────────────────────────────────────────────────────────

_GENERATOR = st.fixed_dictionaries({"p": real_in(0.0, 1.0)})

# For the permutation_invariant check, we need both p and q as explicit keys.
_PQ_GENERATOR = st.fixed_dictionaries({
    "p": real_in(0.0, 1.0),
}).map(lambda d: {"p": d["p"], "q": 1.0 - d["p"]})

# ── symmetries ───────────────────────────────────────────────────────────

def _hw_full(p: float, q: float) -> float:
    """p² + 2pq + q² using explicit p, q (for permutation check)."""
    return p ** 2 + 2 * p * q + q ** 2


# Permutation invariance: swapping p and q (both drawn from the simplex
# p + q = 1) yields the same Hardy-Weinberg sum.
_perm_sym = permutation_invariant(
    fn=_hw_full,
    arg_names=["p", "q"],
    base_strategy=_PQ_GENERATOR,
    tolerance=1e-9,
    max_examples=200,
)

# At p=0.5 (the maximum heterozygosity point), the sum is still exactly 1.
_limit_p_sym = limit_case(
    fn=_hw_lhs,
    arg="p",
    limit_value=0.5,
    expected_form_fn=lambda p: 1.0,
    base_strategy=_GENERATOR,
    tolerance=1e-9,
    max_examples=200,
)

# ── Sim declaration ───────────────────────────────────────────────────────

hardy_weinberg_v2 = Sim(
    name="bio.hardy_weinberg.v2",
    lean_module="Pythia.Bio.Population",
    generator=_GENERATOR,
    property=hardy_weinberg_property,
    symmetries=[_perm_sym, _limit_p_sym],
    replications=1000,
)

__all__ = [
    "hardy_weinberg_v2",
    "hardy_weinberg_property",
    "_hw_lhs",
    "_hw_rhs",
    "_hw_full",
    "_GENERATOR",
    "_PQ_GENERATOR",
]
