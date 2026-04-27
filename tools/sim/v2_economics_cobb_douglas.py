"""v2 PoC: Cobb-Douglas constant-returns-to-scale sim (ATH-791).

Lean side: ``Pythia/Economics/CobbDouglas.lean::cobb_douglas_crts``
proves:  (λK)^α · (λL)^(1-α) = λ · K^α · L^(1-α)

This is the v2 port of ``tools/sim/economics_cobb_douglas.py``.
Do NOT modify the v1 file — this lives alongside it.
"""
from __future__ import annotations

import hypothesis.strategies as st

from tools.sim.harness.v2 import Sim
from tools.sim.harness.v2.generators import positive_real, real_in
from tools.sim.harness.v2.metamorphic import homogeneous, limit_case
from tools.sim.harness.v2.properties import identity


# ── property ─────────────────────────────────────────────────────────────

def _cobb_douglas_lhs(K: float, L: float, lam: float, alpha: float) -> float:
    """(λK)^α · (λL)^(1-α)"""
    return (lam * K) ** alpha * (lam * L) ** (1 - alpha)


def _cobb_douglas_rhs(K: float, L: float, lam: float, alpha: float) -> float:
    """λ · K^α · L^(1-α)"""
    return lam * (K ** alpha * L ** (1 - alpha))


def cobb_douglas_property(sample: dict) -> bool:
    """Identity: LHS == RHS within 1e-9 relative tolerance."""
    return identity(
        lhs_fn=_cobb_douglas_lhs,
        rhs_fn=_cobb_douglas_rhs,
        inputs=sample,
        tolerance=1e-9,
    )


# ── generator ────────────────────────────────────────────────────────────

_GENERATOR = st.fixed_dictionaries({
    "K": positive_real(),
    "L": positive_real(),
    "lam": positive_real(),
    "alpha": real_in(0.05, 0.95),
})

# ── symmetries ───────────────────────────────────────────────────────────

# Constant returns to scale: doubling K and L together doubles output.
# f(c·K, c·L, lam, alpha) = c^1 · f(K, L, lam, alpha)
_homogeneous_sym = homogeneous(
    fn=_cobb_douglas_rhs,
    arg_names=["K", "L"],
    factor_strategy=positive_real(),
    exponent=1,
    base_strategy=_GENERATOR,
    tolerance=1e-7,
    max_examples=200,
)

# At λ=1, both sides collapse to K^α · L^(1-α).
_limit_lam_sym = limit_case(
    fn=_cobb_douglas_lhs,
    arg="lam",
    limit_value=1.0,
    expected_form_fn=lambda K, L, lam, alpha: (K ** alpha) * (L ** (1 - alpha)),
    base_strategy=_GENERATOR,
    tolerance=1e-6,
    max_examples=200,
)

# ── Sim declaration ───────────────────────────────────────────────────────

cobb_douglas_v2 = Sim(
    name="economics.cobb_douglas_crts.v2",
    lean_module="Pythia.Economics.CobbDouglas",
    generator=_GENERATOR,
    property=cobb_douglas_property,
    symmetries=[_homogeneous_sym, _limit_lam_sym],
    replications=1000,
)

__all__ = [
    "cobb_douglas_v2",
    "cobb_douglas_property",
    "_cobb_douglas_lhs",
    "_cobb_douglas_rhs",
    "_GENERATOR",
]
