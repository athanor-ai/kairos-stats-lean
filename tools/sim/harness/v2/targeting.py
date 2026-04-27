"""tools.sim.harness.v2.targeting — Hypothesis targeting helpers."""
from __future__ import annotations

from typing import Any, Callable
from hypothesis.strategies import SearchStrategy


def target_extreme(
    strategy: SearchStrategy,
    edge_fn: Callable[[Any], float],
) -> SearchStrategy:
    """Annotate strategy so Sim.run() calls hypothesis.target(edge_fn(value)).

    Higher edge_fn values = more extreme / closer to boundary.
    """
    strategy._v2_edge_fn = edge_fn  # type: ignore[attr-defined]
    return strategy


def target_violation_proximity(
    bound_fn: Callable[..., float],
    base_strategy: SearchStrategy[dict[str, Any]],
) -> SearchStrategy[dict[str, Any]]:
    """Annotate strategy so Sim.run() calls hypothesis.target(-bound_fn(**inputs)).

    bound_fn(**kwargs) returns the slack between actual and claimed bound;
    smaller slack = tighter = more interesting.
    """
    base_strategy._v2_bound_fn = bound_fn  # type: ignore[attr-defined]
    return base_strategy


__all__ = ["target_extreme", "target_violation_proximity"]
