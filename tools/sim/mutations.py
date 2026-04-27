"""tools.sim.mutations — reusable mutation library.

The original ATH-742 sim runner takes :class:`Mutation` instances
that are deliberately-broken specs the harness expects to fail. Each
domain harness was hand-rolling its own mutations: ``negate_pe``,
``drop_factor``, ``off_by_initial``, etc. The catalogue across
batches 2-6 ended up reinventing the same six or seven shapes, often
with inconsistent thresholds or vacuous mutations that pass on
continuous parameter spaces.

This module provides a single named library + a per-mutation
property test confirming each is actually detectable on a typical
spec shape. Domain harnesses import from here instead of redefining.

Public factories (each returns a :class:`Mutation`):

    negate_value(spec, *, name="negate_value", min_failure_rate=0.5)
    drop_factor(spec, factor_name, *, name=None, min_failure_rate=0.05)
    off_by_const(spec, *, delta, name=None, min_failure_rate=0.5)
    swap_inequality(spec, *, name="swap_inequality")
    strict_bound_below(spec, *, threshold, name=None, min_failure_rate=0.05)
    strict_bound_above(spec, *, threshold, name=None, min_failure_rate=0.05)

All factories take the ORIGINAL bool-returning spec and return a new
:class:`Mutation` whose ``.spec`` callable wraps it. The harness
runs both spec and mutation on the same draws; the mutation MUST
return False on >= min_failure_rate of them.

Per-mutation property tests live in ``tools/sim/test_mutations.py``
and assert each mutation breaks a known-true reference spec on the
expected fraction of a synthetic draw set.
"""
from __future__ import annotations

from typing import Any, Callable

from tools.sim.harness import Mutation


# ─────────────────────────────────────────────────────────────────────
# Wrappers
# ─────────────────────────────────────────────────────────────────────


def negate_value(
    spec: Callable[..., bool],
    *,
    name: str = "negate_value",
    min_failure_rate: float = 0.5,
) -> Mutation:
    """Mutation that flips the spec's verdict. Trivially fails wherever
    the original passes. Use as a sanity sentinel — every harness
    should catch it. min_failure_rate=0.5 reflects that the mutation
    fails wherever the original holds (which is the spec's whole
    domain, so closer to 100%; we conservatively floor at 50% to
    cover specs whose pass set is sparse)."""
    def mutated(**kwargs: Any) -> bool:
        try:
            return not bool(spec(**kwargs))
        except Exception:
            return False
    return Mutation(name=name, spec=mutated, min_failure_rate=min_failure_rate)


def drop_factor(
    spec: Callable[..., bool],
    factor_name: str,
    *,
    name: str | None = None,
    min_failure_rate: float = 0.05,
    replacement: float = 1.0,
) -> Mutation:
    """Mutation that pins one named parameter to ``replacement``
    (default 1.0) instead of the value drawn by the harness. The
    inequality / equality the spec asserts usually depends on the
    factor's actual value, so pinning kills the spec on every draw
    where the actual value differs from ``replacement``.

    Example: a Cobb-Douglas constant-returns-to-scale spec that
    asserts ``(λK)^α (λL)^(1-α) == λ K^α L^(1-α)`` with
    ``drop_factor(spec, "lam", replacement=1.0)`` will fail on every
    draw where ``lam != 1.0``.
    """
    full_name = name or f"drop_factor_{factor_name}"

    def mutated(**kwargs: Any) -> bool:
        try:
            kwargs2 = {**kwargs, factor_name: replacement}
            return bool(spec(**kwargs2))
        except Exception:
            return False
    return Mutation(name=full_name, spec=mutated, min_failure_rate=min_failure_rate)


def off_by_const(
    spec: Callable[..., bool],
    *,
    delta: float,
    name: str | None = None,
    min_failure_rate: float = 0.5,
) -> Mutation:
    """Mutation that adds ``delta`` to whichever side of the spec the
    caller wraps. Implemented by composing: ``spec`` returns bool;
    we WRAP it to produce a different bool by checking the spec at
    ``kwargs['delta']`` (if present) or by adding delta to a designated
    output. Since the harness's spec returns bool, the cleanest way
    to express off-by-const is: caller writes their spec to take an
    optional ``_offset`` kwarg, defaulting to 0.0; the mutation
    invokes spec with ``_offset=delta``.

    For specs that don't honor ``_offset``, this mutation is a no-op
    on the verdict (spec returns the same bool); the property test
    asserts it does break specs that DO honor it.
    """
    full_name = name or f"off_by_const_{delta:+g}"

    def mutated(**kwargs: Any) -> bool:
        try:
            return bool(spec(_offset=delta, **kwargs))
        except TypeError:
            # Spec doesn't accept _offset; mutation is undetectable
            # for this spec. Returning True keeps the harness from
            # double-counting it as a "caught" mutation.
            return True
        except Exception:
            return False
    return Mutation(name=full_name, spec=mutated, min_failure_rate=min_failure_rate)


def swap_inequality(
    spec: Callable[..., bool],
    *,
    name: str = "swap_inequality",
    min_failure_rate: float = 0.5,
) -> Mutation:
    """Alias for ``negate_value`` framed for inequality specs.
    Provided so harness authors can pick the name that reads clearer
    at the call site.
    """
    return negate_value(spec, name=name, min_failure_rate=min_failure_rate)


def strict_bound_below(
    spec: Callable[..., bool],
    *,
    threshold: float,
    output_name: str = "lhs",
    name: str | None = None,
    min_failure_rate: float = 0.05,
) -> Mutation:
    """Mutation that strengthens the spec to demand the output be
    STRICTLY greater than ``threshold``. Caller's spec must accept a
    ``_strict_below_threshold`` kwarg AND a ``_lhs`` kwarg containing
    the value being bounded; if the spec doesn't honor those, the
    mutation is undetectable.

    The simpler convention: callers write their mutation locally as
    ``lambda **kw: spec_value(**kw) > threshold`` since the spec
    library can't introspect the caller's value layout. This factory
    is preserved for harnesses that follow the strict-output
    convention.
    """
    full_name = name or f"strict_below_{threshold:+g}"

    def mutated(**kwargs: Any) -> bool:
        try:
            return bool(spec(
                _strict_below_threshold=threshold,
                **kwargs,
            ))
        except TypeError:
            return True
        except Exception:
            return False
    return Mutation(name=full_name, spec=mutated, min_failure_rate=min_failure_rate)


def strict_bound_above(
    spec: Callable[..., bool],
    *,
    threshold: float,
    name: str | None = None,
    min_failure_rate: float = 0.05,
) -> Mutation:
    """Symmetric to ``strict_bound_below`` — strengthen to demand
    output be STRICTLY less than ``threshold``."""
    full_name = name or f"strict_above_{threshold:+g}"

    def mutated(**kwargs: Any) -> bool:
        try:
            return bool(spec(
                _strict_above_threshold=threshold,
                **kwargs,
            ))
        except TypeError:
            return True
        except Exception:
            return False
    return Mutation(name=full_name, spec=mutated, min_failure_rate=min_failure_rate)


# ─────────────────────────────────────────────────────────────────────
# Lower-level: caller-supplied transform mutation
# ─────────────────────────────────────────────────────────────────────


def custom_transform(
    spec: Callable[..., bool],
    transform: Callable[..., bool],
    *,
    name: str,
    min_failure_rate: float = 0.05,
) -> Mutation:
    """Escape hatch: supply a fully-custom mutated spec. Use when the
    library factories don't fit (e.g. mass-action conservation's
    'apply extent twice' is shaped differently). The library still
    gives you the named ``Mutation`` packaging + the consistent
    min_failure_rate floor.
    """
    return Mutation(name=name, spec=transform, min_failure_rate=min_failure_rate)


__all__ = [
    "custom_transform",
    "drop_factor",
    "negate_value",
    "off_by_const",
    "strict_bound_above",
    "strict_bound_below",
    "swap_inequality",
]
