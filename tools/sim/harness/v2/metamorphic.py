"""tools.sim.harness.v2.metamorphic — symmetry declarations."""
from __future__ import annotations

import itertools
import math
from dataclasses import dataclass
from typing import Any, Callable, Sequence

from hypothesis import given, settings
from hypothesis import strategies as st
from hypothesis.strategies import SearchStrategy


@dataclass
class MetamorphicRelation:
    """Named symmetry check. Call run() to execute."""
    name: str
    check: Callable[[], None]

    def run(self) -> None:
        self.check()


def homogeneous(
    fn: Callable[..., float],
    arg_names: Sequence[str],
    factor_strategy: SearchStrategy[float],
    exponent: float,
    base_strategy: SearchStrategy[dict[str, Any]],
    *,
    tolerance: float = 1e-7,
    max_examples: int = 200,
) -> MetamorphicRelation:
    """f(c·x) = c^k · f(x)."""
    @settings(max_examples=max_examples)
    @given(inputs=base_strategy, c=factor_strategy)
    def _check(inputs: dict[str, Any], c: float) -> None:
        scaled = {k: (c * v if k in arg_names else v) for k, v in inputs.items()}
        lhs, rhs = fn(**scaled), (c ** exponent) * fn(**inputs)
        assert math.isclose(lhs, rhs, rel_tol=tolerance, abs_tol=tolerance), (
            f"homogeneous violated: f(c·x)={lhs}, c^k·f(x)={rhs}, c={c}"
        )
    return MetamorphicRelation(name=f"homogeneous(k={exponent})", check=_check)


def permutation_invariant(
    fn: Callable[..., float],
    arg_names: Sequence[str],
    base_strategy: SearchStrategy[dict[str, Any]],
    *,
    max_examples: int = 200,
    tolerance: float = 1e-9,
) -> MetamorphicRelation:
    """Permuting iid args doesn't change the result."""
    @settings(max_examples=max_examples)
    @given(inputs=base_strategy)
    def _check(inputs: dict[str, Any]) -> None:
        ref = fn(**inputs)
        vals = [inputs[k] for k in arg_names]
        for perm in itertools.islice(itertools.permutations(vals), 120):
            result = fn(**{**inputs, **dict(zip(arg_names, perm))})
            assert math.isclose(result, ref, rel_tol=tolerance, abs_tol=tolerance), (
                f"permutation_invariant violated: {ref} != {result}"
            )
    return MetamorphicRelation(name="permutation_invariant", check=_check)


def time_reversal_invariant(
    fn: Callable[[list[float]], float],
    path_strategy: SearchStrategy[list[float]],
    *,
    max_examples: int = 200,
    tolerance: float = 1e-9,
) -> MetamorphicRelation:
    """f(path) == f(reversed(path))."""
    @settings(max_examples=max_examples)
    @given(path=path_strategy)
    def _check(path: list[float]) -> None:
        fwd, rev = fn(path), fn(list(reversed(path)))
        assert math.isclose(fwd, rev, rel_tol=tolerance, abs_tol=tolerance), (
            f"time_reversal_invariant violated: {fwd} != {rev}"
        )
    return MetamorphicRelation(name="time_reversal_invariant", check=_check)


def bilinear(
    fn: Callable[..., float],
    arg1: str,
    arg2: str,
    base_strategy: SearchStrategy[dict[str, Any]],
    scalar_strategy: SearchStrategy[float],
    *,
    max_examples: int = 200,
    tolerance: float = 1e-7,
) -> MetamorphicRelation:
    """f(c·x, y) = c·f(x,y) and f(x, c·y) = c·f(x,y)."""
    @settings(max_examples=max_examples)
    @given(inputs=base_strategy, c=scalar_strategy)
    def _check(inputs: dict[str, Any], c: float) -> None:
        base = fn(**inputs)
        for arm, k in [(arg1, arg1), (arg2, arg2)]:
            r = fn(**{**inputs, k: c * inputs[k]})
            assert math.isclose(r, c * base, rel_tol=tolerance, abs_tol=tolerance), (
                f"bilinear ({arm} arm) violated: {r} != {c * base}"
            )
    return MetamorphicRelation(name=f"bilinear({arg1},{arg2})", check=_check)


def subadditive(
    fn: Callable[..., float],
    arg_names: Sequence[str],
    base_strategy: SearchStrategy[dict[str, Any]],
    *,
    max_examples: int = 200,
    atol: float = 1e-9,
) -> MetamorphicRelation:
    """f(x+y) <= f(x) + f(y)."""
    @settings(max_examples=max_examples)
    @given(a=base_strategy, b=base_strategy)
    def _check(a: dict[str, Any], b: dict[str, Any]) -> None:
        combined = {k: (a[k] + b[k] if k in arg_names else a[k]) for k in a}
        assert fn(**combined) <= fn(**a) + fn(**b) + atol, (
            f"subadditive violated"
        )
    return MetamorphicRelation(name="subadditive", check=_check)


def limit_case(
    fn: Callable[..., float],
    arg: str,
    limit_value: float,
    expected_form_fn: Callable[..., float],
    base_strategy: SearchStrategy[dict[str, Any]],
    *,
    max_examples: int = 200,
    tolerance: float = 1e-6,
) -> MetamorphicRelation:
    """At arg=limit_value, fn behaves like expected_form_fn."""
    @settings(max_examples=max_examples)
    @given(inputs=base_strategy)
    def _check(inputs: dict[str, Any]) -> None:
        at = {**inputs, arg: limit_value}
        result, expected = fn(**at), expected_form_fn(**at)
        assert math.isclose(result, expected, rel_tol=tolerance, abs_tol=tolerance), (
            f"limit_case at {arg}={limit_value}: fn={result}, expected={expected}"
        )
    return MetamorphicRelation(name=f"limit_case({arg}={limit_value})", check=_check)


__all__ = [
    "MetamorphicRelation", "bilinear", "homogeneous", "limit_case",
    "permutation_invariant", "subadditive", "time_reversal_invariant",
]
