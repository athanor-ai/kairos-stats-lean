"""tools.sim.harness — v1 harness compatibility shim + v2 subpackage.

Python resolves ``tools.sim.harness`` to this package (directory)
rather than ``harness.py`` once the directory exists.  All v1 public
symbols are re-implemented here verbatim so that existing imports such
as ``from tools.sim.harness import run_harness`` continue to work.

The original ``tools/sim/harness.py`` file is left untouched; it is
simply shadowed by this package on the import path.

v2 lives at ``tools.sim.harness.v2``.
"""
from __future__ import annotations

# ── v1 harness content (verbatim copy of tools/sim/harness.py) ───────
# We reproduce it here rather than exec/importlib because dataclasses
# need a stable __module__ reference that importlib shims break.

import json
import math
import random
import time
from dataclasses import dataclass, field
from typing import Any, Callable, Optional


# ─── Strategies ───────────────────────────────────────────────────────


class _Generator:
    def draw(self, rng: random.Random) -> Any:
        raise NotImplementedError


@dataclass(frozen=True)
class Floats(_Generator):
    lo: float
    hi: float
    log_scale: bool = False

    def draw(self, rng: random.Random) -> float:
        if self.log_scale:
            if self.lo <= 0 or self.hi <= 0:
                raise ValueError("log_scale=True requires strictly-positive bounds")
            log_lo, log_hi = math.log(self.lo), math.log(self.hi)
            return math.exp(rng.uniform(log_lo, log_hi))
        return rng.uniform(self.lo, self.hi)


@dataclass(frozen=True)
class Ints(_Generator):
    lo: int
    hi: int

    def draw(self, rng: random.Random) -> int:
        return rng.randint(self.lo, self.hi)


@dataclass(frozen=True)
class Choice(_Generator):
    options: tuple

    def draw(self, rng: random.Random) -> Any:
        return rng.choice(self.options)


def floats(lo: float, hi: float, *, log_scale: bool = False) -> Floats:
    return Floats(lo=lo, hi=hi, log_scale=log_scale)


def ints(lo: int, hi: int) -> Ints:
    return Ints(lo=lo, hi=hi)


def choice(*options: Any) -> Choice:
    return Choice(options=tuple(options))


@dataclass(frozen=True)
class Strategy:
    generators: dict[str, _Generator] = field(default_factory=dict)

    def __init__(self, **kwargs: _Generator) -> None:
        object.__setattr__(self, "generators", dict(kwargs))

    def draw(self, rng: random.Random) -> dict[str, Any]:
        return {k: g.draw(rng) for k, g in self.generators.items()}

    def keys(self) -> tuple[str, ...]:
        return tuple(self.generators.keys())


# ─── Mutation ─────────────────────────────────────────────────────────


@dataclass(frozen=True)
class Mutation:
    name: str
    spec: Callable[..., bool]
    min_failure_rate: float = 0.05


# ─── HarnessResult + run_harness ──────────────────────────────────────


@dataclass
class HarnessResult:
    name: str
    pbt_passed: bool
    sweep_passed: bool
    sweep_total: int
    mutations_caught: list[str] = field(default_factory=list)
    mutations_missed: list[str] = field(default_factory=list)
    first_pbt_failure: Optional[dict] = None
    first_sweep_failure: Optional[dict] = None
    wall_seconds: float = 0.0
    n_pbt: int = 0

    @property
    def all_passed(self) -> bool:
        return self.pbt_passed and self.sweep_passed and not self.mutations_missed

    def to_json(self) -> str:
        return json.dumps({
            "name": self.name,
            "pbt_passed": self.pbt_passed,
            "sweep_passed": self.sweep_passed,
            "sweep_total": self.sweep_total,
            "mutations_caught": self.mutations_caught,
            "mutations_missed": self.mutations_missed,
            "first_pbt_failure": self.first_pbt_failure,
            "first_sweep_failure": self.first_sweep_failure,
            "wall_seconds": self.wall_seconds,
            "n_pbt": self.n_pbt,
            "all_passed": self.all_passed,
        }, indent=2, default=str)

    def summarize(self) -> str:
        tag = "✓" if self.all_passed else "✗"
        lines = [f"{tag} {self.name} (wall={self.wall_seconds:.2f}s, n_pbt={self.n_pbt})"]
        lines.append(
            f"  PBT     : {'pass' if self.pbt_passed else 'FAIL'}"
            + (f" — first failure: {self.first_pbt_failure}" if self.first_pbt_failure else "")
        )
        lines.append(
            f"  Sweep   : {'pass' if self.sweep_passed else 'FAIL'} ({self.sweep_total} points)"
            + (f" — first failure: {self.first_sweep_failure}" if self.first_sweep_failure else "")
        )
        if self.mutations_caught or self.mutations_missed:
            lines.append(
                f"  Mutants : {len(self.mutations_caught)} caught, "
                f"{len(self.mutations_missed)} missed"
            )
            for m in self.mutations_missed:
                lines.append(f"    ✗ MISSED: {m} (vacuous-test risk)")
        return "\n".join(lines)


def run_harness(
    name: str,
    spec: Callable[..., bool],
    strategy: Strategy,
    *,
    n_pbt: int = 10_000,
    sweep_points: int = 5,
    mutations: tuple[Mutation, ...] = (),
    seed: int = 42,
) -> HarnessResult:
    rng = random.Random(seed)
    t0 = time.time()

    pbt_passed = True
    first_pbt_failure: Optional[dict] = None
    pbt_draws: list[dict] = []
    for _ in range(n_pbt):
        kwargs = strategy.draw(rng)
        pbt_draws.append(kwargs)
        try:
            ok = bool(spec(**kwargs))
        except Exception as e:
            ok = False
            kwargs = {**kwargs, "_exception": f"{type(e).__name__}: {e!s:.150}"}
        if not ok and first_pbt_failure is None:
            pbt_passed = False
            first_pbt_failure = kwargs

    sweep_passed, first_sweep_failure, sweep_total = _run_sweep(spec, strategy, sweep_points)

    caught: list[str] = []
    missed: list[str] = []
    for m in mutations:
        n_failures = 0
        for kwargs in pbt_draws:
            try:
                ok = bool(m.spec(**kwargs))
            except Exception:
                ok = False
            if not ok:
                n_failures += 1
        rate = n_failures / max(1, len(pbt_draws))
        if rate >= m.min_failure_rate:
            caught.append(m.name)
        else:
            missed.append(m.name)

    return HarnessResult(
        name=name,
        pbt_passed=pbt_passed,
        sweep_passed=sweep_passed,
        sweep_total=sweep_total,
        mutations_caught=caught,
        mutations_missed=missed,
        first_pbt_failure=first_pbt_failure,
        first_sweep_failure=first_sweep_failure,
        wall_seconds=time.time() - t0,
        n_pbt=n_pbt,
    )


def _run_sweep(
    spec: Callable[..., bool],
    strategy: Strategy,
    sweep_points: int,
) -> tuple[bool, Optional[dict], int]:
    axes: dict[str, list[Any]] = {}
    for k, gen in strategy.generators.items():
        if isinstance(gen, Floats):
            if gen.log_scale:
                axes[k] = _geomspace(gen.lo, gen.hi, sweep_points)
            else:
                axes[k] = _linspace(gen.lo, gen.hi, sweep_points)
        elif isinstance(gen, Ints):
            n = min(sweep_points, gen.hi - gen.lo + 1)
            axes[k] = _int_grid(gen.lo, gen.hi, n)
        elif isinstance(gen, Choice):
            axes[k] = list(gen.options)
        else:
            raise TypeError(f"sweep: unknown generator {type(gen).__name__}")

    total = 1
    for vals in axes.values():
        total *= max(1, len(vals))
    while total > 10_000:
        biggest = max(axes, key=lambda k: len(axes[k]))
        axes[biggest] = axes[biggest][::2]
        total = 1
        for vals in axes.values():
            total *= max(1, len(vals))

    keys = list(axes.keys())
    cur = [0] * len(keys)
    sweep_total = 0
    sweep_passed = True
    first_sweep_failure: Optional[dict] = None
    while True:
        kwargs = {k: axes[k][cur[i]] for i, k in enumerate(keys)}
        sweep_total += 1
        try:
            ok = bool(spec(**kwargs))
        except Exception as e:
            ok = False
            kwargs = {**kwargs, "_exception": f"{type(e).__name__}: {e!s:.150}"}
        if not ok and first_sweep_failure is None:
            sweep_passed = False
            first_sweep_failure = kwargs
        for i in range(len(keys) - 1, -1, -1):
            cur[i] += 1
            if cur[i] < len(axes[keys[i]]):
                break
            cur[i] = 0
        else:
            break
    return sweep_passed, first_sweep_failure, sweep_total


def _linspace(lo: float, hi: float, n: int) -> list[float]:
    if n <= 1:
        return [lo]
    step = (hi - lo) / (n - 1)
    return [lo + i * step for i in range(n)]


def _geomspace(lo: float, hi: float, n: int) -> list[float]:
    if n <= 1:
        return [lo]
    log_lo, log_hi = math.log(lo), math.log(hi)
    step = (log_hi - log_lo) / (n - 1)
    return [math.exp(log_lo + i * step) for i in range(n)]


def _int_grid(lo: int, hi: int, n: int) -> list[int]:
    if n <= 1:
        return [lo]
    if n >= hi - lo + 1:
        return list(range(lo, hi + 1))
    step = (hi - lo) / (n - 1)
    return [int(round(lo + i * step)) for i in range(n)]


def isclose(a: float, b: float, *, rtol: float = 1e-9, atol: float = 0.0) -> bool:
    return math.isclose(a, b, rel_tol=rtol, abs_tol=atol)


def le(a: float, b: float, *, atol: float = 0.0) -> bool:
    return a <= b + atol


__all__ = [
    "Choice",
    "Floats",
    "HarnessResult",
    "Ints",
    "Mutation",
    "Strategy",
    "choice",
    "floats",
    "ints",
    "isclose",
    "le",
    "run_harness",
]
