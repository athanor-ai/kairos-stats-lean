"""Pythia simulation harness — PBT + sweep + mutation testing.

The Lean side proves the theorem. This module empirically verifies
it: random parameter draws check the bound holds, a deterministic
sweep covers realistic ranges, and mutation tests confirm the
property isn't passing vacuously by perturbing the spec and
expecting failure.

Zero external dependencies. Uses only Python stdlib (random, math,
itertools, dataclasses, typing). A customer who installs pythia and
runs `python -m tools.sim.economics_cobb_douglas` gets working
empirical verification with no extra `pip install`.

Public API:

    Strategy(K=floats(0.01, 1e6), L=floats(0.01, 1e6), ...)
    run_harness(name, spec, strategy, mutations=[...]) -> HarnessResult

`spec` is a Python callable taking keyword args (matching `strategy`
keys) and returning a bool: True when the theorem holds at those
parameters, False otherwise. The harness draws random kwargs from
the strategy, calls `spec`, asserts True. A mutation is a separate
callable; the harness asserts it is False on at least
`mutation_min_failure_rate` of draws (default 5 %), confirming the
mutation is detectable.

Float-tolerance helpers:

    isclose(a, b, rtol=1e-9) — same shape as math.isclose
    le(a, b, atol=0.0)        — a <= b + atol (inequality slack)

Use these inside spec callables for robust comparisons against
numerical noise.
"""
from __future__ import annotations

import json
import math
import random
import time
from dataclasses import dataclass, field
from typing import Any, Callable, Optional


# ─────────────────────────────────────────────────────────────────────
# Strategies — random parameter generators
# ─────────────────────────────────────────────────────────────────────


class _Generator:
    """Base for parameter generators. Subclasses implement `draw`."""

    def draw(self, rng: random.Random) -> Any:
        raise NotImplementedError


@dataclass(frozen=True)
class Floats(_Generator):
    """Uniform draws in `[lo, hi]`. Use `log_scale=True` for orders-of-
    magnitude params (rates, concentrations, prices)."""
    lo: float
    hi: float
    log_scale: bool = False

    def draw(self, rng: random.Random) -> float:
        if self.log_scale:
            if self.lo <= 0 or self.hi <= 0:
                raise ValueError(
                    "log_scale=True requires strictly-positive bounds"
                )
            log_lo, log_hi = math.log(self.lo), math.log(self.hi)
            return math.exp(rng.uniform(log_lo, log_hi))
        return rng.uniform(self.lo, self.hi)


@dataclass(frozen=True)
class Ints(_Generator):
    """Inclusive integer range."""
    lo: int
    hi: int

    def draw(self, rng: random.Random) -> int:
        return rng.randint(self.lo, self.hi)


@dataclass(frozen=True)
class Choice(_Generator):
    """Pick one value from `options`."""
    options: tuple

    def draw(self, rng: random.Random) -> Any:
        return rng.choice(self.options)


# Convenience factories so test files read like Hypothesis specs.
def floats(lo: float, hi: float, *, log_scale: bool = False) -> Floats:
    return Floats(lo=lo, hi=hi, log_scale=log_scale)


def ints(lo: int, hi: int) -> Ints:
    return Ints(lo=lo, hi=hi)


def choice(*options: Any) -> Choice:
    return Choice(options=tuple(options))


@dataclass(frozen=True)
class Strategy:
    """A bag of named generators. Each call to `Strategy.draw(rng)`
    returns a fresh kwargs dict."""
    generators: dict[str, _Generator] = field(default_factory=dict)

    def __init__(self, **kwargs: _Generator) -> None:
        # `dataclass(frozen=True)` blocks normal __init__ assignment;
        # use object.__setattr__ to bypass.
        object.__setattr__(self, "generators", dict(kwargs))

    def draw(self, rng: random.Random) -> dict[str, Any]:
        return {k: g.draw(rng) for k, g in self.generators.items()}

    def keys(self) -> tuple[str, ...]:
        return tuple(self.generators.keys())


# ─────────────────────────────────────────────────────────────────────
# Mutation
# ─────────────────────────────────────────────────────────────────────


@dataclass(frozen=True)
class Mutation:
    """A deliberately-wrong spec the harness expects to fail.

    `name` shows up in the report; `spec` has the same signature as
    the original spec under test. The harness re-draws `n_pbt` random
    parameter sets, evaluates the mutated spec, and asserts it fails
    on at least `min_failure_rate` of them. If the mutation passes
    universally, the original tests are vacuous and we'd never know.
    """
    name: str
    spec: Callable[..., bool]
    min_failure_rate: float = 0.05  # 5 % default; raise for stricter tests


# ─────────────────────────────────────────────────────────────────────
# Result + run_harness
# ─────────────────────────────────────────────────────────────────────


@dataclass
class HarnessResult:
    """Aggregate outcome of one harness run.

    Fields:
        name              : identifier for the theorem (passed by caller)
        pbt_passed        : did all `n_pbt` random draws satisfy `spec`?
        sweep_passed      : did all sweep grid points satisfy `spec`?
        sweep_total       : grid size
        mutations_caught  : list of mutation names that failed at the
                            required rate (good — these are detectable)
        mutations_missed  : list of mutation names that did NOT fail
                            often enough (BAD — original tests vacuous)
        first_pbt_failure : kwargs dict of the first PBT draw that
                            violated the spec, or None if all passed
        first_sweep_failure : same shape, for the deterministic sweep
        wall_seconds      : wall-clock runtime
        n_pbt             : how many random draws were run
    """
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
        """True iff PBT, sweep, AND every mutation was caught."""
        return (
            self.pbt_passed
            and self.sweep_passed
            and not self.mutations_missed
        )

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
        """Human-readable one-block summary for terminal output."""
        tag = "✓" if self.all_passed else "✗"
        lines = [f"{tag} {self.name} (wall={self.wall_seconds:.2f}s, n_pbt={self.n_pbt})"]
        lines.append(
            f"  PBT     : {'pass' if self.pbt_passed else 'FAIL'}"
            + (f" — first failure: {self.first_pbt_failure}"
               if self.first_pbt_failure else "")
        )
        lines.append(
            f"  Sweep   : {'pass' if self.sweep_passed else 'FAIL'} ({self.sweep_total} points)"
            + (f" — first failure: {self.first_sweep_failure}"
               if self.first_sweep_failure else "")
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
    """Run the full empirical battery on one theorem.

    Args:
        name        : human-readable theorem identifier
        spec        : callable(**kwargs) -> bool. Returns True when the
                      theorem holds at those parameter values.
        strategy    : a `Strategy(...)` of named parameter generators.
                      Keys must match the kwargs `spec` accepts.
        n_pbt       : how many random PBT draws to run. Default 10 000.
        sweep_points: per-axis grid resolution. Total sweep size is
                      ≤ sweep_points^|axes|; clamped at 10 000 to bound
                      runtime.
        mutations   : tuple of Mutation. Each is re-evaluated on the
                      same n_pbt draws and the harness expects it to
                      FAIL at the rate the Mutation declared.
        seed        : RNG seed for reproducibility.

    Returns:
        HarnessResult.

    Raises nothing — failures are surfaced through the result, not
    exceptions, so a CI script can collect multiple harness outputs
    before deciding to fail.
    """
    rng = random.Random(seed)
    t0 = time.time()

    # ─── PBT ───────────────────────────────────────────────────────
    pbt_passed = True
    first_pbt_failure: Optional[dict] = None
    pbt_draws: list[dict] = []  # kept for re-use by mutation testing
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

    # ─── Sweep ─────────────────────────────────────────────────────
    sweep_passed, first_sweep_failure, sweep_total = _run_sweep(
        spec, strategy, sweep_points,
    )

    # ─── Mutations ─────────────────────────────────────────────────
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
    """Deterministic grid sweep over each axis. Total size capped at
    10_000 to bound runtime; we shrink `sweep_points` if it would
    exceed.

    Float axes get linspace; log-scale floats get geomspace; ints
    get evenly-spaced values; choices iterate all options.
    """
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

    # Cap the total grid size.
    total = 1
    for vals in axes.values():
        total *= max(1, len(vals))
    while total > 10_000:
        # Reduce the largest axis by one point.
        biggest = max(axes, key=lambda k: len(axes[k]))
        axes[biggest] = axes[biggest][::2]  # halve
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
        # Advance odometer.
        for i in range(len(keys) - 1, -1, -1):
            cur[i] += 1
            if cur[i] < len(axes[keys[i]]):
                break
            cur[i] = 0
        else:
            break
    return sweep_passed, first_sweep_failure, sweep_total


# ─────────────────────────────────────────────────────────────────────
# Helpers
# ─────────────────────────────────────────────────────────────────────


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
    """math.isclose with our default tolerances. Use inside spec callables."""
    return math.isclose(a, b, rel_tol=rtol, abs_tol=atol)


def le(a: float, b: float, *, atol: float = 0.0) -> bool:
    """Inequality with absolute slack — `a <= b + atol`."""
    return a <= b + atol
