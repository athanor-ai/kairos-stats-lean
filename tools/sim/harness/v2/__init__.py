"""tools.sim.harness.v2 — composable sim-runner v2.

A new sim is a ~20-line declaration::

    from tools.sim.harness.v2 import Sim
    from tools.sim.harness.v2.generators import real_in
    from tools.sim.harness.v2.properties import identity

    smoke = Sim(
        name="smoke.identity_add_zero",
        lean_module="Pythia.Smoke",
        generator=real_in(-1e6, 1e6),
        property=lambda x: identity(lambda x: x + 0, lambda x: x, {"x": x}),
        replications=500,
    )
    smoke.run()
"""
from __future__ import annotations

import warnings
from dataclasses import dataclass, field
from typing import Any, Callable, Optional

from hypothesis import HealthCheck, given, settings
from hypothesis.strategies import SearchStrategy

from tools.sim.harness.v2.differential import DifferentialCheck, lean_eval_matches_python
from tools.sim.harness.v2.metamorphic import MetamorphicRelation
from tools.sim.harness.v2.properties import Property
from tools.sim.harness.v2.replay import record_failure, replay_corpus
from tools.sim.harness.v2.statistical import binomial_ci_check


@dataclass
class Sim:
    """Composable sim declaration.

    Attributes:
        name:                 Unique id (used for counterexample paths).
        lean_module:          Lean module backing the theorem.
        generator:            Hypothesis SearchStrategy yielding one sample.
        property:             Callable(sample) -> bool.
        symmetries:           MetamorphicRelation list; each auto-checked.
        differential:         Optional Lean↔Python DifferentialCheck.
        boundary_targets:     Arg names to annotate for extreme targeting.
        replications:         Hypothesis max_examples for main property check.
        statistical_assertion: Dict {claimed_prob, ci_level} for CI gate.
    """
    name: str
    lean_module: str
    generator: SearchStrategy
    property: Property
    symmetries: list[MetamorphicRelation] = field(default_factory=list)
    differential: Optional[DifferentialCheck] = None
    boundary_targets: list[str] = field(default_factory=list)
    replications: int = 1000
    statistical_assertion: Optional[dict] = None

    def run(self) -> None:
        """Compose all primitives and run the sim end-to-end."""
        self._run_property()
        self._run_symmetries()
        self._run_differential()
        replay_corpus(self.name, self.property)

    def _run_property(self) -> None:
        prop = self.property
        failures: list[Any] = []

        @settings(
            max_examples=self.replications,
            suppress_health_check=[HealthCheck.too_slow, HealthCheck.large_base_example],
        )
        @given(sample=self.generator)
        def _inner(sample: Any) -> None:
            try:
                ok = bool(prop(sample))
            except Exception as exc:
                failures.append({"sample": _safe_repr(sample), "exc": str(exc)})
                record_failure(self.name, 0, {"sample": _safe_repr(sample)}, str(exc))
                raise AssertionError(f"property raised on sample={_safe_repr(sample)}: {exc}") from exc
            if not ok:
                failures.append({"sample": _safe_repr(sample)})
                record_failure(self.name, 0, {"sample": _safe_repr(sample)}, "property check failed")
                raise AssertionError(f"property failed on sample={_safe_repr(sample)}")

        _inner()

        if self.statistical_assertion and failures:
            claimed = self.statistical_assertion.get("claimed_prob", 0.05)
            level = self.statistical_assertion.get("ci_level", 0.99)
            assert binomial_ci_check(len(failures), self.replications, claimed, ci_level=level), (
                f"statistical_assertion failed: {len(failures)}/{self.replications} violations"
            )

    def _run_symmetries(self) -> None:
        for sym in self.symmetries:
            sym.run()

    def _run_differential(self) -> None:
        if self.differential is None:
            return
        d = self.differential
        ok = lean_eval_matches_python(d.lean_decl, d.python_fn, d.inputs, tolerance=d.tolerance)
        if not ok:
            msg = f"differential check failed: lean_decl={d.lean_decl!r}"
            record_failure(self.name, 0, d.inputs, msg)
            raise AssertionError(msg)


def _safe_repr(sample: Any) -> Any:
    if isinstance(sample, (int, float, bool, str)):
        return sample
    if isinstance(sample, (list, tuple)):
        return [_safe_repr(x) for x in sample]
    if isinstance(sample, dict):
        return {str(k): _safe_repr(v) for k, v in sample.items()}
    return str(sample)


__all__ = ["Sim"]
