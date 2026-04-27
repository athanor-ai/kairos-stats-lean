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

The :meth:`Sim.run` method composes:

* ``_run_property`` — exercises the predicate. Two modes:

  * **strict** (``statistical_assertion is None``): wraps in ``@given``;
    Hypothesis raises on the first failure, with shrinking. Best for
    deterministic identities where any violation is a bug.
  * **statistical** (``statistical_assertion`` set): draws
    ``replications`` independent samples via ``strategy.example()``,
    counts violations, asserts the upper bound of a Wilson CI on the
    violation rate is below ``claimed_prob``. Best for tail bounds /
    concentration inequalities where some violation rate is expected.

* ``_run_symmetries`` — runs each :class:`MetamorphicRelation` (each
  has its own internal ``@given`` with ``max_examples``).
* ``_run_differential`` — invokes ``lake env lean #eval ...`` once
  with ``DifferentialCheck.inputs``; skips with a warning if no lake.
* ``replay_corpus`` — replays every counterexample previously
  recorded for this sim's name; raises if any still fails.

If the generator was annotated by :func:`target_extreme` or
:func:`target_violation_proximity`, ``_run_property`` reads the
``_v2_edge_fn`` / ``_v2_bound_fn`` attribute and calls
``hypothesis.target()`` inside the ``@given`` body so coverage is
biased toward the declared boundary / tight-bound region.
"""
from __future__ import annotations

import warnings
from dataclasses import dataclass, field
from typing import Any, Callable, Optional

from hypothesis import HealthCheck, given, settings, target as _h_target
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
        differential:         Optional Lean<->Python DifferentialCheck.
        replications:         Hypothesis max_examples for the property.
        statistical_assertion: Dict {claimed_prob, ci_level} or None.
            When set, switches the property loop to statistical mode:
            draws ``replications`` independent samples, counts
            violations, asserts the upper Wilson CI bound on the
            violation rate is at or below ``claimed_prob``.
    """
    name: str
    lean_module: str
    generator: SearchStrategy
    property: Property
    symmetries: list[MetamorphicRelation] = field(default_factory=list)
    differential: Optional[DifferentialCheck] = None
    replications: int = 1000
    statistical_assertion: Optional[dict] = None

    def run(self) -> None:
        """Compose all primitives and run the sim end-to-end.

        Replay-corpus runs only in strict mode. In statistical mode
        the CI assertion is the report, and re-running a saved
        counterexample on a probabilistic property is conceptually
        incoherent (the same sample is *expected* to fail at the
        declared rate; replay would raise on every CI-passing sim).
        """
        self._run_property()
        self._run_symmetries()
        self._run_differential()
        if self.statistical_assertion is None:
            replay_corpus(self.name, self.property)

    def _run_property(self) -> None:
        if self.statistical_assertion is None:
            self._run_property_strict()
        else:
            self._run_property_statistical()

    def _run_property_strict(self) -> None:
        """First-failure-raises mode with Hypothesis shrinking.

        If the generator was annotated by :func:`target_extreme` /
        :func:`target_violation_proximity`, calls
        ``hypothesis.target()`` inside the ``@given`` body so coverage
        is biased toward the declared region.
        """
        prop = self.property
        sim_name = self.name
        edge_fn = getattr(self.generator, "_v2_edge_fn", None)
        bound_fn = getattr(self.generator, "_v2_bound_fn", None)

        @settings(
            max_examples=self.replications,
            suppress_health_check=[HealthCheck.too_slow, HealthCheck.large_base_example],
        )
        @given(sample=self.generator)
        def _inner(sample: Any) -> None:
            if edge_fn is not None:
                try:
                    _h_target(float(edge_fn(sample)))
                except (TypeError, ValueError) as exc:
                    warnings.warn(
                        f"target_extreme edge_fn raised on sample={_safe_repr(sample)}: {exc}",
                        stacklevel=2,
                    )
            if bound_fn is not None:
                try:
                    if isinstance(sample, dict):
                        slack = bound_fn(**sample)
                    else:
                        slack = bound_fn(sample)
                    _h_target(-float(slack))
                except (TypeError, ValueError) as exc:
                    warnings.warn(
                        f"target_violation_proximity bound_fn raised on sample={_safe_repr(sample)}: {exc}",
                        stacklevel=2,
                    )
            try:
                ok = bool(prop(sample))
            except Exception as exc:
                record_failure(sim_name, 0, sample, str(exc))
                raise AssertionError(
                    f"property raised on sample={_safe_repr(sample)}: {exc}"
                ) from exc
            if not ok:
                record_failure(sim_name, 0, sample, "property check failed")
                raise AssertionError(
                    f"property failed on sample={_safe_repr(sample)}"
                )

        _inner()

    def _run_property_statistical(self) -> None:
        """Statistical mode: count violations across N independent draws,
        assert upper Wilson CI bound on the violation rate <= claimed_prob.

        Used for tail-bound / concentration sims where some
        violation rate is expected by the theorem itself. We
        intentionally use ``strategy.example()`` here instead of
        ``@given``: ``@given`` shrinks on the first failure, which is
        the wrong abstraction for "estimate a violation rate".
        ``.example()`` emits a fresh random sample each call, which is
        what we want for unbiased Bernoulli replications. Hypothesis
        emits ``NonInteractiveExampleWarning`` on each call; we
        silence it deliberately because the use is correct here.
        """
        from hypothesis.errors import NonInteractiveExampleWarning

        prop = self.property
        n = self.replications
        violations = 0
        first_failure_recorded = False

        with warnings.catch_warnings():
            warnings.simplefilter("ignore", NonInteractiveExampleWarning)
            for i in range(n):
                sample = self.generator.example()
                try:
                    ok = bool(prop(sample))
                except Exception as exc:
                    violations += 1
                    if not first_failure_recorded:
                        record_failure(self.name, i, sample, f"property raised: {exc}")
                        first_failure_recorded = True
                    continue
                if not ok:
                    violations += 1
                    if not first_failure_recorded:
                        record_failure(self.name, i, sample, "property check failed")
                        first_failure_recorded = True

        claimed = float(self.statistical_assertion.get("claimed_prob", 0.05))
        level = float(self.statistical_assertion.get("ci_level", 0.99))
        passed = binomial_ci_check(violations, n, claimed, ci_level=level)
        if not passed:
            raise AssertionError(
                f"statistical_assertion failed: {violations}/{n} violations exceed "
                f"claimed_prob={claimed} at upper Wilson CI bound (level={level})"
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
    """Repr a sample for use in JSON / error messages.

    Returns scalars / lists / dicts unchanged so they can round-trip
    through :func:`record_failure` -> :func:`replay_corpus`.
    """
    if isinstance(sample, (int, float, bool, str)) or sample is None:
        return sample
    if isinstance(sample, (list, tuple)):
        return [_safe_repr(x) for x in sample]
    if isinstance(sample, dict):
        return {str(k): _safe_repr(v) for k, v in sample.items()}
    return str(sample)


__all__ = ["Sim"]
