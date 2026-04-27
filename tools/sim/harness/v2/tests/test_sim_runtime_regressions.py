"""Regressions for three bugs found in the v2 harness audit (2026-04-27).

These tests would have caught the original defects:

1. ``Sim.boundary_targets`` was declared on the dataclass but never
   read by ``Sim.run()``. The smoke test set the field and "passed",
   but no targeting was actually exercised. Fixed by deleting the
   field and reading ``_v2_edge_fn`` / ``_v2_bound_fn`` annotations
   off the strategy directly.

2. ``Sim._run_property`` raised ``AssertionError`` per-failure inside
   the Hypothesis ``@given`` body and only checked
   ``statistical_assertion`` *afterward* against an outer-scope
   ``failures`` list — making the CI assertion unreachable. Fixed by
   splitting into ``_run_property_strict`` (raises) and
   ``_run_property_statistical`` (counts and asserts).

3. ``record_failure`` saved ``{"sample": ...}`` while ``replay_corpus``
   called ``property_fn(**inputs)`` — round-trip only worked when the
   user's parameter name happened to be ``sample``. Fixed by saving
   the sample directly (any shape) and replaying with positional
   ``property_fn(sample)``.

Each test below exercises the path that was previously dead.
"""
from __future__ import annotations

import json

import hypothesis.strategies as st
import pytest

from tools.sim.harness.v2 import Sim
from tools.sim.harness.v2 import replay as replay_mod
from tools.sim.harness.v2.generators import real_in
from tools.sim.harness.v2.targeting import target_extreme


@pytest.fixture(autouse=True)
def isolated_ce_dir(tmp_path, monkeypatch):
    """Redirect counterexample writes to a temp directory."""
    monkeypatch.setattr(replay_mod, "_CE_DIR", tmp_path / "counterexamples")
    return tmp_path / "counterexamples"


# ─── Bug 1: boundary targeting actually runs ─────────────────────────


def test_target_extreme_edge_fn_is_invoked_during_run() -> None:
    """If a generator was wrapped with ``target_extreme(edge_fn=...)``,
    the edge_fn should be CALLED during ``Sim.run()`` — not just
    annotated and ignored. We verify by counting invocations of a
    spy edge_fn while ``Sim.run()`` executes.
    """
    invocations: list[float] = []

    def spy_edge_fn(x: float) -> float:
        invocations.append(x)
        return abs(x)

    gen = target_extreme(real_in(-10.0, 10.0), edge_fn=spy_edge_fn)

    sim = Sim(
        name="regression.target_extreme_invoked",
        lean_module="N/A",
        generator=gen,
        property=lambda x: True,  # never fails
        replications=20,
    )
    sim.run()

    # ``replications=20`` produces at least 20 ``@given`` body executions,
    # one per draw. ``edge_fn`` should be called on every one.
    assert len(invocations) >= 20, (
        f"target_extreme.edge_fn was called {len(invocations)} time(s); "
        f"expected at least 20 (one per replication). Bug 1: boundary "
        "targeting wired but not executed."
    )


def test_target_violation_proximity_bound_fn_is_invoked_during_run() -> None:
    """Same shape as Bug 1 but for the ``target_violation_proximity``
    annotation."""
    from tools.sim.harness.v2.targeting import target_violation_proximity

    invocations: list[dict] = []

    def spy_bound_fn(**inputs: float) -> float:
        invocations.append(inputs)
        return inputs["x"] - 1.0  # slack = x - 1

    base = st.fixed_dictionaries({"x": real_in(-5.0, 5.0)})
    gen = target_violation_proximity(spy_bound_fn, base_strategy=base)

    sim = Sim(
        name="regression.target_violation_proximity_invoked",
        lean_module="N/A",
        generator=gen,
        property=lambda sample: True,
        replications=20,
    )
    sim.run()

    assert len(invocations) >= 20, (
        f"target_violation_proximity.bound_fn was called "
        f"{len(invocations)} time(s); expected at least 20."
    )


# ─── Bug 2: statistical_assertion fires when violations exceed claim ──


def test_statistical_assertion_fails_when_violation_rate_exceeds_claim() -> None:
    """A property that always fails should trip the statistical
    assertion: violation rate ~= 1.0 vs claimed_prob=0.05 fails the
    Wilson CI upper bound.

    Previously this check was unreachable because ``_run_property``
    raised on the first per-sample failure inside ``@given``. With
    the rewrite, statistical mode aggregates without raising
    per-sample.
    """
    sim = Sim(
        name="regression.stat_high_violation_rate",
        lean_module="N/A",
        generator=real_in(0.0, 1.0),
        property=lambda x: False,  # 100% violation rate
        replications=100,
        statistical_assertion={"claimed_prob": 0.05, "ci_level": 0.99},
    )
    with pytest.raises(AssertionError, match="statistical_assertion failed"):
        sim.run()


def test_statistical_assertion_passes_when_violation_rate_under_claim() -> None:
    """A property that never fails passes the statistical assertion.

    Sample-size calculus: Wilson upper CI for 0/500 at 99% level is
    ~0.013, which is below claimed_prob=0.05. A smaller N would not
    pass even with zero observed violations because the CI alone
    exceeds the claim — this is correct conservative behaviour and
    is exercised by the *fails* test below.
    """
    sim = Sim(
        name="regression.stat_zero_violation_rate",
        lean_module="N/A",
        generator=real_in(0.0, 1.0),
        property=lambda x: True,
        replications=500,
        statistical_assertion={"claimed_prob": 0.05, "ci_level": 0.99},
    )
    sim.run()  # no raise


def test_statistical_assertion_fails_with_too_few_samples() -> None:
    """Conservative-CI behaviour: 0 violations in only 100 samples
    does NOT prove violation rate <= 0.05 at 99% confidence.

    Wilson upper CI for 0/100 at 99% level is ~0.062, above
    claimed_prob=0.05. The assertion correctly fails — proving the
    binomial CI gate is actually computing a CI, not just passing
    when violations==0.
    """
    sim = Sim(
        name="regression.stat_undersized",
        lean_module="N/A",
        generator=real_in(0.0, 1.0),
        property=lambda x: True,  # zero violations in expectation
        replications=100,
        statistical_assertion={"claimed_prob": 0.05, "ci_level": 0.99},
    )
    with pytest.raises(AssertionError, match="statistical_assertion failed"):
        sim.run()


def test_statistical_assertion_distinguishes_borderline_rates() -> None:
    """A property that fails ~3% of the time passes claimed_prob=0.10
    but fails claimed_prob=0.001 at the same N. Demonstrates the CI
    assertion is actually doing the binomial test, not trivially
    passing or failing.

    Sample-size calculus (N=500, ~3% empirical rate):
    Wilson upper CI for 15/500 at 99% level is ~0.057.
    * 0.057 <= 0.10 → lax claim passes
    * 0.057  > 0.001 → strict claim fails
    """

    # Deterministic 3% violation rate: fail on indices 0, 1, 2 out of
    # every 100. The property's input is unused; we drive a counter.
    state = {"i": 0}

    def gen_index_property(_unused: float) -> bool:
        i = state["i"]
        state["i"] += 1
        return (i % 100) >= 3

    # Lax claim: 10% — CI upper ~5.7% < 10%, passes.
    state["i"] = 0
    sim_lax = Sim(
        name="regression.stat_borderline_lax",
        lean_module="N/A",
        generator=real_in(0.0, 1.0),
        property=gen_index_property,
        replications=500,
        statistical_assertion={"claimed_prob": 0.10, "ci_level": 0.99},
    )
    sim_lax.run()  # no raise

    # Strict claim: 0.1% — CI upper ~5.7% > 0.1%, fails.
    state["i"] = 0
    sim_strict = Sim(
        name="regression.stat_borderline_strict",
        lean_module="N/A",
        generator=real_in(0.0, 1.0),
        property=gen_index_property,
        replications=500,
        statistical_assertion={"claimed_prob": 0.001, "ci_level": 0.99},
    )
    with pytest.raises(AssertionError, match="statistical_assertion failed"):
        sim_strict.run()


# ─── Bug 3: replay shape round-trips for non-matching param names ─────


def test_record_then_replay_with_mismatched_param_name() -> None:
    """A failure recorded via the strict path should be replayable
    even when the property's parameter name differs from any saved
    dict key.

    Previously ``record_failure(inputs={"sample": ...})`` paired with
    ``replay_corpus -> fn(**inputs)`` would call ``fn(sample=...)``,
    which TypeErrors for any property with a different param name.

    Note: Hypothesis's shrinking phase records many distinct
    counterexamples per failing run (one per shrink attempt that
    finds a new failing input). We assert at-least-one and verify
    the SHAPE of the first one is a scalar — the original bug was
    a shape mismatch, not a count mismatch.
    """
    # Step 1: run a strict-mode Sim that always fails — this records
    # at least one counterexample under ``regression.replay_mismatch``.
    sim_record = Sim(
        name="regression.replay_mismatch",
        lean_module="N/A",
        generator=real_in(7.0, 7.0001),
        property=lambda x: False,
        replications=1,
    )
    with pytest.raises(AssertionError):
        sim_record.run()

    # Step 2: read the recorded entries and confirm shape: the saved
    # JSON ``sample`` field is a scalar float, NOT wrapped under a
    # sentinel key. Hypothesis may record multiple shrink attempts;
    # any one of them must show the correct shape.
    entries = replay_mod.load_corpus("regression.replay_mismatch")
    assert len(entries) >= 1, "no counterexamples recorded — record_failure path skipped"
    for entry in entries:
        sample = entry.get("sample")
        # Negative assertion: the OLD buggy shape stored
        # ``inputs={"sample": ...}`` which would deserialise into a
        # dict with key 'sample'. Detect that explicitly and reject.
        assert not (isinstance(sample, dict) and set(sample.keys()) == {"sample"}), (
            f"recorded entry uses old buggy shape (dict-wrapped under 'sample' key): {entry}"
        )
        # Positive assertion: scalar float for a real_in generator.
        assert isinstance(sample, (int, float)), (
            f"recorded sample wrong type: got {type(sample).__name__}, expected scalar; "
            f"entry={entry}"
        )

    # Step 3: replay with a property whose param name is
    # ``param_with_some_other_name`` (deliberately not 'sample').
    # In the buggy version this would TypeError because the old
    # ``replay_corpus`` did ``property_fn(**inputs)``. Now it's
    # positional, so any param name works.
    replay_mod.replay_corpus(
        "regression.replay_mismatch",
        lambda param_with_some_other_name: True,  # replay should not raise
    )

    # Step 4: replay with a property that genuinely fails (returns
    # False) should still raise, proving the replay actually invokes
    # the property — not just iterates over the corpus.
    with pytest.raises(AssertionError, match="still failing"):
        replay_mod.replay_corpus(
            "regression.replay_mismatch",
            lambda anything: False,
        )
