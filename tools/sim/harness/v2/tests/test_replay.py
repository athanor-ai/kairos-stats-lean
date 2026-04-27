"""Unit tests for tools.sim.harness.v2.replay.

Covers the replay shape contract: ``record_failure(sample)`` saves
the sample as-is, and ``replay_corpus(sim, fn)`` calls
``fn(sample)`` positionally. Earlier the pair did
``record_failure(inputs={...})`` paired with
``replay_corpus -> fn(**inputs)``, which only worked when the dict
key happened to match the user's parameter name. The new contract
is shape-agnostic (scalar, list, or dict samples all round-trip).
"""
from __future__ import annotations

import json

import pytest

from tools.sim.harness.v2 import replay as replay_mod
from tools.sim.harness.v2.replay import (
    load_corpus,
    record_failure,
    replay_corpus,
)


@pytest.fixture(autouse=True)
def isolated_ce_dir(tmp_path, monkeypatch):
    """Redirect counterexample writes to a temp directory."""
    monkeypatch.setattr(replay_mod, "_CE_DIR", tmp_path / "counterexamples")
    return tmp_path / "counterexamples"


class TestRecordFailure:
    def test_creates_file(self, isolated_ce_dir) -> None:
        path = record_failure("test_sim", seed=42, sample={"x": 1.0}, message="oops")
        assert path.exists()

    def test_file_is_valid_json(self, isolated_ce_dir) -> None:
        path = record_failure("test_sim", seed=0, sample={"y": 2.0}, message="bad")
        data = json.loads(path.read_text())
        assert data["sim_name"] == "test_sim"
        assert data["sample"]["y"] == 2.0
        assert data["message"] == "bad"

    def test_records_scalar_sample(self, isolated_ce_dir) -> None:
        path = record_failure("scalar_sim", seed=0, sample=3.14, message="")
        data = json.loads(path.read_text())
        assert data["sample"] == 3.14

    def test_records_list_sample(self, isolated_ce_dir) -> None:
        path = record_failure("list_sim", seed=0, sample=[1, 2, 3], message="")
        data = json.loads(path.read_text())
        assert data["sample"] == [1, 2, 3]

    def test_deterministic_hash(self, isolated_ce_dir) -> None:
        path1 = record_failure("sim", seed=1, sample={"a": 3}, message="m1")
        path2 = record_failure("sim", seed=2, sample={"a": 3}, message="m2")
        # Same sample -> same hash -> same file (last write wins)
        assert path1 == path2

    def test_different_samples_different_files(self, isolated_ce_dir) -> None:
        path1 = record_failure("sim", seed=0, sample={"a": 1}, message="")
        path2 = record_failure("sim", seed=0, sample={"a": 2}, message="")
        assert path1 != path2


class TestLoadCorpus:
    def test_empty_when_no_dir(self, isolated_ce_dir) -> None:
        entries = load_corpus("nonexistent_sim")
        assert entries == []

    def test_loads_written_entries(self, isolated_ce_dir) -> None:
        record_failure("my_sim", seed=0, sample={"z": 9.9}, message="fail")
        entries = load_corpus("my_sim")
        assert len(entries) == 1
        assert entries[0]["sample"]["z"] == 9.9

    def test_multiple_entries(self, isolated_ce_dir) -> None:
        record_failure("s", seed=0, sample={"a": 1}, message="")
        record_failure("s", seed=0, sample={"a": 2}, message="")
        entries = load_corpus("s")
        assert len(entries) == 2


class TestReplayCorpus:
    def test_passes_when_corpus_empty(self, isolated_ce_dir) -> None:
        replay_corpus("no_sim", lambda sample: True)  # should not raise

    def test_passes_when_property_now_holds(self, isolated_ce_dir) -> None:
        record_failure("sim2", seed=0, sample={"x": 5.0}, message="old")
        replay_corpus("sim2", lambda sample: True)  # fixed — should not raise

    def test_raises_when_still_failing(self, isolated_ce_dir) -> None:
        record_failure("sim3", seed=0, sample={"x": 5.0}, message="broken")
        with pytest.raises(AssertionError, match="still failing"):
            replay_corpus("sim3", lambda sample: False)

    def test_raises_on_exception(self, isolated_ce_dir) -> None:
        record_failure("sim4", seed=0, sample={"x": 5.0}, message="exc")

        def bad_fn(sample):
            raise RuntimeError("boom")

        with pytest.raises(AssertionError):
            replay_corpus("sim4", bad_fn)

    def test_replays_scalar_sample(self, isolated_ce_dir) -> None:
        """Regression: scalar samples (e.g. ``real_in(...)``-emitted
        floats) round-trip through record + replay. Earlier a scalar
        sample was wrapped under a fixed key, which broke any
        property whose parameter name differed."""
        record_failure("scalar_sim", seed=0, sample=42.0, message="num")
        # Property takes the scalar positionally; the param is named
        # ``s`` (deliberately not matching any saved-dict key).
        replay_corpus("scalar_sim", lambda s: s == 42.0)

    def test_replays_dict_sample_with_arbitrary_param_name(
        self, isolated_ce_dir
    ) -> None:
        """Regression: a dict sample is delivered to the property
        positionally, not via ``**``-unpacking. So a property that
        receives the whole dict under a different param name still
        works."""
        record_failure("dict_sim", seed=0, sample={"K": 1, "L": 2}, message="m")
        # Property takes the dict positionally as ``cfg``.
        replay_corpus("dict_sim", lambda cfg: cfg["K"] == 1 and cfg["L"] == 2)

    def test_replays_list_sample(self, isolated_ce_dir) -> None:
        record_failure("list_sim", seed=0, sample=[1, 2, 3], message="m")
        replay_corpus("list_sim", lambda xs: sum(xs) == 6)


class TestReplayCorpusFixture:
    def test_fixture_returns_callable(self, replay_corpus_fixture, isolated_ce_dir) -> None:
        # Should not raise when corpus is empty
        replay_corpus_fixture("empty_sim", lambda sample: True)
