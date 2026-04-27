"""Unit tests for tools.sim.harness.v2.replay."""
from __future__ import annotations

import json
import tempfile
from pathlib import Path

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
        path = record_failure("test_sim", seed=42, inputs={"x": 1.0}, message="oops")
        assert path.exists()

    def test_file_is_valid_json(self, isolated_ce_dir) -> None:
        path = record_failure("test_sim", seed=0, inputs={"y": 2.0}, message="bad")
        data = json.loads(path.read_text())
        assert data["sim_name"] == "test_sim"
        assert data["inputs"]["y"] == 2.0
        assert data["message"] == "bad"

    def test_deterministic_hash(self, isolated_ce_dir) -> None:
        path1 = record_failure("sim", seed=1, inputs={"a": 3}, message="m1")
        path2 = record_failure("sim", seed=2, inputs={"a": 3}, message="m2")
        # Same inputs → same hash → same file (last write wins)
        assert path1 == path2

    def test_different_inputs_different_files(self, isolated_ce_dir) -> None:
        path1 = record_failure("sim", seed=0, inputs={"a": 1}, message="")
        path2 = record_failure("sim", seed=0, inputs={"a": 2}, message="")
        assert path1 != path2


class TestLoadCorpus:
    def test_empty_when_no_dir(self, isolated_ce_dir) -> None:
        entries = load_corpus("nonexistent_sim")
        assert entries == []

    def test_loads_written_entries(self, isolated_ce_dir) -> None:
        record_failure("my_sim", seed=0, inputs={"z": 9.9}, message="fail")
        entries = load_corpus("my_sim")
        assert len(entries) == 1
        assert entries[0]["inputs"]["z"] == 9.9

    def test_multiple_entries(self, isolated_ce_dir) -> None:
        record_failure("s", seed=0, inputs={"a": 1}, message="")
        record_failure("s", seed=0, inputs={"a": 2}, message="")
        entries = load_corpus("s")
        assert len(entries) == 2


class TestReplayCorpus:
    def test_passes_when_corpus_empty(self, isolated_ce_dir) -> None:
        replay_corpus("no_sim", lambda x: True)  # should not raise

    def test_passes_when_property_now_holds(self, isolated_ce_dir) -> None:
        record_failure("sim2", seed=0, inputs={"x": 5.0}, message="old")
        replay_corpus("sim2", lambda x: True)  # fixed — should not raise

    def test_raises_when_still_failing(self, isolated_ce_dir) -> None:
        record_failure("sim3", seed=0, inputs={"x": 5.0}, message="broken")
        with pytest.raises(AssertionError, match="still failing"):
            replay_corpus("sim3", lambda x: False)

    def test_raises_on_exception(self, isolated_ce_dir) -> None:
        record_failure("sim4", seed=0, inputs={"x": 5.0}, message="exc")

        def bad_fn(x):
            raise RuntimeError("boom")

        with pytest.raises(AssertionError):
            replay_corpus("sim4", bad_fn)


class TestReplayCorpusFixture:
    def test_fixture_returns_callable(self, replay_corpus_fixture, isolated_ce_dir) -> None:
        # Should not raise when corpus is empty
        replay_corpus_fixture("empty_sim", lambda x: True)
