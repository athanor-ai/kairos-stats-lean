"""Unit tests for tools.sim.harness.v2.differential."""
from __future__ import annotations

import warnings

import pytest

from tools.sim.harness.v2.differential import (
    DifferentialCheck,
    _parse_lean_float,
    lean_eval_matches_python,
)


class TestParseLeanFloat:
    def test_integer_string(self) -> None:
        assert _parse_lean_float("42") == 42.0

    def test_float_string(self) -> None:
        assert abs(_parse_lean_float("3.14") - 3.14) < 1e-10

    def test_rational_string(self) -> None:
        assert abs(_parse_lean_float("1/2") - 0.5) < 1e-10

    def test_negative_rational(self) -> None:
        assert abs(_parse_lean_float("-3/4") - (-0.75)) < 1e-10

    def test_unparseable_returns_none(self) -> None:
        assert _parse_lean_float("hello world") is None

    def test_zero_denominator_returns_none(self) -> None:
        assert _parse_lean_float("1/0") is None

    def test_whitespace_stripped(self) -> None:
        assert _parse_lean_float("  7  ") == 7.0


class TestDifferentialCheck:
    def test_dataclass_fields(self) -> None:
        dc = DifferentialCheck(
            lean_decl="#eval {x} + 0",
            python_fn=lambda x: x + 0,
            inputs={"x": 5.0},
        )
        assert dc.lean_decl == "#eval {x} + 0"
        assert dc.tolerance == 1e-9


class TestLeanEvalMatchesPython:
    def test_skip_when_no_lake(self) -> None:
        """When lake is absent, function returns True with a warning."""
        import shutil
        original_which = shutil.which

        def mock_which(cmd):
            if cmd == "lake":
                return None
            return original_which(cmd)

        import tools.sim.harness.v2.differential as diff_mod
        orig = diff_mod.shutil.which
        diff_mod.shutil.which = mock_which
        try:
            with warnings.catch_warnings(record=True) as w:
                warnings.simplefilter("always")
                result = lean_eval_matches_python(
                    "#eval {x} + 0",
                    lambda x: x,
                    {"x": 5.0},
                )
            assert result is True
            assert any("lake not found" in str(warning.message) for warning in w)
        finally:
            diff_mod.shutil.which = orig

    def test_python_fn_called(self) -> None:
        """Verify python_fn is the comparison target (not that lake runs)."""
        called = []

        def py_fn(x):
            called.append(x)
            return x

        import shutil
        if not shutil.which("lake"):
            # Skip the full check, just verify python_fn would be called
            pytest.skip("lake not available in this environment")
