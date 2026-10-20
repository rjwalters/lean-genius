"""Unit tests for ``anvil/skills/paper/lib/artifact_verify.py`` (issue #663).

The paper-review external-artifact verification gate: run the companion
code/proof artifact a paper's claims rest on, not just the rendered PDF.
Motivating canary incident (tractatus, 2026-07-13): a review ACCEPTed a
paper whose Lean 4 proof repo did not ``lake build`` and whose headline
theorem was false.

These tests cover the acceptance criteria directly:

- absent declaration → no-op (fail-open, byte-identical to pre-#663),
- successful commands → no critical flag,
- a failing command (non-zero exit) → CriticalFlag + Verdict.BLOCK
  through the UNMODIFIED ``anvil/lib/critics.py`` aggregator/schema,
- a timeout → CriticalFlag + BLOCK,
- an unresolvable cwd / command → fail-open (major finding, NOT a silent
  pass, NOT a blocker),
- the ``_artifact_verify.json`` sidecar payload shape,
- multi-command run-all (an earlier failure does not skip later commands).

Distinct filename per the #58 packaging convention; ``__init__.py`` chain
in this tests/ directory. The subprocess commands use ``sys.executable``
so the suite is self-contained (no lake/git dependency).
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

_REPO_ROOT = Path(__file__).resolve().parents[4]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from anvil.lib.critics import aggregate, compute_verdict  # noqa: E402
from anvil.lib.review_schema import Kind, Review, Verdict  # noqa: E402
from anvil.skills.paper.lib.artifact_verify import (  # noqa: E402
    DEFAULT_TIMEOUT_S,
    GATE_NAME,
    OUTCOME_FAIL,
    OUTCOME_PASS,
    OUTCOME_TIMEOUT,
    OUTCOME_UNRESOLVABLE,
    ArtifactVerifyConfig,
    discover_artifact_verify,
    verify,
)


# -----------------------------------------------------------------------------
# Helpers
# -----------------------------------------------------------------------------


def _write_anvil_json(thread_dir: Path, config: dict) -> None:
    (thread_dir / ".anvil.json").write_text(json.dumps(config), encoding="utf-8")


def _py(code: str) -> str:
    """A shell-safe command string that runs Python inline via sys.executable."""
    # shlex.split handles the quoting; embed the code with single quotes.
    return f"{sys.executable} -c {json.dumps(code)}"


# -----------------------------------------------------------------------------
# Discovery: absent declaration → fail-open no-op
# -----------------------------------------------------------------------------


def test_absent_anvil_json_is_not_declared(tmp_path):
    """No .anvil.json at all → declared=False (byte-identical to today)."""
    cfg = discover_artifact_verify(tmp_path)
    assert cfg.declared is False
    assert cfg.commands == []
    assert cfg.config_warning is None


def test_anvil_json_without_artifact_verify_is_not_declared(tmp_path):
    """A .anvil.json carrying only venue/max_iterations → not declared."""
    _write_anvil_json(tmp_path, {"venue": "neurips", "max_iterations": 4})
    cfg = discover_artifact_verify(tmp_path)
    assert cfg.declared is False
    assert cfg.config_warning is None


def test_malformed_json_degrades_to_not_declared(tmp_path):
    """Unparseable .anvil.json → not declared (never raises)."""
    (tmp_path / ".anvil.json").write_text("{ not json ", encoding="utf-8")
    cfg = discover_artifact_verify(tmp_path)
    assert cfg.declared is False


def test_empty_commands_list_is_not_declared_but_warns(tmp_path):
    """Declared block with no runnable commands fails open WITH a warning
    (distinguishable from never-declared)."""
    _write_anvil_json(tmp_path, {"artifact_verify": {"commands": []}})
    cfg = discover_artifact_verify(tmp_path)
    assert cfg.declared is False
    assert cfg.config_warning is not None


def test_declared_block_parses_fields(tmp_path):
    """A well-formed block parses commands / cwd / timeout_s."""
    _write_anvil_json(
        tmp_path,
        {
            "artifact_verify": {
                "commands": ["lake build", "lake exe check"],
                "cwd": "proof/",
                "timeout_s": 120,
            }
        },
    )
    cfg = discover_artifact_verify(tmp_path)
    assert cfg.declared is True
    assert cfg.commands == ["lake build", "lake exe check"]
    assert cfg.cwd == "proof/"
    assert cfg.timeout_s == 120


def test_malformed_timeout_falls_back_to_default(tmp_path):
    """A non-positive / non-numeric timeout_s silently uses the default."""
    _write_anvil_json(
        tmp_path,
        {"artifact_verify": {"commands": ["true"], "timeout_s": -5}},
    )
    cfg = discover_artifact_verify(tmp_path)
    assert cfg.declared is True
    assert cfg.timeout_s == DEFAULT_TIMEOUT_S
    assert cfg.config_warning is not None


def test_boolean_timeout_is_rejected(tmp_path):
    """A JSON ``true`` for timeout_s must not become a 1-second budget."""
    _write_anvil_json(
        tmp_path,
        {"artifact_verify": {"commands": ["true"], "timeout_s": True}},
    )
    cfg = discover_artifact_verify(tmp_path)
    assert cfg.timeout_s == DEFAULT_TIMEOUT_S


# -----------------------------------------------------------------------------
# verify(): not-declared config is a safe no-op
# -----------------------------------------------------------------------------


def test_verify_not_declared_is_noop(tmp_path):
    """Calling verify() on a not-declared config never runs a subprocess."""
    cfg = ArtifactVerifyConfig(declared=False)
    res = verify(cfg, thread_dir=tmp_path)
    assert res.ran is False
    assert res.commands == []
    assert res.to_critical_flags() == []


# -----------------------------------------------------------------------------
# verify(): success path → no flag
# -----------------------------------------------------------------------------


def test_successful_commands_no_flag(tmp_path):
    """Every command exits 0 → passed, no critical flag, ran=True."""
    _write_anvil_json(
        tmp_path,
        {"artifact_verify": {"commands": [_py("import sys; sys.exit(0)")]}},
    )
    cfg = discover_artifact_verify(tmp_path)
    res = verify(cfg, thread_dir=tmp_path)
    assert res.ran is True
    assert res.passed is True
    assert res.to_critical_flags() == []
    assert all(c.outcome == OUTCOME_PASS for c in res.commands)


# -----------------------------------------------------------------------------
# verify(): failing command → CriticalFlag → Verdict.BLOCK (no schema change)
# -----------------------------------------------------------------------------


def test_failing_command_emits_flag_and_blocks(tmp_path):
    """A non-zero exit emits an artifact_verify_* CriticalFlag that routes
    through the UNMODIFIED aggregator + compute_verdict to Verdict.BLOCK."""
    _write_anvil_json(
        tmp_path,
        {"artifact_verify": {"commands": [_py("import sys; sys.exit(1)")]}},
    )
    cfg = discover_artifact_verify(tmp_path)
    res = verify(cfg, thread_dir=tmp_path)
    assert res.passed is False
    assert res.commands[0].outcome == OUTCOME_FAIL
    assert res.commands[0].exit_code == 1

    review = res.to_review(version_dir="paper.1", critic_id="paper-artifact-verify")
    assert review.kind == Kind.TOOL_EVIDENCE
    types = {cf.type for cf in review.critical_flags}
    assert f"{GATE_NAME}_0" in types

    # The failing finding is a blocker.
    assert any(f.severity == "blocker" for f in review.findings)

    # Route through the existing aggregator + verdict path — no schema
    # change, no aggregator change.
    agg = aggregate([review])
    assert compute_verdict(agg, threshold=35) == Verdict.BLOCK

    # Schema round-trip validates the kind=tool_evidence tool_calls contract.
    review2 = Review.model_validate(review.model_dump())
    assert len(review2.critical_flags) == len(review.critical_flags)
    assert all(f.tool_calls is not None for f in review2.findings)


def test_timeout_emits_flag_and_blocks(tmp_path):
    """A command exceeding timeout_s is OUTCOME_TIMEOUT → CriticalFlag + BLOCK."""
    _write_anvil_json(
        tmp_path,
        {
            "artifact_verify": {
                "commands": [_py("import time; time.sleep(30)")],
                "timeout_s": 1,
            }
        },
    )
    cfg = discover_artifact_verify(tmp_path)
    assert cfg.timeout_s == 1
    res = verify(cfg, thread_dir=tmp_path)
    assert res.passed is False
    assert res.commands[0].outcome == OUTCOME_TIMEOUT
    assert res.commands[0].exit_code is None

    review = res.to_review(version_dir="paper.1", critic_id="paper-artifact-verify")
    assert any(cf.type == f"{GATE_NAME}_0" for cf in review.critical_flags)
    agg = aggregate([review])
    assert compute_verdict(agg, threshold=35) == Verdict.BLOCK


# -----------------------------------------------------------------------------
# verify(): unresolvable cwd / command → fail-open (major, not silent pass)
# -----------------------------------------------------------------------------


def test_missing_cwd_fails_open_with_major_not_blocker(tmp_path):
    """A declared cwd that does not exist → fail open: ran=False, open_reason
    set, a MAJOR finding, NO CriticalFlag, and NOT a silent pass."""
    _write_anvil_json(
        tmp_path,
        {"artifact_verify": {"commands": [_py("import sys; sys.exit(0)")], "cwd": "nope/"}},
    )
    cfg = discover_artifact_verify(tmp_path)
    res = verify(cfg, thread_dir=tmp_path)
    assert res.ran is False
    assert res.open_reason is not None
    # Fail-open must NOT read as verified.
    assert res.passed is False
    assert res.to_critical_flags() == []

    review = res.to_review(version_dir="paper.1", critic_id="paper-artifact-verify")
    assert review.critical_flags == []
    assert any(f.severity == "major" for f in review.findings)
    # Does not force a BLOCK on its own.
    agg = aggregate([review])
    assert compute_verdict(agg, threshold=35) != Verdict.BLOCK


def test_cwd_that_is_a_file_fails_open(tmp_path):
    """A declared cwd that is a file (not a directory) → fail open."""
    (tmp_path / "afile").write_text("x", encoding="utf-8")
    _write_anvil_json(
        tmp_path,
        {"artifact_verify": {"commands": ["true"], "cwd": "afile"}},
    )
    cfg = discover_artifact_verify(tmp_path)
    res = verify(cfg, thread_dir=tmp_path)
    assert res.ran is False
    assert res.open_reason is not None


def test_unlaunchable_command_is_unresolvable_major(tmp_path):
    """A command whose executable is not on PATH → OUTCOME_UNRESOLVABLE,
    a major finding, NO blocker (fail-open), and passed=False."""
    _write_anvil_json(
        tmp_path,
        {
            "artifact_verify": {
                "commands": ["this-binary-does-not-exist-anywhere-663 --run"]
            }
        },
    )
    cfg = discover_artifact_verify(tmp_path)
    res = verify(cfg, thread_dir=tmp_path)
    assert res.ran is True
    assert res.commands[0].outcome == OUTCOME_UNRESOLVABLE
    assert res.passed is False
    assert res.open_reason is not None

    review = res.to_review(version_dir="paper.1", critic_id="paper-artifact-verify")
    assert review.critical_flags == []  # unresolvable is NOT a blocker
    assert any(f.severity == "major" for f in review.findings)


# -----------------------------------------------------------------------------
# Multi-command: run-all, not short-circuit
# -----------------------------------------------------------------------------


def test_multi_command_runs_all_after_a_failure(tmp_path):
    """When an earlier command fails, later commands still run; each failure
    surfaces as a distinct artifact_verify_<n> flag."""
    marker = tmp_path / "third-ran.txt"
    _write_anvil_json(
        tmp_path,
        {
            "artifact_verify": {
                "commands": [
                    _py("import sys; sys.exit(1)"),  # index 0: fails
                    _py("import sys; sys.exit(0)"),  # index 1: passes
                    _py(f"open({json.dumps(str(marker))}, 'w').write('x')"),  # index 2
                ]
            }
        },
    )
    cfg = discover_artifact_verify(tmp_path)
    res = verify(cfg, thread_dir=tmp_path)
    # All three commands executed (no short-circuit on the index-0 failure).
    assert len(res.commands) == 3
    assert marker.exists(), "later command did not run after an earlier failure"
    assert res.commands[0].outcome == OUTCOME_FAIL
    assert res.commands[1].outcome == OUTCOME_PASS
    assert res.commands[2].outcome == OUTCOME_PASS

    review = res.to_review(version_dir="paper.1", critic_id="paper-artifact-verify")
    types = {cf.type for cf in review.critical_flags}
    # Exactly the one failing command → exactly one flag.
    assert types == {f"{GATE_NAME}_0"}


# -----------------------------------------------------------------------------
# Sidecar JSON payload shape (_artifact_verify.json)
# -----------------------------------------------------------------------------


def test_to_json_payload_shape(tmp_path):
    """to_json() emits the _artifact_verify.json contract and round-trips."""
    _write_anvil_json(
        tmp_path,
        {"artifact_verify": {"commands": [_py("import sys; sys.exit(1)")]}},
    )
    cfg = discover_artifact_verify(tmp_path)
    res = verify(cfg, thread_dir=tmp_path)
    payload = res.to_json()
    assert payload["gate"] == GATE_NAME
    assert payload["ran"] is True
    assert payload["pass"] is False
    assert isinstance(payload["commands"], list)
    assert payload["commands"][0]["outcome"] == OUTCOME_FAIL
    # JSON-serializable.
    assert json.loads(json.dumps(payload))["pass"] is False


def test_cwd_relative_resolution(tmp_path):
    """A relative cwd is resolved against the thread dir, and a command run
    there sees that directory."""
    proof = tmp_path / "proof"
    proof.mkdir()
    (proof / "marker.txt").write_text("present", encoding="utf-8")
    _write_anvil_json(
        tmp_path,
        {
            "artifact_verify": {
                # Exit 0 only if the cwd contains marker.txt.
                "commands": [
                    _py("import os,sys; sys.exit(0 if os.path.exists('marker.txt') else 2)")
                ],
                "cwd": "proof",
            }
        },
    )
    cfg = discover_artifact_verify(tmp_path)
    res = verify(cfg, thread_dir=tmp_path)
    assert res.passed is True
    assert res.resolved_cwd == str(proof)
