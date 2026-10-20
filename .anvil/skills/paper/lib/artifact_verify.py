"""Deterministic external-artifact verification gate for ``anvil:paper``.

This is the paper-skill analog of ``anvil/lib/render_gate.py``: a cheap,
deterministic pre-scoring gate that runs *before* the expensive LLM content
review. Where the render gate verifies the *rendered paper* (page fit,
overfull boxes, compile success, placeholders) and the numeric-consistency
checker verifies *claim-vs-claim arithmetic within the paper text*, this
gate verifies a paper's claims against an **external artifact** the paper
depends on — a companion code/proof repository, a benchmark harness, a
dataset checksum — by *running it*.

Motivating incident (the tractatus canary, 2026-07-13): a review pass once
ACCEPTed a paper version whose companion Lean 4 proof repository did not
build and whose headline theorem was false — caught only later by actually
running ``lake build`` and diffing statements against proofs. Nothing in
``paper-review`` today runs the external artifact the paper's central claim
rests on; this gate closes that gap.

Skill-local first (``CLAUDE.md`` "wait for the second consumer before
generalizing"): this is a paper-specific need with no second consumer yet.
It reuses the framework ``Review`` / ``CriticalFlag`` / ``Finding`` /
``Score`` / ``Kind.TOOL_EVIDENCE`` types directly (no schema change) and
routes failures through the unmodified ``anvil/lib/critics.py`` aggregator
exactly as the render gate does. Promote to ``anvil/lib/`` only if a second
skill (``installation`` / ``report`` / ``ip-uspto``) wants the same hook.

Declaration contract (fail-open)
--------------------------------

The gate is driven by an optional ``artifact_verify`` field in
``<thread>/.anvil.json`` (documented in ``anvil/skills/paper/SKILL.md``'s
``.anvil.json`` schema table), mirroring the venue-overlay discovery
contract in ``anvil/lib/rubric.py::discover_venue_rubric``::

    {
      "artifact_verify": {
        "commands": ["lake build", "lake exe check_theorems"],
        "cwd": "proof/",
        "timeout_s": 300
      }
    }

- **Absent** (the default for every existing thread): behavior is
  byte-identical to today — no subprocess call, no file written, no
  finding. This is the load-bearing fail-open contract the issue asks
  for. Callers detect this via ``ArtifactVerifyConfig.declared == False``
  and simply skip the gate.
- **Declared but unresolvable** (missing/non-existent ``cwd``, ``cwd`` is
  a file, or a command isn't resolvable): the gate fails **open** with a
  stdout-facing warning (mirroring ``discover_venue_rubric``'s
  "declared but no matching YAML found" warning) and a ``major`` finding
  in the review — a broken declaration is a defect worth surfacing, but
  must not be indistinguishable from "the reviewer never checked". It
  does NOT emit a ``blocker`` / ``CriticalFlag`` and does NOT silently
  pass as "verified".
- **Declared and resolvable**: each command runs via ``subprocess.run``
  with the declared ``cwd`` and ``timeout_s``. A failed command (non-zero
  exit OR timeout) emits a ``CriticalFlag`` (``type`` prefix
  ``artifact_verify_*``) that routes through the existing
  ``compute_verdict`` path and forces ``Verdict.BLOCK`` — no aggregator or
  schema change needed.

Run-all, not short-circuit
--------------------------

All declared commands run even after an earlier one fails (same posture
as the render gate's independent checks) so a reviewer sees every failing
step in one pass, each surfaced as a distinct ``artifact_verify_<n>``
flag. A command that does not run because a *prior command in the same
list* failed does not happen — each command is a separate subprocess and
they all execute; the caller gets the full picture.

Subprocess-only, no new Python dependency (``CLAUDE.md`` "Add Python deps
only when subprocess won't do"). The raw stdout/stderr capture is written
to ``<thread>.{N}.review/_artifact_verify.json`` (mirroring the render
gate's ``_gate.json``) for CI/operator inspection — a conditional output,
NOT in the review's required-files manifest (same treatment as
``_gate.json`` / ``_review.venue.json``).
"""

from __future__ import annotations

import json
import shlex
import subprocess
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

from anvil.lib.review_schema import (
    CriticalFlag,
    Finding,
    Kind,
    Review,
    Score,
)


# Gate name used in findings/reasons and the JSON payload.
GATE_NAME = "artifact_verify"

# Default per-command timeout in seconds when ``timeout_s`` is unset or
# malformed. Chosen to match the issue's example (a Lean ``lake build`` from
# scratch is the motivating workload).
DEFAULT_TIMEOUT_S = 300

# Per-command outcome tags surfaced in the JSON payload and findings.
OUTCOME_PASS = "pass"          # command exited 0
OUTCOME_FAIL = "fail"          # command exited non-zero
OUTCOME_TIMEOUT = "timeout"    # command exceeded timeout_s
OUTCOME_UNRESOLVABLE = "unresolvable"  # command not launchable (OSError)

# Cap on captured stdout/stderr per command (bytes of text) written into
# ``_artifact_verify.json``. A runaway build log should not bloat the
# sidecar; the tail is the operationally useful part.
_CAPTURE_TAIL_CHARS = 20_000


# -----------------------------------------------------------------------------
# Config discovery (fail-open, mirrors discover_venue_rubric)
# -----------------------------------------------------------------------------


@dataclass
class ArtifactVerifyConfig:
    """Parsed ``artifact_verify`` block from ``<thread>/.anvil.json``.

    ``declared`` is the load-bearing fail-open discriminator: ``False``
    means no ``artifact_verify`` block was present (or it was empty /
    malformed to the point of carrying no commands), so the caller skips
    the gate entirely and the review is byte-identical to pre-#663.
    """

    declared: bool
    commands: list[str] = field(default_factory=list)
    cwd: Optional[str] = None
    timeout_s: int = DEFAULT_TIMEOUT_S
    # A one-line note recorded when the declaration itself is malformed
    # (e.g. ``commands`` is not a list of strings). Surfaced as a warning
    # by the caller; the gate still fails open.
    config_warning: Optional[str] = None


def _read_anvil_json(thread_dir: Path) -> dict:
    """Read ``<thread_dir>/.anvil.json`` and return the parsed dict (or {}).

    Mirrors ``anvil/lib/rubric.py::_read_anvil_json`` — a missing file,
    unreadable file, malformed JSON, or non-dict top level all degrade to
    an empty dict rather than raising.
    """
    anvil_json = thread_dir / ".anvil.json"
    if not anvil_json.is_file():
        return {}
    try:
        with anvil_json.open("r", encoding="utf-8") as fh:
            data = json.load(fh)
    except (json.JSONDecodeError, OSError):
        return {}
    if not isinstance(data, dict):
        return {}
    return data


def discover_artifact_verify(thread_dir: Path) -> ArtifactVerifyConfig:
    """Discover the ``artifact_verify`` config for a thread.

    Reads ``<thread_dir>/.anvil.json`` for the ``artifact_verify`` field.
    Returns a config with ``declared=False`` (the fail-open default, no
    gate) when:

    - there is no ``.anvil.json`` (or it is unreadable / malformed JSON),
    - there is no ``artifact_verify`` key,
    - ``artifact_verify`` is ``null`` / not an object,
    - ``artifact_verify.commands`` is absent / empty / not a list of
      non-empty strings.

    When ``commands`` carries at least one usable string, returns a config
    with ``declared=True`` and the resolved ``commands`` / ``cwd`` /
    ``timeout_s`` (a malformed ``timeout_s`` silently falls back to
    :data:`DEFAULT_TIMEOUT_S`, matching the render gate's
    coerce-or-fallback contract for ``words_per_page``). A partially
    malformed block that still yields ≥1 command sets ``config_warning``
    so the caller can surface the defect without discarding the whole
    declaration.
    """
    config = _read_anvil_json(thread_dir)
    block = config.get("artifact_verify")
    if not isinstance(block, dict):
        # Absent, null, or wrong shape → fail open (no gate). Note we do
        # NOT warn here: an absent block is the common, intended default.
        return ArtifactVerifyConfig(declared=False)

    raw_commands = block.get("commands")
    warning: Optional[str] = None
    commands: list[str] = []
    if isinstance(raw_commands, list):
        for entry in raw_commands:
            if isinstance(entry, str) and entry.strip():
                commands.append(entry.strip())
            else:
                warning = (
                    "artifact_verify.commands contains a non-string or "
                    "empty entry; skipped it."
                )
    elif raw_commands is not None:
        warning = (
            "artifact_verify.commands must be a list of command strings; "
            f"got {type(raw_commands).__name__}."
        )

    if not commands:
        # Declared but carrying no runnable command → fail open. Surface
        # the broken declaration as a warning so it is distinguishable
        # from "never declared".
        return ArtifactVerifyConfig(
            declared=False,
            config_warning=(
                warning
                or "artifact_verify declared but carries no runnable "
                "commands; skipping the gate."
            ),
        )

    raw_cwd = block.get("cwd")
    cwd = raw_cwd.strip() if isinstance(raw_cwd, str) and raw_cwd.strip() else None

    raw_timeout = block.get("timeout_s")
    timeout_s = DEFAULT_TIMEOUT_S
    if isinstance(raw_timeout, bool):
        # bool is an int subclass — reject it explicitly so ``true`` does
        # not become a 1-second timeout.
        pass
    elif isinstance(raw_timeout, (int, float)) and raw_timeout > 0:
        timeout_s = int(raw_timeout)
    elif raw_timeout is not None:
        warning = (
            (warning + " " if warning else "")
            + "artifact_verify.timeout_s must be a positive number; "
            f"falling back to {DEFAULT_TIMEOUT_S}s."
        )

    return ArtifactVerifyConfig(
        declared=True,
        commands=commands,
        cwd=cwd,
        timeout_s=timeout_s,
        config_warning=warning,
    )


# -----------------------------------------------------------------------------
# Result types (mirror render_gate.GateFinding / GateResult)
# -----------------------------------------------------------------------------


@dataclass
class CommandResult:
    """Outcome of running one declared ``artifact_verify`` command."""

    index: int                 # 0-based position in the commands list
    command: str               # the raw command string as declared
    outcome: str               # one of OUTCOME_* above
    exit_code: Optional[int]   # process exit code (None on timeout / unresolvable)
    stdout_tail: str           # last _CAPTURE_TAIL_CHARS of stdout
    stderr_tail: str           # last _CAPTURE_TAIL_CHARS of stderr

    @property
    def passed(self) -> bool:
        return self.outcome == OUTCOME_PASS

    def to_dict(self) -> dict:
        return {
            "index": self.index,
            "command": self.command,
            "outcome": self.outcome,
            "exit_code": self.exit_code,
            "stdout_tail": self.stdout_tail,
            "stderr_tail": self.stderr_tail,
        }


@dataclass
class ArtifactVerifyResult:
    """Outcome of one artifact-verify pass. JSON-serializable + Review-emitter.

    The typed ``Review`` emitted by ``to_review`` carries one
    ``CriticalFlag`` per failed command (non-zero exit or timeout), which
    forces ``Verdict.BLOCK`` in the aggregator without any schema change —
    the exact shape ``render_gate.GateResult`` established.

    ``passed`` is ``True`` only when the gate actually ran AND every
    command exited 0. A fail-open (``ran=False``) result is NOT a pass in
    the "verified" sense — it carries ``passed=False`` with an
    ``open_reason`` so a reader can tell the artifact was not verified
    rather than silently trusting it. Fail-open results emit no
    ``CriticalFlag`` (they must not block the review) but DO surface a
    ``major`` finding via ``to_review`` when a broken declaration caused
    the skip.
    """

    ran: bool                        # True when at least one command executed
    cwd: Optional[str]               # the resolved cwd string (as declared)
    resolved_cwd: Optional[str]      # the absolute cwd used, or None if unresolved
    timeout_s: int
    commands: list[CommandResult] = field(default_factory=list)
    passed: bool = True
    reasons: list[str] = field(default_factory=list)
    # Populated when the gate failed open (declaration broken / cwd
    # unresolvable). ``None`` on a normal run.
    open_reason: Optional[str] = None

    @property
    def failed_commands(self) -> list[CommandResult]:
        return [c for c in self.commands if not c.passed]

    def to_json(self) -> dict:
        """Emit the ``_artifact_verify.json`` payload.

        Keys mirror the render gate's ``_gate.json`` shape: a ``gate``
        tag, the per-command results, a ``pass`` boolean, and ``reasons``.
        """
        return {
            "gate": GATE_NAME,
            "ran": self.ran,
            "cwd": self.cwd,
            "resolved_cwd": self.resolved_cwd,
            "timeout_s": self.timeout_s,
            "commands": [c.to_dict() for c in self.commands],
            "pass": self.passed,
            "open_reason": self.open_reason,
            "reasons": list(self.reasons),
        }

    def to_critical_flags(self) -> list[CriticalFlag]:
        """One ``CriticalFlag`` per failed command.

        Empty list when the gate passed OR when it failed open (a broken
        declaration surfaces as a ``major`` finding, never a blocker — it
        must not be indistinguishable from an unverified artifact silently
        passing). The flag ``type`` follows the ``artifact_verify_<n>``
        convention (``<n>`` is the 0-based command index) so downstream
        consumers can route on the specific failing step.
        """
        flags: list[CriticalFlag] = []
        for cr in self.failed_commands:
            if cr.outcome == OUTCOME_UNRESOLVABLE:
                # An unlaunchable command is a broken declaration, not a
                # verified failure — surfaced as a major finding, not a
                # blocker (see to_review).
                continue
            if cr.outcome == OUTCOME_TIMEOUT:
                justification = (
                    f"artifact_verify command {cr.index} timed out after "
                    f"{self.timeout_s}s: {cr.command!r}. The external "
                    "artifact did not verify within the declared budget."
                )
            else:
                justification = (
                    f"artifact_verify command {cr.index} exited "
                    f"{cr.exit_code}: {cr.command!r}. The external artifact "
                    "the paper's claims rest on did not verify (run the "
                    "artifact, not just the PDF)."
                )
            flags.append(
                CriticalFlag(
                    type=f"{GATE_NAME}_{cr.index}",
                    justification=justification,
                )
            )
        return flags

    def to_review(self, *, version_dir: str, critic_id: str) -> Review:
        """Build a typed ``Review`` (``kind=Kind.TOOL_EVIDENCE``) for the
        critics aggregator.

        Mirrors ``render_gate.GateResult.to_review``:

        - a one-row scorecard with ``score=None`` (the gate owns no rubric
          dimension; it is a pre-flight pass/fail), so ``aggregate`` treats
          this critic as null-everywhere for scoring purposes.
        - one ``CriticalFlag`` per failed command (via
          ``to_critical_flags``) → forces ``Verdict.BLOCK`` in
          ``compute_verdict``.
        - findings: a ``blocker`` per non-zero/timeout command and a
          ``major`` per unresolvable command or broken declaration (the
          fail-open path). ``tool_calls=[]`` on every finding satisfies the
          ``Kind.TOOL_EVIDENCE`` schema requirement.
        """
        scores = [
            Score(
                dimension=GATE_NAME,
                score=None,
                max=1,
                justification=(
                    "artifact-verify is pre-flight pass/fail; owns no "
                    "rubric dim."
                ),
            )
        ]
        findings: list[Finding] = []

        if self.open_reason is not None:
            # Fail-open path: a broken declaration is a defect worth
            # surfacing, but it is NOT a blocker (it must not read as an
            # unverified artifact silently passing).
            findings.append(
                Finding(
                    severity="major",
                    dimension=GATE_NAME,
                    evidence_span=".anvil.json",
                    rationale=self.open_reason,
                    suggested_fix=(
                        "Fix the artifact_verify declaration in "
                        ".anvil.json (a resolvable cwd and runnable "
                        "commands) so the external artifact is actually "
                        "verified, or remove the block to opt out."
                    ),
                    tool_calls=[],
                )
            )

        for cr in self.failed_commands:
            if cr.outcome == OUTCOME_UNRESOLVABLE:
                findings.append(
                    Finding(
                        severity="major",
                        dimension=GATE_NAME,
                        evidence_span=".anvil.json",
                        rationale=(
                            f"artifact_verify command {cr.index} could not "
                            f"be launched: {cr.command!r}. {cr.stderr_tail}"
                        ),
                        suggested_fix=(
                            "Ensure the command's executable is on PATH and "
                            "the declared cwd exists."
                        ),
                        tool_calls=[],
                    )
                )
            else:
                detail = (
                    f"timed out after {self.timeout_s}s"
                    if cr.outcome == OUTCOME_TIMEOUT
                    else f"exited {cr.exit_code}"
                )
                findings.append(
                    Finding(
                        severity="blocker",
                        dimension=GATE_NAME,
                        evidence_span=".anvil.json",
                        rationale=(
                            f"artifact_verify command {cr.index} {detail}: "
                            f"{cr.command!r}. stderr tail: {cr.stderr_tail}"
                        ),
                        suggested_fix=(
                            "Fix the external artifact so the command "
                            "succeeds, or correct the paper's claim that "
                            "the artifact was meant to substantiate."
                        ),
                        tool_calls=[],
                    )
                )

        return Review(
            schema_version="1",
            kind=Kind.TOOL_EVIDENCE,
            version_dir=version_dir,
            critic_id=critic_id,
            scores=scores,
            findings=findings,
            critical_flags=self.to_critical_flags(),
        )


# -----------------------------------------------------------------------------
# Public API: verify()
# -----------------------------------------------------------------------------


def _tail(text: str) -> str:
    """Return the last ``_CAPTURE_TAIL_CHARS`` chars of ``text``."""
    if len(text) <= _CAPTURE_TAIL_CHARS:
        return text
    return "…(truncated)…\n" + text[-_CAPTURE_TAIL_CHARS:]


def verify(config: ArtifactVerifyConfig, *, thread_dir: Path) -> ArtifactVerifyResult:
    """Run the declared ``artifact_verify`` commands over an external artifact.

    Parameters
    ----------
    config:
        The parsed declaration from :func:`discover_artifact_verify`. When
        ``config.declared`` is ``False`` this function is NOT expected to be
        called (the caller skips the gate entirely on the fail-open
        default); if it is called anyway it returns a ``ran=False`` result
        so a mis-wired caller still degrades safely.
    thread_dir:
        The thread root (the directory that owns ``.anvil.json``). The
        declared ``cwd`` is resolved relative to this dir when it is not
        absolute — matching the venue-overlay convention that per-thread
        config paths are thread-relative.

    Resolution / fail-open contract
    -------------------------------

    - ``config.declared == False`` → ``ran=False``, ``passed=False``, no
      commands, no flags.
    - ``cwd`` declared but missing / not a directory → **fail open**:
      ``ran=False``, ``open_reason`` set, no commands run, no blocker (a
      ``major`` finding is surfaced by ``to_review``). Does NOT silently
      pass as verified.
    - otherwise → each command runs via ``subprocess.run`` with the
      resolved ``cwd`` and ``config.timeout_s``. Commands are parsed with
      ``shlex.split`` (POSIX tokenization); an unparseable command string
      or an unlaunchable executable is recorded as ``OUTCOME_UNRESOLVABLE``
      (a ``major`` finding, fail-open) rather than crashing. A non-zero
      exit or timeout is ``OUTCOME_FAIL`` / ``OUTCOME_TIMEOUT`` (a
      ``blocker`` + ``CriticalFlag``). ALL commands run — no short-circuit.
    """
    if not config.declared:
        return ArtifactVerifyResult(
            ran=False,
            cwd=config.cwd,
            resolved_cwd=None,
            timeout_s=config.timeout_s,
            passed=False,
            reasons=[f"{GATE_NAME}: not declared; gate skipped (fail-open)."],
        )

    # Resolve cwd relative to the thread root when not absolute.
    if config.cwd is None:
        resolved = thread_dir
    else:
        cwd_path = Path(config.cwd)
        resolved = cwd_path if cwd_path.is_absolute() else (thread_dir / cwd_path)

    if not resolved.exists() or not resolved.is_dir():
        what = "does not exist" if not resolved.exists() else "is not a directory"
        open_reason = (
            f"{GATE_NAME}: declared cwd {str(resolved)!r} {what}; "
            "gate failed open (artifact NOT verified)."
        )
        return ArtifactVerifyResult(
            ran=False,
            cwd=config.cwd,
            resolved_cwd=None,
            timeout_s=config.timeout_s,
            passed=False,
            reasons=[open_reason],
            open_reason=open_reason,
        )

    results: list[CommandResult] = []
    reasons: list[str] = []
    for i, command in enumerate(config.commands):
        try:
            argv = shlex.split(command)
        except ValueError as exc:
            results.append(
                CommandResult(
                    index=i,
                    command=command,
                    outcome=OUTCOME_UNRESOLVABLE,
                    exit_code=None,
                    stdout_tail="",
                    stderr_tail=f"unparseable command string: {exc}",
                )
            )
            reasons.append(
                f"{GATE_NAME}: command {i} is unparseable ({exc}); "
                "recorded as unresolvable (fail-open major)."
            )
            continue
        if not argv:
            results.append(
                CommandResult(
                    index=i,
                    command=command,
                    outcome=OUTCOME_UNRESOLVABLE,
                    exit_code=None,
                    stdout_tail="",
                    stderr_tail="empty command",
                )
            )
            continue
        try:
            proc = subprocess.run(
                argv,
                cwd=str(resolved),
                capture_output=True,
                text=True,
                timeout=config.timeout_s,
                check=False,
            )
        except subprocess.TimeoutExpired as exc:
            results.append(
                CommandResult(
                    index=i,
                    command=command,
                    outcome=OUTCOME_TIMEOUT,
                    exit_code=None,
                    stdout_tail=_tail(exc.stdout.decode() if isinstance(exc.stdout, bytes) else (exc.stdout or "")),
                    stderr_tail=_tail(exc.stderr.decode() if isinstance(exc.stderr, bytes) else (exc.stderr or "")),
                )
            )
            reasons.append(
                f"{GATE_NAME}: command {i} timed out after "
                f"{config.timeout_s}s: {command!r}."
            )
            continue
        except (OSError, ValueError) as exc:
            # Executable not on PATH, permission denied, etc. A broken
            # declaration, not a verified failure → fail-open major.
            results.append(
                CommandResult(
                    index=i,
                    command=command,
                    outcome=OUTCOME_UNRESOLVABLE,
                    exit_code=None,
                    stdout_tail="",
                    stderr_tail=str(exc),
                )
            )
            reasons.append(
                f"{GATE_NAME}: command {i} could not be launched "
                f"({exc}); recorded as unresolvable (fail-open major)."
            )
            continue

        outcome = OUTCOME_PASS if proc.returncode == 0 else OUTCOME_FAIL
        results.append(
            CommandResult(
                index=i,
                command=command,
                outcome=outcome,
                exit_code=proc.returncode,
                stdout_tail=_tail(proc.stdout or ""),
                stderr_tail=_tail(proc.stderr or ""),
            )
        )
        if outcome == OUTCOME_FAIL:
            reasons.append(
                f"{GATE_NAME}: command {i} exited {proc.returncode}: {command!r}."
            )

    # ``passed`` is True only when every command exited 0. An unresolvable
    # command is a fail-open defect (major), so it also makes ``passed``
    # False — the artifact was not proven to verify. ``open_reason`` is set
    # when any command was unresolvable so a reader can distinguish "the
    # artifact failed" from "the declaration was broken".
    any_unresolvable = any(c.outcome == OUTCOME_UNRESOLVABLE for c in results)
    open_reason: Optional[str] = None
    if any_unresolvable:
        open_reason = (
            f"{GATE_NAME}: one or more commands were unresolvable "
            "(unlaunchable / unparseable); gate failed open for those "
            "(artifact NOT verified)."
        )
    passed = all(c.passed for c in results)

    return ArtifactVerifyResult(
        ran=True,
        cwd=config.cwd,
        resolved_cwd=str(resolved),
        timeout_s=config.timeout_s,
        commands=results,
        passed=passed,
        reasons=reasons,
        open_reason=open_reason,
    )


__all__ = [
    "GATE_NAME",
    "DEFAULT_TIMEOUT_S",
    "OUTCOME_PASS",
    "OUTCOME_FAIL",
    "OUTCOME_TIMEOUT",
    "OUTCOME_UNRESOLVABLE",
    "ArtifactVerifyConfig",
    "ArtifactVerifyResult",
    "CommandResult",
    "discover_artifact_verify",
    "verify",
]
