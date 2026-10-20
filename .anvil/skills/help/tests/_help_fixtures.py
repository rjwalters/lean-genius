"""Programmatic fixture builders for the `anvil:help` test suite (#725).

Builds a throwaway consumer-repo tree under a tmp path: a
``.anvil/install-metadata.json`` manifest, ``.anvil/skills/<name>/`` skill
dirs (SKILL.md + commands/ + optional rubric.md), and ``.claude/skills/``
shim dirs. Every builder is a pure function of its arguments so tests stay
deterministic.
"""

from __future__ import annotations

import json
import textwrap
from pathlib import Path


def write_skill_dir(
    base: Path,
    name: str,
    *,
    description: str,
    user_invocable: bool,
    commands: list[str],
    rubric_total: int | None = None,
    rubric_threshold: str | None = None,
    rubric_malformed: bool = False,
) -> None:
    """Create ``base/<name>/`` with SKILL.md, commands/, optional rubric.md."""
    skill_dir = base / name
    (skill_dir / "commands").mkdir(parents=True, exist_ok=True)

    ui = "true" if user_invocable else "false"
    skill_md = textwrap.dedent(
        f"""\
        ---
        name: {name}
        description: {description}
        domain: anvil
        type: skill
        user-invocable: {ui}
        ---

        # anvil:{name}

        Fixture skill body.
        """
    )
    (skill_dir / "SKILL.md").write_text(skill_md, encoding="utf-8")

    for cmd in commands:
        (skill_dir / "commands" / f"{cmd}.md").write_text(
            f"# {cmd}\n", encoding="utf-8"
        )

    if rubric_malformed:
        (skill_dir / "rubric.md").write_text(
            "# Rubric\n\n| | **Total** | (weights vary) | see below |\n",
            encoding="utf-8",
        )
    elif rubric_total is not None:
        threshold = rubric_threshold or "≥35"
        (skill_dir / "rubric.md").write_text(
            "# Rubric\n\n"
            "| # | Dimension | Weight |\n"
            "|---|---|---|\n"
            "| 1 | Something | 5 |\n"
            f"| | **Total** | **{rubric_total}** | Advance threshold: {threshold} |\n",
            encoding="utf-8",
        )


def write_manifest(
    repo_root: Path,
    *,
    installed_skills: list[str],
    anvil_version: str = "0.9.0",
    skill_versions: dict[str, str] | None = None,
    raw: str | None = None,
) -> None:
    """Write ``.anvil/install-metadata.json``. ``raw`` overrides the JSON."""
    manifest_dir = repo_root / ".anvil"
    manifest_dir.mkdir(parents=True, exist_ok=True)
    path = manifest_dir / "install-metadata.json"
    if raw is not None:
        path.write_text(raw, encoding="utf-8")
        return
    data = {
        "anvil_version": anvil_version,
        "layout_version": 2,
        "installed_skills": installed_skills,
        "skill_versions": skill_versions or {},
    }
    path.write_text(json.dumps(data, indent=2), encoding="utf-8")


def write_shim(repo_root: Path, name: str) -> None:
    """Create a ``.claude/skills/anvil-<name>/SKILL.md`` shim."""
    shim_dir = repo_root / ".claude" / "skills" / f"anvil-{name}"
    shim_dir.mkdir(parents=True, exist_ok=True)
    (shim_dir / "SKILL.md").write_text(
        f"---\nname: anvil-{name}\n---\nshim\n", encoding="utf-8"
    )


def write_codex_shim(repo_root: Path, name: str) -> None:
    """Create a ``.agents/skills/anvil-<name>/SKILL.md`` shim (issue #1004).

    Mirrors ``write_shim`` above, but at Codex CLI's repo-root registration
    path (``write_codex_shim()`` in ``install-anvil.sh`` since #1003).
    """
    shim_dir = repo_root / ".agents" / "skills" / f"anvil-{name}"
    shim_dir.mkdir(parents=True, exist_ok=True)
    (shim_dir / "SKILL.md").write_text(
        f"---\nname: anvil-{name}\n---\nshim\n", encoding="utf-8"
    )


def build_repo(
    repo_root: Path,
    *,
    with_manifest: bool = True,
    manifest_raw: str | None = None,
) -> None:
    """Build a small two-artifact + two-utility consumer repo fixture.

    Artifact skills: ``memo`` (rubric /44, ≥35) and ``essay`` (rubric /44,
    ≥35, shorter lifecycle). Utility skills: ``project-scout`` and
    ``help`` (no rubric). Optionally omit or corrupt the manifest.
    """
    skills_base = repo_root / ".anvil" / "skills"

    write_skill_dir(
        skills_base,
        "memo",
        description="Draft, review, and revise investment memos.",
        user_invocable=False,
        commands=["memo", "memo-draft", "memo-review", "memo-revise", "memo-figures"],
        rubric_total=44,
        rubric_threshold="≥35",
    )
    write_skill_dir(
        skills_base,
        "essay",
        description="Draft, review, and revise short-form voice-grounded essays.",
        user_invocable=False,
        commands=["essay", "essay-draft", "essay-review", "essay-revise", "essay-status"],
        rubric_total=44,
        rubric_threshold="≥35",
    )
    write_skill_dir(
        skills_base,
        "project-scout",
        description="Repo-wide read-only discovery of anvil-adoptable clusters.",
        user_invocable=True,
        commands=["project-scout"],
    )
    write_skill_dir(
        skills_base,
        "help",
        description="Read-only orientation for installed Anvil skills.",
        user_invocable=True,
        commands=["help"],
    )

    installed = ["essay", "help", "memo", "project-scout"]
    for name in installed:
        write_shim(repo_root, name)

    if with_manifest:
        write_manifest(
            repo_root,
            installed_skills=installed,
            skill_versions={n: "0.9.0" for n in installed},
            raw=manifest_raw,
        )
