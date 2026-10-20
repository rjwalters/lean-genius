"""Read-only introspection + rendering for the `anvil:help` skill (#725).

Pure functions over a consumer repo's on-disk Anvil install state. No
function in this module writes anywhere — the skill is read-only by
construction (SHA-256-verified in ``tests/test_help_readonly.py``).

Introspection sources, in priority order:

1. ``.anvil/install-metadata.json`` — the authoritative ``installed_skills``
   list plus ``anvil_version`` / ``skill_versions``. Parsed defensively; a
   missing or malformed manifest is a soft-fail (``ManifestResult.ok`` is
   ``False``), not an exception.
2. ``.claude/skills/anvil-*/`` and ``.agents/skills/anvil-*/`` — fallback
   skill enumeration when the manifest is unavailable (degraded mode). The
   former is Claude Code's registration shim glob; the latter is Codex
   CLI's (issue #1004, produced by ``write_codex_shim()`` in
   ``install-anvil.sh`` since #1003). Both are unioned so a Codex-only
   install (no ``.claude/`` at all) still reports accurately.
3. ``.anvil/skills/<name>/SKILL.md`` frontmatter — per-skill description +
   the artifact-vs-utility classification.
4. ``.anvil/skills/<name>/commands/*.md`` — the real command set.
5. ``.anvil/skills/<name>/rubric.md`` — total + advance threshold (when
   present; artifact-class skills only).

The source-repo layout (``anvil/skills/<name>/…``, no ``.anvil/`` prefix) is
also recognized so the command works from an Anvil checkout, not only a
consumer install.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from pathlib import Path


# --------------------------------------------------------------------------
# Manifest parsing
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class ManifestResult:
    """Outcome of reading ``.anvil/install-metadata.json``.

    ``ok`` is ``True`` only when the manifest was present, parsed as JSON,
    and carried an ``installed_skills`` list. Otherwise ``ok`` is ``False``
    and ``reason`` names the degraded-mode cause; callers fall back to the
    shim glob.
    """

    ok: bool
    installed_skills: tuple[str, ...] = ()
    anvil_version: str | None = None
    skill_versions: dict[str, str] = field(default_factory=dict)
    reason: str = ""


def read_manifest(repo_root: Path) -> ManifestResult:
    """Read + defensively parse ``.anvil/install-metadata.json``.

    Never raises on a missing or malformed manifest — returns a
    ``ManifestResult`` with ``ok=False`` and a human-readable ``reason``.
    """
    path = repo_root / ".anvil" / "install-metadata.json"
    if not path.is_file():
        return ManifestResult(ok=False, reason="manifest not found")
    try:
        raw = path.read_text(encoding="utf-8")
    except OSError as exc:  # pragma: no cover - unusual FS error
        return ManifestResult(ok=False, reason=f"manifest unreadable: {exc}")
    try:
        data = json.loads(raw)
    except (json.JSONDecodeError, ValueError):
        return ManifestResult(ok=False, reason="manifest is not valid JSON")
    if not isinstance(data, dict):
        return ManifestResult(ok=False, reason="manifest is not a JSON object")

    installed = data.get("installed_skills")
    if not isinstance(installed, list) or not all(
        isinstance(s, str) for s in installed
    ):
        return ManifestResult(
            ok=False, reason="manifest has no valid installed_skills list"
        )

    version = data.get("anvil_version")
    if not isinstance(version, str):
        version = None

    raw_versions = data.get("skill_versions")
    versions: dict[str, str] = {}
    if isinstance(raw_versions, dict):
        for k, v in raw_versions.items():
            if isinstance(k, str) and isinstance(v, str):
                versions[k] = v

    return ManifestResult(
        ok=True,
        installed_skills=tuple(sorted(installed)),
        anvil_version=version,
        skill_versions=versions,
    )


def enumerate_shim_skills(repo_root: Path) -> tuple[str, ...]:
    """Fallback skill list from ``.claude/skills/anvil-*/`` and
    ``.agents/skills/anvil-*/`` shim dirs (issue #1004).

    ``.claude/skills/`` is Claude Code's registration-shim glob;
    ``.agents/skills/`` is Codex CLI's equivalent (produced by
    ``write_codex_shim()`` in ``install-anvil.sh`` since #1003). Both are
    scanned and unioned so a Codex-only install (no ``.claude/`` directory
    at all) still reports the correct skill list, not an empty one.

    Strips the ``anvil-`` prefix. Sorted, deduplicated. Used only when the
    manifest is unavailable (degraded mode).
    """
    names: set[str] = set()
    for shim_root in (
        repo_root / ".claude" / "skills",
        repo_root / ".agents" / "skills",
    ):
        if not shim_root.is_dir():
            continue
        for child in shim_root.iterdir():
            if child.is_dir() and child.name.startswith("anvil-"):
                names.add(child.name[len("anvil-") :])
    return tuple(sorted(names))


def enumerate_source_skills(repo_root: Path) -> tuple[str, ...]:
    """Last-resort skill list from the per-skill dir base directly.

    When neither the manifest nor the shim glob is available — the case
    when running from a bare Anvil source checkout (no ``.anvil/`` install,
    no ``.claude/`` shims) — enumerate the ``<base>/<name>/SKILL.md`` dirs
    themselves. Sorted, deduplicated.
    """
    base = skills_base(repo_root)
    if base is None:
        return ()
    names: set[str] = set()
    for child in base.iterdir():
        if child.is_dir() and (child / "SKILL.md").is_file():
            names.add(child.name)
    return tuple(sorted(names))


# --------------------------------------------------------------------------
# Per-skill introspection
# --------------------------------------------------------------------------


def skills_base(repo_root: Path) -> Path | None:
    """Return the directory that holds per-skill dirs, or ``None``.

    Prefers the consumer-install layout ``.anvil/skills/``; falls back to
    the source-repo layout ``anvil/skills/`` (so the command works from an
    Anvil checkout too).
    """
    consumer = repo_root / ".anvil" / "skills"
    if consumer.is_dir():
        return consumer
    source = repo_root / "anvil" / "skills"
    if source.is_dir():
        return source
    return None


_FRONTMATTER_RE = re.compile(r"^---\s*\n(.*?)\n---\s*\n", re.DOTALL)


def parse_frontmatter(skill_md_text: str) -> dict[str, str]:
    """Parse the flat ``key: value`` YAML frontmatter of a SKILL.md.

    Deliberately minimal (no full YAML): every Anvil ``SKILL.md`` frontmatter
    is flat ``key: value`` pairs. Returns an empty dict when no frontmatter
    block is present. Values are stripped of surrounding quotes/whitespace.
    """
    match = _FRONTMATTER_RE.match(skill_md_text)
    if not match:
        return {}
    fields: dict[str, str] = {}
    for line in match.group(1).splitlines():
        if ":" not in line:
            continue
        key, _, value = line.partition(":")
        key = key.strip()
        value = value.strip().strip('"').strip("'").strip()
        if key:
            fields[key] = value
    return fields


@dataclass(frozen=True)
class SkillInfo:
    """Introspected metadata for one installed skill."""

    name: str
    description: str
    user_invocable: bool
    is_artifact: bool
    commands: tuple[str, ...]
    rubric_total: int | None
    rubric_threshold: str | None
    has_rubric_file: bool
    version: str | None = None

    @property
    def group(self) -> str:
        return "artifact" if self.is_artifact else "utility"


# Rubric "Total" line, e.g.
#   | | **Total** | **44** | Advance threshold: ≥35 |
#   | | **Total** | **45** | | Advance threshold: ≥39 |
#   | | **Total** | **49** | Advance threshold: **≥43** | |
_RUBRIC_TOTAL_RE = re.compile(
    r"\*\*Total\*\*\s*\|\s*\**\s*(\d+)\s*\**\s*\|"
    r".*?Advance threshold:\s*\**\s*(\S+?)\s*\**\s*(?:\||$)",
    re.IGNORECASE,
)


def parse_rubric_summary(rubric_text: str) -> tuple[int | None, str | None]:
    """Extract ``(total, threshold)`` from a rubric.md's Total line.

    Returns ``(None, None)`` when no line matches the expected pattern —
    the caller degrades to "rubric summary unavailable" rather than crashing.
    """
    for line in rubric_text.splitlines():
        if "**Total**" not in line:
            continue
        match = _RUBRIC_TOTAL_RE.search(line)
        if match:
            try:
                total = int(match.group(1))
            except ValueError:  # pragma: no cover - regex guarantees digits
                return (None, None)
            threshold = match.group(2).strip()
            return (total, threshold or None)
    return (None, None)


def read_skill_info(
    base: Path, name: str, version: str | None = None
) -> SkillInfo | None:
    """Introspect one skill directory. ``None`` when the dir is absent."""
    skill_dir = base / name
    skill_md = skill_dir / "SKILL.md"
    if not skill_md.is_file():
        return None

    try:
        fm = parse_frontmatter(skill_md.read_text(encoding="utf-8"))
    except OSError:  # pragma: no cover - unusual FS error
        fm = {}

    description = fm.get("description", "")
    user_invocable = fm.get("user-invocable", "").strip().lower() == "true"

    commands_dir = skill_dir / "commands"
    commands: list[str] = []
    if commands_dir.is_dir():
        commands = sorted(cmd.stem for cmd in commands_dir.glob("*.md"))

    rubric_file = skill_dir / "rubric.md"
    has_rubric = rubric_file.is_file()
    total: int | None = None
    threshold: str | None = None
    if has_rubric:
        try:
            total, threshold = parse_rubric_summary(
                rubric_file.read_text(encoding="utf-8")
            )
        except OSError:  # pragma: no cover - unusual FS error
            total, threshold = None, None

    # Artifact-class skills are the non-user-invocable, rubric-bearing set;
    # utility / bridge tools are user-invocable and rubric-less. The two
    # signals agree for every shipped skill; user-invocable is the primary
    # (it drives invocation style) and rubric presence is the corroborator.
    is_artifact = (not user_invocable) and has_rubric

    return SkillInfo(
        name=name,
        description=description,
        user_invocable=user_invocable,
        is_artifact=is_artifact,
        commands=tuple(commands),
        rubric_total=total,
        rubric_threshold=threshold,
        has_rubric_file=has_rubric,
        version=version,
    )


# --------------------------------------------------------------------------
# Aggregate model
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class InstallModel:
    """The fully-introspected install state for a consumer repo."""

    anvil_version: str | None
    degraded: bool
    degraded_reason: str
    skills: tuple[SkillInfo, ...]
    unknown_skills: tuple[str, ...]  # named in manifest, no dir on disk

    @property
    def artifact_skills(self) -> tuple[SkillInfo, ...]:
        return tuple(s for s in self.skills if s.is_artifact)

    @property
    def utility_skills(self) -> tuple[SkillInfo, ...]:
        return tuple(s for s in self.skills if not s.is_artifact)

    def find(self, name: str) -> SkillInfo | None:
        for s in self.skills:
            if s.name == name:
                return s
        return None


def build_model(repo_root: Path) -> InstallModel:
    """Introspect ``repo_root`` into an ``InstallModel`` (read-only)."""
    manifest = read_manifest(repo_root)
    base = skills_base(repo_root)

    if manifest.ok:
        names = manifest.installed_skills
        degraded = False
        degraded_reason = ""
    else:
        names = enumerate_shim_skills(repo_root)
        if not names:
            # No manifest and no shims: fall back to the per-skill dir base
            # directly (the bare Anvil source-checkout case).
            names = enumerate_source_skills(repo_root)
        degraded = True
        degraded_reason = manifest.reason

    skills: list[SkillInfo] = []
    unknown: list[str] = []
    for name in names:
        info = None
        if base is not None:
            info = read_skill_info(base, name, manifest.skill_versions.get(name))
        if info is None:
            unknown.append(name)
        else:
            skills.append(info)

    skills.sort(key=lambda s: s.name)
    return InstallModel(
        anvil_version=manifest.anvil_version,
        degraded=degraded,
        degraded_reason=degraded_reason,
        skills=tuple(skills),
        unknown_skills=tuple(sorted(unknown)),
    )


# --------------------------------------------------------------------------
# Rendering
# --------------------------------------------------------------------------

_LIFECYCLE_DIAGRAM = "draft → review → revise → (audit) → figures"


def _start_here_pointer(model: InstallModel) -> str | None:
    """Best "start here" command for an actually-installed skill."""
    artifacts = model.artifact_skills
    if artifacts:
        s = artifacts[0]
        draft = f"{s.name}-draft"
        cmd = draft if draft in s.commands else (s.commands[0] if s.commands else s.name)
        return f"/anvil:{cmd} <slug>"
    utils = model.utility_skills
    if utils:
        return f"/anvil:{utils[0].name} …"
    return None


def render_overview(model: InstallModel) -> str:
    lines: list[str] = []
    lines.append("# Anvil — installed skills")
    lines.append("")
    if model.anvil_version:
        lines.append(f"Anvil version: **{model.anvil_version}**")
    elif model.degraded:
        lines.append(
            "Anvil version: unknown "
            f"(degraded mode — {model.degraded_reason}; "
            "skill list recovered from a .claude/skills/anvil-* / "
            ".agents/skills/anvil-* directory scan)"
        )
    else:
        lines.append("Anvil version: unknown")
    lines.append("")

    if not model.skills and not model.unknown_skills:
        lines.append(
            "No Anvil skills detected in this repo. Run `install-anvil.sh` "
            "from an Anvil checkout to install skills."
        )
        return "\n".join(lines)

    artifacts = model.artifact_skills
    utils = model.utility_skills

    lines.append("## Artifact skills — produce a versioned thread")
    lines.append("")
    if artifacts:
        for s in artifacts:
            lines.append(f"- **{s.name}** — {s.description or '(no description)'}")
    else:
        lines.append("- _(none installed)_")
    lines.append("")

    lines.append("## Utility / bridge tools — one-shot, no thread")
    lines.append("")
    if utils:
        for s in utils:
            lines.append(f"- **{s.name}** — {s.description or '(no description)'}")
    else:
        lines.append("- _(none installed)_")
    lines.append("")

    lines.append("## Lifecycle")
    lines.append("")
    lines.append(
        f"Artifact skills follow the common shape `{_LIFECYCLE_DIAGRAM}`, but "
        "it is NOT uniform: `essay` stops at draft/review/revise/status "
        "(no audit, no figures); `report` adds an AUDITED → CUSTOMER-READY "
        "promotion gate; `ip-uspto` extends it with USPTO-specific phases; "
        "`primer`/`spec` run parallel review + audit and end at AUDITED. "
        "Run `anvil:help <skill>` to see any one skill's real command set."
    )
    lines.append("")
    lines.append(
        "Utility / bridge tools have **no lifecycle** — they are one-shot "
        "(or recurring) commands invoked directly by name, not threads."
    )
    lines.append("")

    if model.unknown_skills:
        lines.append("## Listed in manifest but not found on disk")
        lines.append("")
        for name in model.unknown_skills:
            lines.append(f"- {name}")
        lines.append("")

    pointer = _start_here_pointer(model)
    if pointer:
        lines.append("## Start here")
        lines.append("")
        lines.append(f"Open a thread with: `{pointer}`")
        lines.append("")
    lines.append(
        "Run `anvil:help <skill>` for a skill's command set, rubric, and "
        "thread layout."
    )
    return "\n".join(lines)


def render_skill(model: InstallModel, name: str) -> str:
    info = model.find(name)
    if info is None:
        lines = [f"# anvil:help {name}", ""]
        if name in model.unknown_skills:
            lines.append(
                f"**{name}** is listed in the install manifest but its skill "
                "directory was not found on disk. The install may be "
                "incomplete — try re-running `install-anvil.sh`."
            )
        else:
            installed = ", ".join(s.name for s in model.skills) or "(none)"
            lines.append(
                f"**{name}** is not installed in this repo. `anvil:help` "
                "describes only what is installed, not what is available "
                "upstream."
            )
            lines.append("")
            lines.append(f"Installed skills: {installed}")
        return "\n".join(lines)

    lines: list[str] = [f"# anvil:help {info.name}", ""]
    group = "Artifact skill" if info.is_artifact else "Utility / bridge tool"
    lines.append(f"**Group:** {group}")
    if info.version:
        lines.append(f"**Version:** {info.version}")
    lines.append("")
    if info.description:
        lines.append(info.description)
        lines.append("")

    lines.append("## Commands")
    lines.append("")
    if info.commands:
        for cmd in info.commands:
            lines.append(f"- `/anvil:{cmd}`")
    else:
        lines.append("- _(no commands found on disk)_")
    lines.append("")

    lines.append("## Rubric")
    lines.append("")
    if not info.has_rubric_file:
        lines.append(
            "No rubric — this is a one-shot tool, not a scored artifact thread."
        )
    elif info.rubric_total is None:
        lines.append(
            "Rubric present, but summary unavailable (the rubric's Total line "
            "did not match the expected format). See "
            f"`.anvil/skills/{info.name}/rubric.md` for the full rubric."
        )
    else:
        threshold = info.rubric_threshold or "?"
        lines.append(
            f"Scored on /{info.rubric_total}. Advance threshold: {threshold}. "
            f"Full rubric: `.anvil/skills/{info.name}/rubric.md`."
        )
    lines.append("")

    lines.append("## Thread layout")
    lines.append("")
    if info.is_artifact:
        lines.append(
            f"Each version of a `{info.name}` thread lives in an immutable "
            f"`{{slug}}.{{N}}/` directory with sibling read-only critic dirs "
            "(`.review/`, optional `.audit/`). See "
            f"`.anvil/skills/{info.name}/SKILL.md` for the full state machine."
        )
    else:
        lines.append(
            "No versioned thread — invoke this tool directly by name; it acts "
            "in place with no `{slug}.{N}/` version dirs. See "
            f"`.anvil/skills/{info.name}/SKILL.md` for usage."
        )
    return "\n".join(lines)


def render_help(repo_root, skill: str | None = None) -> str:
    """Top-level entry: introspect ``repo_root`` and render the help text.

    Read-only. ``skill=None`` → overview; ``skill=<name>`` → deep-dive.
    """
    root = Path(repo_root)
    model = build_model(root)
    if skill:
        return render_skill(model, skill)
    return render_overview(model)
