"""Per-company theme primitive (issue #322 — Phase A).

A *theme* is a named bundle of brand-level defaults that anvil skills
resolve below the per-thread BRIEF.md override surface. The motivating
canary need (issue #322) is the studio's portfolio split — one tenant
running multiple brands through the same anvil pipeline — but the
primitive is generic.

Lookup precedence (per the issue body's design)::

    per-thread BRIEF.md document entry
        >  project-level BRIEF.md (theme: <name>)
        >  per-theme theme.yml
        >  framework default

This module owns the **theme.yml loader** — the small typed reader that
turns ``<consumer>/.anvil/themes/<theme>/theme.yml`` into a typed
:class:`Theme`. Per-skill *asset resolvers* (template + stylesheet
precedence walkers) live under each skill's ``lib/`` directory; see
``anvil/skills/memo/lib/theme_resolver.py`` for the Phase A memo
implementation.

Phase A scope
-------------
- Pydantic :class:`Theme` model (open-set per-skill knob blocks via
  ``extra="allow"``).
- :func:`load_theme` reader — returns ``None`` cleanly when the theme
  directory or theme.yml is absent (so consumers without themes are
  unaffected).
- :func:`find_consumer_root` walks upward from a path looking for the
  ``.anvil/`` marker directory (the installed-anvil sentinel — the
  install script writes ``<consumer>/.anvil/anvil/...`` per the post-#230
  layout).

Phase B (deferred to per-skill follow-up issues) lifts the resolver to
``anvil:proposal``, ``anvil:installation``, ``anvil:deck``,
``anvil:slides``, ``anvil:report``, ``anvil:paper``, ``anvil:ip-uspto``.
"""

from __future__ import annotations

from pathlib import Path
from typing import Any, Dict, Optional

import yaml
from pydantic import BaseModel, ConfigDict, Field


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

THEMES_DIRNAME = "themes"
"""Subdirectory under ``<consumer>/.anvil/`` that holds per-theme bundles."""

THEME_FILENAME = "theme.yml"
"""Filename for the top-level theme metadata inside a theme directory."""

ANVIL_DIRNAME = ".anvil"
"""Marker directory at the consumer root containing the installed anvil."""


# ---------------------------------------------------------------------------
# Typed model
# ---------------------------------------------------------------------------


class Theme(BaseModel):
    """Typed representation of a ``<consumer>/.anvil/themes/<name>/theme.yml``.

    The fields enumerated here are the **framework-level** knobs that
    multiple skills consume (accent color, studio name, fonts, render
    engine). Per-skill nested blocks (``memo:``, ``proposal:``,
    ``installation:``, ``deck:``, ``slides:``, ``report:``, ``paper:``,
    ``ip-uspto:``) ride under ``extra="allow"`` — Phase A does not
    enumerate them. Each Phase B follow-up issue will add a typed reader
    for the specific skill's nested block (e.g., adding
    ``proposal.signature_color`` as a typed field once
    ``anvil:proposal`` wires the resolver).

    The theme.yml schema is intentionally **forgiving** about unknown
    fields: themes are consumer-defined and may carry knobs that future
    framework versions formalize. The :func:`load_theme` reader prefers
    "skip silently" over "raise" for unknown keys so the consumer's
    theme.yml isn't a versioning hostage.

    Attributes
    ----------
    name
        The theme's directory basename (e.g. ``"acme-semi"``). Filled
        in by :func:`load_theme`; not a YAML key the consumer writes.
    accent_color
        Cross-skill brand accent (LaTeX, CSS, Marp themes all consume
        this). Free string — typically ``#RRGGBB`` but no validation is
        enforced (some skills want named colors).
    studio
        Studio / company name for cover-page templates, footers, etc.
    body_font
        Body-text font family the renderer should pin. Skills decide
        how to consume it (LaTeX ``\\setmainfont``, CSS
        ``font-family``).
    mono_font
        Monospace font family for code blocks, tables, etc.
    render_engine
        For skills with multiple renderer chains (currently just
        ``anvil:memo``), the brand's preferred engine. Subject to
        availability — if the engine is not on PATH, the skill falls
        back to its existing selection logic. Recognized values
        currently track ``MEMO_ENGINE_WEASYPRINT`` /
        ``MEMO_ENGINE_WKHTMLTOPDF`` / ``MEMO_ENGINE_XELATEX`` for the
        memo skill; future skills define their own enums.
    raw
        The full parsed YAML dict, including any per-skill nested
        blocks the consumer wrote. Phase B readers extract per-skill
        knobs from here until typed fields are added.
    """

    model_config = ConfigDict(extra="allow")

    name: str = Field(..., min_length=1)
    accent_color: Optional[str] = Field(default=None)
    studio: Optional[str] = Field(default=None)
    body_font: Optional[str] = Field(default=None)
    mono_font: Optional[str] = Field(default=None)
    render_engine: Optional[str] = Field(default=None)
    raw: Dict[str, Any] = Field(default_factory=dict)

    def skill_block(self, skill: str) -> Dict[str, Any]:
        """Return the per-skill nested block (``memo:``, ``proposal:``, …).

        Returns an empty dict when the theme does not define the block.
        The returned dict is a **copy** — callers may mutate it without
        affecting the cached theme.
        """
        block = self.raw.get(skill)
        if isinstance(block, dict):
            return dict(block)
        return {}


# ---------------------------------------------------------------------------
# Consumer-root discovery
# ---------------------------------------------------------------------------


def find_consumer_root(start: Path) -> Optional[Path]:
    """Walk upward from ``start`` and return the consumer repo root.

    The "consumer root" is the directory containing the ``.anvil/``
    marker — the directory written by ``scripts/install-anvil.sh`` to
    seat the installed framework. This is the same root the theme
    catalog lives under (``<root>/.anvil/themes/<name>/``).

    Parameters
    ----------
    start
        Any path (file or directory; existent or not). The walk uses
        ``Path`` arithmetic and only consults the filesystem at each
        candidate directory.

    Returns
    -------
    Optional[Path]
        The consumer root, or ``None`` when no enclosing directory has
        a ``.anvil/`` sibling. Tests running from a temp directory
        without an installed anvil get ``None`` and the resolver falls
        through to framework defaults.

    Notes
    -----
    The walk **does not** require that ``.anvil/themes/`` exists — only
    that ``.anvil/`` exists. A consumer who has installed anvil but
    declared no themes still produces a valid consumer root (the theme
    loader returns ``None`` for any specific theme name).
    """
    try:
        current = Path(start).absolute()
    except OSError:
        current = Path(start)

    if not current.is_dir():
        current = current.parent

    visited: set = set()
    while True:
        key = str(current)
        if key in visited:
            return None
        visited.add(key)

        if (current / ANVIL_DIRNAME).is_dir():
            return current

        if current.parent == current:
            return None
        current = current.parent


# ---------------------------------------------------------------------------
# theme.yml loader
# ---------------------------------------------------------------------------


def load_theme(
    consumer_root: Optional[Path], theme_name: Optional[str]
) -> Optional[Theme]:
    """Load ``<consumer_root>/.anvil/themes/<theme_name>/theme.yml``.

    Absence-tolerant by design: returns ``None`` rather than raising
    when the consumer root, theme directory, or theme.yml is missing.
    Callers (asset resolvers) treat a ``None`` return as "no theme tier
    applies, fall through to the next precedence level".

    Parameters
    ----------
    consumer_root
        The consumer repo root (the directory containing ``.anvil/``).
        When ``None``, the function short-circuits and returns ``None``
        — caller did not locate a consumer root and there's no theme
        catalog to consult.
    theme_name
        The theme's directory basename, as declared by the project
        BRIEF's ``theme:`` field. When ``None`` or empty, the function
        returns ``None`` — no theme was declared.

    Returns
    -------
    Optional[Theme]
        Parsed theme, or ``None`` when any of:

        - ``consumer_root`` is ``None``.
        - ``theme_name`` is ``None`` or empty.
        - ``<consumer_root>/.anvil/themes/<theme_name>/`` does not
          exist or is not a directory.
        - ``<consumer_root>/.anvil/themes/<theme_name>/theme.yml`` does
          not exist (a theme dir may be a typography-only override
          tier with no metadata — that's valid; just no Theme model).
        - The theme.yml file is unreadable or has unparseable YAML.

    Raises
    ------
    This function never raises. Misconfiguration in theme.yml (e.g. a
    non-dict top-level value) returns ``None`` — the consumer's render
    falls through to the next tier. This matches the broader anvil
    pattern of graceful degrade for opt-in overrides.

    Examples
    --------
    >>> theme = load_theme(Path("/repo"), "acme-semi")
    >>> theme.accent_color
    '#0066CC'
    >>> theme.skill_block("memo").get("signature_color")
    '#0066CC'
    """
    if consumer_root is None:
        return None
    if theme_name is None or not str(theme_name).strip():
        return None

    theme_dir = Path(consumer_root) / ANVIL_DIRNAME / THEMES_DIRNAME / theme_name
    if not theme_dir.is_dir():
        return None

    theme_file = theme_dir / THEME_FILENAME
    if not theme_file.is_file():
        return None

    try:
        text = theme_file.read_text(encoding="utf-8")
    except OSError:
        return None

    try:
        parsed = yaml.safe_load(text)
    except yaml.YAMLError:
        return None

    if not isinstance(parsed, dict):
        # Empty file (``None``), top-level list, or malformed — treat
        # as "no theme metadata available" rather than raising.
        return None

    # The pydantic model rejects unknown TYPED fields with a clear
    # message, but unknown keys are allowed via ``extra="allow"``. We
    # extract the known typed fields explicitly so the model never
    # rejects a forward-compat key in theme.yml.
    typed: Dict[str, Any] = {
        "name": theme_name,
        "raw": parsed,
    }
    for field in ("accent_color", "studio", "body_font", "mono_font", "render_engine"):
        value = parsed.get(field)
        if value is not None and not isinstance(value, str):
            # Wrong-type field: treat as absent rather than raise.
            continue
        typed[field] = value

    try:
        return Theme(**typed)
    except Exception:  # pragma: no cover — defensive; pydantic settings forbid this
        return None


__all__ = [
    "ANVIL_DIRNAME",
    "THEMES_DIRNAME",
    "THEME_FILENAME",
    "Theme",
    "find_consumer_root",
    "load_theme",
]
