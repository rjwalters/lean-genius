"""Shared YAML-frontmatter extraction primitive (issue #1075).

Consolidates five byte-for-byte-identical ``_extract_frontmatter()``
implementations that had accumulated, each one documenting itself as a
manual mirror of an earlier copy:

- ``anvil/lib/project_discovery.py`` (the original)
- ``anvil/lib/project_brief.py``
- ``anvil/skills/project-share/lib/config.py``
- ``anvil/skills/project-book/lib/config.py``
- ``anvil/skills/proposal/lib/project_brief.py``

``pyyaml>=6.0`` is a declared base dependency (``pyproject.toml``), so
every one of those five call sites can rely on it unconditionally. This
module intentionally does NOT absorb the two lookalikes that keep a
hand-rolled pyyaml-fallback parser for when pyyaml is absent —
``anvil/lib/project_detect.py`` and
``anvil/skills/rubric-rebackport/lib/detect.py`` — those have a
materially different contract and stay separate. It also does not touch
``anvil/lib/marp_lint.py``'s same-named helper, which returns the raw
frontmatter *string* (for CSS-class scanning), not a parsed dict.

Convention parsed: optional UTF-8 BOM strip, skip leading blank lines,
require an opening ``---`` delimiter, find the matching closing ``---``,
``yaml.safe_load`` the body, require the parsed result to be a ``dict``.
"""

from __future__ import annotations

from typing import Optional

import yaml

FRONTMATTER_DELIM = "---"
"""The frontmatter delimiter line, compared after ``.strip()``."""


def extract_frontmatter(text: str) -> Optional[dict]:
    """Extract the YAML frontmatter from ``text`` and return it as a dict.

    Returns ``None`` when the text has no frontmatter, the frontmatter is
    malformed, or the parsed value isn't a dict. Intentionally
    **tolerant** — every consumer of this helper treats an unparseable or
    absent frontmatter block as "not present" rather than raising.
    """
    # The opener must be the first non-empty line. Leading blank lines
    # and BOM are tolerated, mirroring how most frontmatter consumers
    # (pandoc, Jekyll, Marp) parse the marker.
    lines = text.splitlines()
    # Strip a leading UTF-8 BOM if present on the first line.
    if lines and lines[0].startswith("﻿"):
        lines[0] = lines[0][1:]

    # Find first non-empty line; must be the delimiter.
    first_idx = 0
    while first_idx < len(lines) and lines[first_idx].strip() == "":
        first_idx += 1
    if first_idx >= len(lines):
        return None
    if lines[first_idx].strip() != FRONTMATTER_DELIM:
        return None

    # Find the closing delimiter starting from the line after the opener.
    body_start = first_idx + 1
    close_idx = None
    for i in range(body_start, len(lines)):
        if lines[i].strip() == FRONTMATTER_DELIM:
            close_idx = i
            break
    if close_idx is None:
        return None

    yaml_text = "\n".join(lines[body_start:close_idx])
    try:
        parsed = yaml.safe_load(yaml_text)
    except yaml.YAMLError:
        return None
    if not isinstance(parsed, dict):
        return None
    return parsed


__all__ = ["FRONTMATTER_DELIM", "extract_frontmatter"]
