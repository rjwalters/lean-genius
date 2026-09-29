"""Shared on-brand figure styling for Anvil skills.

This package is the ``anvil/lib/``-level home for the figure-theming primitive
that keeps matplotlib charts AND mermaid diagrams on the deck brand palette
(navy ``#1f4e7a`` + restrained greys + Helvetica) by default — instead of each
figure author hand-matching hex values to the CSS theme.

Ships three assets plus the canonical Python palette:

- ``palette.py`` — canonical Python palette constants (``ANVIL_NAVY`` etc.) and
  :func:`apply`, which ``plt.style.use``-es the shipped ``anvil.mplstyle``.
- ``anvil.mplstyle`` — declarative matplotlib defaults (navy-first
  ``prop_cycle``, Helvetica font, ink/rule colors, 200-DPI transparent
  ``savefig``, 12x7 figure size).
- ``mermaid-theme.json`` — mermaid ``theme: base`` + navy ``themeVariables``,
  passed to ``mmdc`` via ``-c``.

The single-source-of-truth contract: ``anvil/skills/deck/assets/anvil-deck.css``
``:root`` is the cross-format source of truth; ``palette.py`` is the canonical
Python mirror; the ``.mplstyle`` and ``.json`` carry sync-header notes. Drift is
enforced by ``tests/lib/test_figures.py``, not a code generator.

Lib-level so it can serve both ``anvil:deck`` and ``anvil:slides``; this issue
wires it into deck only (slides adoption is tracked separately).
"""

from anvil.lib.figures.palette import (
    ANVIL_BG,
    ANVIL_BG_SECTION,
    ANVIL_GREY,
    ANVIL_INK,
    ANVIL_MUTED,
    ANVIL_NAVY,
    ANVIL_NAVY_TINT,
    ANVIL_RAMP,
    ANVIL_RULE,
    ANVIL_SUCCESS,
    ANVIL_WARNING,
    MPLSTYLE_PATH,
    apply,
)


__all__ = [
    "ANVIL_BG",
    "ANVIL_BG_SECTION",
    "ANVIL_GREY",
    "ANVIL_INK",
    "ANVIL_MUTED",
    "ANVIL_NAVY",
    "ANVIL_NAVY_TINT",
    "ANVIL_RAMP",
    "ANVIL_RULE",
    "ANVIL_SUCCESS",
    "ANVIL_WARNING",
    "MPLSTYLE_PATH",
    "apply",
]
