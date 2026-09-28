"""Canonical Python-side palette for Anvil figures.

This module is the **canonical Python definition** of the Anvil brand palette
for figures (matplotlib charts and, indirectly, mermaid diagrams). The named
constants below mirror, value-for-value, the CSS custom properties in the
deck theme's ``:root`` block:

    anvil/skills/deck/assets/anvil-deck.css   (the cross-format source of truth)

Keeping a single set of hex values across four file formats (a CSS file, a
matplotlib ``.mplstyle``, this Python module, and a mermaid JSON) is enforced
by a **drift-detection unit test**, not a code generator: ``tests/lib/
test_figures.py`` parses the hexes out of ``anvil-deck.css`` ``:root`` and
asserts these constants equal them. Any future palette drift between the CSS
chrome and the figures fails CI.

Two ways to use this module from a figure script:

1. **Defaults with zero effort** — call :func:`apply` to ``plt.style.use`` the
   shipped ``anvil.mplstyle``. The first series of any chart is then navy and
   the axes/text are the restrained brand greys, with no per-series color
   bookkeeping::

       from anvil.lib.figures.palette import apply
       apply()
       fig, ax = plt.subplots()
       ax.plot(x, y)          # navy by default

2. **Explicit per-series colors** — import the named constants when a chart
   needs to assign colors deliberately (a "hero" series in navy, a secondary
   series in muted grey, etc.)::

       from anvil.lib.figures.palette import ANVIL_NAVY, ANVIL_MUTED
       ax.bar(q, hero, color=ANVIL_NAVY)
       ax.bar(q, other, color=ANVIL_MUTED)

The constants are importable **without matplotlib installed** — only
:func:`apply` imports matplotlib (lazily, at call time), so a script that just
references ``ANVIL_NAVY`` does not pull a hard matplotlib dependency.
"""

from __future__ import annotations

from pathlib import Path


# --- Canonical brand palette -------------------------------------------------
# These mirror anvil/skills/deck/assets/anvil-deck.css :root, value for value.
# Drift between this module and that CSS is caught by tests/lib/test_figures.py.

ANVIL_NAVY = "#1f4e7a"
"""Deep navy accent (``--anvil-accent``). Primary/"hero" series color."""

ANVIL_INK = "#1a1a1a"
"""Near-black ink (``--anvil-text``). Axis labels, ticks, titles, annotations."""

ANVIL_MUTED = "#6b6b6b"
"""Muted grey (``--anvil-muted``). Secondary series, de-emphasized labels."""

# ``ANVIL_GREY`` is an alias for ``ANVIL_MUTED`` — both names appear in
# author-facing guidance (the issue references ``ANVIL_GREY``), so expose both
# pointing at the single canonical value.
ANVIL_GREY = ANVIL_MUTED

ANVIL_RULE = "#d6d6d6"
"""Light rule grey (``--anvil-rule``). Spines, gridlines, baselines."""

ANVIL_BG = "#ffffff"
"""White background (``--anvil-bg``). Default content-slide background."""

ANVIL_BG_SECTION = "#f5f5f5"
"""Section-slide background (``--anvil-bg-section``)."""

ANVIL_WARNING = "#b5651d"
"""Warm sienna warning accent (``--anvil-warning``).

Used by the ``anvil-warning`` mermaid classDef (shipped in
``mermaid-theme.json``'s ``themeCSS`` block) to semantically mark a diagram
node as "needs attention / rejected / failed / blocked". Dark enough that
white text remains legible at projector scale. Deliberately a warm rust
rather than the rose/crimson the design critic flagged across 12/12 decks.
"""

ANVIL_SUCCESS = "#2d5f3f"
"""Muted forest-green success accent (``--anvil-success``).

Used by the ``anvil-success`` mermaid classDef (shipped in
``mermaid-theme.json``'s ``themeCSS`` block) to semantically mark a diagram
node as "approved / complete / passed". Deep enough that white text remains
legible at projector scale; stays in the cool dark mid-tone range so it
coexists with the navy primary.
"""


# --- Multi-series ramp -------------------------------------------------------
# The CSS :root defines exactly ONE accent (navy) plus greys, so the
# multi-series prop_cycle is new design introduced with the figures package.
# It anchors on navy, keeps secondary = the existing --anvil-muted grey, and
# deliberately avoids the rose/crimson/magenta/gold that the design critic
# flagged across 12/12 decks. ``ANVIL_NAVY_TINT`` is a lighter navy tint
# (tertiary) that stays inside the restrained brand.

ANVIL_NAVY_TINT = "#5b82a6"
"""Lighter navy tint. Tertiary series color in the ramp."""

ANVIL_RAMP = (ANVIL_NAVY, ANVIL_MUTED, ANVIL_NAVY_TINT, ANVIL_RULE)
"""Navy-anchored series ramp: navy -> muted slate -> navy tint -> rule grey.

This is the source for the ``axes.prop_cycle`` in ``anvil.mplstyle`` (which
must list the same colors, navy first) and the secondary/tertiary constants
authors reference for explicit per-series colors.
"""


# Path to the shipped declarative matplotlib style, resolved relative to THIS
# module so ``apply()`` works regardless of the working directory the figure
# script is invoked from (deck-figures runs scripts from varied CWDs).
MPLSTYLE_PATH = Path(__file__).resolve().parent / "anvil.mplstyle"


def apply() -> None:
    """Apply the shipped Anvil matplotlib style to the global ``rcParams``.

    Equivalent to ``matplotlib.pyplot.style.use(MPLSTYLE_PATH)``. Call this
    once near the top of a figure script to get on-brand defaults (navy-first
    ``prop_cycle``, Helvetica-family font, ink/rule axis colors, 200-DPI
    transparent ``savefig``, 12x7 figure size) with no per-series effort.

    matplotlib is imported lazily here so that the named color constants above
    remain importable in environments without matplotlib installed.

    Raises:
        ImportError: if matplotlib is not installed (only when ``apply`` is
            actually called — importing the constants never triggers this).
    """
    import matplotlib.pyplot as plt

    plt.style.use(str(MPLSTYLE_PATH))
