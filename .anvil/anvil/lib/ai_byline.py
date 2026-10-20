"""Opt-in AI-authorship byline renderer (issue #941).

The problem
-----------

Frontier model output now carries an intrinsic, server-side statistical
watermark (green-list logit bias) that targets the *adversarial* case —
someone passing AI text off as human. That mechanism is out of a
consumer's hands and says nothing about a different, honest-actor
problem: a self-publisher who *wants* to disclose AI-assisted authorship
on their own terms, as an editorial choice, for brand transparency or
provenance for downstream readers.

This module renders that disclosure line. It is deliberately small and
detachable — **not** a watermark, **not** tamper-resistant, and **not**
on by default. See ``anvil/lib/snippets/provenance.md`` for how this
relates to (and is distinct from) the corpus claim-provenance tier
(#597) and the intrinsic model-output watermark.

Activation
----------

The line only ever appears when a project's ``BRIEF.md`` declares a
top-level ``ai_byline:`` block with ``enabled: true`` — see
:class:`anvil.lib.project_brief.AiByline` for the schema and
:func:`anvil.lib.project_brief.resolve_ai_byline` for the
BRIEF → rendered-string resolution. This module owns only the pure
string-rendering half: given the (already-parsed) configured text /
model name / date, produce the line consumer commands splice into a
rendered artifact.

Custom text templating
-----------------------

A consumer-declared ``text:`` override may embed the literal
placeholders ``{model}`` and ``{date}``, substituted with
``model_name`` / ``date`` when supplied (empty string when not — never
raises on a missing placeholder value, and never raises on an unused
placeholder value). Plain ``str.replace`` substitution, not
``str.format`` — a byline is free-form prose that may itself contain
brace characters unrelated to templating (e.g. a citation), and
``str.replace`` never raises on those.
"""

from __future__ import annotations

__all__ = [
    "DEFAULT_PLACEMENT",
    "DEFAULT_TEXT",
    "VALID_PLACEMENTS",
    "render_byline",
    "render_byline_markdown",
]

#: The default line used when a project declares ``ai_byline: {enabled:
#: true}`` with no ``text:`` override. Deliberately generic — it names
#: no specific model/tool by default (that is what ``{model}`` is for).
DEFAULT_TEXT = "Drafted with AI assistance and reviewed by a human editor."

#: Recognized ``placement:`` values (see ``AiByline.placement``).
VALID_PLACEMENTS = ("byline", "footer", "frontmatter-only")

#: Default placement when the block is active but declares no
#: ``placement:`` — nearest the title, matching the "byline" name.
DEFAULT_PLACEMENT = "byline"


def render_byline(
    *,
    text: str | None = None,
    model_name: str | None = None,
    date: str | None = None,
) -> str:
    """Render the AI-authorship byline text.

    Parameters
    ----------
    text
        The consumer's ``ai_byline.text`` override, if declared. May
        embed ``{model}`` / ``{date}`` placeholders. ``None`` or an
        empty/whitespace-only string falls back to :data:`DEFAULT_TEXT`.
    model_name
        Optional model/tool name (e.g. ``"Claude"``) substituted for a
        ``{model}`` placeholder in ``text``. Ignored by
        :data:`DEFAULT_TEXT`, which never references ``{model}``.
    date
        Optional date string substituted for a ``{date}`` placeholder in
        ``text``. Same ignore-when-unused behavior as ``model_name``.

    Returns
    -------
    str
        The rendered line, stripped of leading/trailing whitespace.
        Deterministic given fixed inputs — no clock reads, no I/O.

    Notes
    -----
    A placeholder with no substitution value supplied is replaced with
    the empty string (never raises, never leaves a literal ``{model}``
    in the output) — e.g. ``text="Drafted with {model} assistance."``
    with ``model_name=None`` renders as ``"Drafted with  assistance."``
    collapsed to single spaces by the final whitespace normalization.
    """
    template = text.strip() if text and text.strip() else DEFAULT_TEXT
    rendered = template.replace("{model}", model_name or "").replace(
        "{date}", date or ""
    )
    # Collapse any run of whitespace left behind by an empty placeholder
    # substitution (e.g. "with  assistance" -> "with assistance") without
    # touching intentional formatting elsewhere in a custom template.
    rendered = " ".join(rendered.split())
    return rendered


def render_byline_markdown(rendered_text: str) -> str:
    """Wrap an already-rendered byline string in the markdown convention
    used at injection sites: an italicized, single-line paragraph.

    Kept as a thin, separate helper (rather than baked into
    :func:`render_byline`) so a rendered-PDF consumer (e.g. ``report``,
    via a pandoc ``--include-after-body`` snippet) can reuse the same
    markdown wrapping a markdown-native consumer (``essay``) applies
    directly to its body.
    """
    return f"*{rendered_text}*"
