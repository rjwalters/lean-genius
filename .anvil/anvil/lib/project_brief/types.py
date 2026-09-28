"""Artifact-type registry + shared field-family constants (issue #1121 split).

Part of the ``anvil.lib.project_brief`` package — see the package
``__init__.py`` docstring for the full module. This submodule owns:

- :class:`ArtifactType` and the registered/memo/skill-identity type sets.
- The issue #394 consumer artifact-type extension tier
  (:func:`consumer_overlay_dir_for` / :func:`discover_consumer_artifact_types`).
- Shared field-family constants (rubric dimension bounds, recognized
  frontmatter key sets, default iteration cap, valid render engines, voice
  doc kinds) consumed by ``models.py`` and ``fields.py``.

Split from the pre-#1121 monolithic ``anvil/lib/project_brief.py`` along its
existing "Consumer artifact-type extension tier" / constants section
boundary. No behavior change — see ``__init__.py`` for the split rationale.
"""

from __future__ import annotations

import re
from enum import Enum
from pathlib import Path
from typing import Dict, Optional, Tuple

from anvil.lib.theme import find_consumer_root

# The registered artifact types. The first seven are memo subtypes
# (five seeds per the curator's confirmation comment on #283, plus the
# canary-proven challenge-memo / strategy-memo registered under #394);
# the rest are skill-identity values — deck / slides / proposal
# added under #386, paper added under #408 (a paper-class LaTeX paper
# thread in a shared project BRIEF previously had NO registered type,
# so project-migrate's BRIEF synthesis silently defaulted a research
# paper to 'investment-memo'), report added under #432 (the vN
# report-dir adoption mode's inferred type), and ip-uspto /
# ip-uspto-provisional added under #440 (letter-family adoption's
# REQUIRED `--artifact-type` values — strict post-write BRIEF
# validation would otherwise roll back every adopted write), and
# essay added under #460 (the `anvil:essay` artifact class), and
# datasheet added under #486 (the `anvil:datasheet` artifact class —
# shipped #418/#421 before this registry pattern was consistently
# applied; backfilled so a validated BRIEF can carry the type and
# rubric-rebackport's BRIEF-route inference reaches the datasheet
# rubric row). Unknown
# values are rejected with a clear error listing this set UNLESS a
# consumer overlay JSON backs them (the #394 consumer extension tier —
# see `discover_consumer_artifact_types` below).
#
# Registering a new MEMO subtype upstream requires:
#   1. Adding the literal here (and to MEMO_ARTIFACT_TYPES below).
#   2. Landing a matching overlay file (sub-deliverable 3 / #286).
#   3. Documenting the new shape in `anvil/skills/memo/SKILL.md`.
# A consumer can instead declare a type with NO framework release by
# shipping `<consumer>/.anvil/skills/memo/rubric_overlays/<type>.json`.
#
# Registering a new SKILL-IDENTITY value requires:
#   1. Adding the literal here AND to SKILL_IDENTITY_ARTIFACT_TYPES
#      below (NOT to MEMO_ARTIFACT_TYPES — no memo overlay JSON; memo
#      commands fail loudly on non-memo types).
#   2. Documenting it in the owning skill's SKILL.md.
# Legacy input aliases for renamed artifact types (issue #694). Keyed by
# the OLD string a consumer BRIEF may still carry; the value is the
# CANONICAL enum member the parser normalizes to. This keeps existing
# consumer BRIEFs (authored before a rename) parsing without a manual
# edit, while the parser emits the canonical typed member going forward.
#
# `pub` → `paper`: the `anvil:pub` skill was renamed to `anvil:paper`
# under #694 (hard rename, no skill-level forwarding alias). A consumer
# BRIEF with `artifact_type: pub` still parses and normalizes to
# `ArtifactType.PAPER`. This alias is INPUT-ONLY: nothing emits `"pub"`.
_ARTIFACT_TYPE_INPUT_ALIASES: Dict[str, "ArtifactType"] = {}


REGISTERED_ARTIFACT_TYPES: Tuple[str, ...] = (
    "investment-memo",
    "position-paper",
    "tactical-plan",
    "vision-document",
    "descriptive-thesis",
    "challenge-memo",
    "strategy-memo",
    "deck",
    "slides",
    "proposal",
    "paper",
    "report",
    "ip-uspto",
    "ip-uspto-provisional",
    "essay",
    "datasheet",
    "primer",
    "spec",
    "memoir",
)


class ArtifactType(str, Enum):
    """Closed-ended enum of registered artifact types.

    Inheriting from ``str`` lets a ``BriefDocument.artifact_type`` value
    serialize round-trip through JSON / YAML without a custom encoder.
    Unknown values raise ``ValueError`` at parse time — see the
    ``_validate_artifact_type`` helper for the diagnostic shape.

    Members
    -------
    INVESTMENT_MEMO
        The default memo shape. Calibrated for ranked-recommendation
        invest / pass / conditional decisions with a check size.
    POSITION_PAPER
        Argumentative case for a specific viewpoint (e.g., the canary's
        "latency wall" thesis).
    TACTICAL_PLAN
        Execution plan with prioritized actions and ownership.
    VISION_DOCUMENT
        Long-horizon technical or strategic vision.
    DESCRIPTIVE_THESIS
        Descriptive case for a team / market / shape (e.g., the canary's
        "team thesis").
    CHALLENGE_MEMO
        Tests a NAMED positioning thesis against evidence and delivers
        a verdict on the test (holds / breaks / holds-with-amendments)
        rather than an invest / pass / check-size decision. Registered
        under #394 from the canary's ``broadcom-thesis`` /
        ``sensor-stack`` threads.
    STRATEGY_MEMO
        Internal playbook (e.g., a fundraising strategy): the
        recommendation is the actionability of the play; financial
        scoring targets the soundness of the anchors the play leans on
        rather than venture-style unit economics. Registered under
        #394 from the canary's ``fundraising-strategy`` thread.
    DECK
        Skill-identity value (#386): an ``anvil:deck`` pitch-deck thread.
        Not a memo subtype — selects no memo rubric overlay.
    SLIDES
        Skill-identity value (#386): an ``anvil:slides`` talk-deck
        thread. Not a memo subtype — selects no memo rubric overlay.
    PROPOSAL
        Skill-identity value (#386): an ``anvil:proposal`` LaTeX
        customer-proposal thread. Not a memo subtype — selects no memo
        rubric overlay.
    PAPER
        Skill-identity value (#408; skill renamed ``pub`` → ``paper``
        under #694): an ``anvil:paper`` LaTeX research-paper thread. Not
        a memo subtype — selects no memo rubric overlay. Registered so
        project-migrate's BRIEF synthesis can name paper-class
        ``.tex``-bodied threads instead of silently defaulting them to
        ``investment-memo``. The legacy string ``pub`` is accepted as an
        input alias (see ``_ARTIFACT_TYPE_INPUT_ALIASES``) so pre-rename
        consumer BRIEFs keep parsing.
    REPORT
        Skill-identity value (#432): an ``anvil:report`` technical /
        customer-facing report thread. Not a memo subtype — selects no
        memo rubric overlay. Registered so project-migrate's vN
        report-dir adoption (``--adopt-vn``) can name the adopted
        thread's owning skill instead of silently defaulting to
        ``investment-memo`` (the same registry-gap shape #408 closed
        for ``paper``).
    IP_USPTO
        Skill-identity value (#440): an ``anvil:ip-uspto`` USPTO
        non-provisional patent-application thread. Not a memo subtype —
        selects no memo rubric overlay. Registered so project-migrate's
        letter-family adoption (``--adopt-family``) can record the
        operator's REQUIRED ``--artifact-type`` choice and survive
        strict post-write BRIEF validation (the #432 ``report``
        precedent).
    IP_USPTO_PROVISIONAL
        Skill-identity value (#440): an ``anvil:ip-uspto-provisional``
        USPTO provisional-application thread (claims-optional,
        enablement-depth-first — the conversion seed for
        ``anvil:ip-uspto``). Not a memo subtype — selects no memo
        rubric overlay. Registered alongside ``ip-uspto`` because
        there is no safe inference between a full application and a
        provisional — ``--adopt-family`` REQUIRES the operator to name
        one explicitly.
    ESSAY
        Skill-identity value (#460): an ``anvil:essay`` short-form
        voice-grounded essay / blog-post thread (markdown-only body,
        READY-terminal with a consumer-native publish handoff). Not a
        memo subtype — selects no memo rubric overlay. Registered per
        the #439/#457 precedent so a shared project BRIEF can declare
        which skill owns an essay thread.
    DATASHEET
        Skill-identity value (#486): an ``anvil:datasheet`` customer-facing
        IC / component datasheet thread (LaTeX ``datasheet.tex`` body). Not
        a memo subtype — selects no memo rubric overlay. The skill shipped
        (#418/#421) before this registry pattern was consistently applied;
        registered here so a validated BRIEF can carry
        ``artifact_type: datasheet`` and rubric-rebackport's BRIEF-route
        inference (#484) resolves an unstamped datasheet review to the
        ``("datasheet", 44)`` KNOWN_RUBRICS row.
    PRIMER
        Skill-identity value (#686): an ``anvil:primer`` long-form
        pedagogical explainer thread (a teach-from-intuition companion to
        a formal spec; markdown source-of-truth with an optional PDF
        render). Not a memo subtype — selects no memo rubric overlay.
        Registered per the #386/#408/#432/#440/#460 precedent so a shared
        project BRIEF can declare which skill owns a primer thread, and so
        the optional ``spec_ref`` companion-input key parses under the
        STRICT unknown-key rejection.
    SPEC
        Skill-identity value (#697/#706): an ``anvil:spec`` normative
        technical-specification thread (a protocol/wire-format/consensus
        spec maintained truthfully against its implementation; LaTeX
        source-of-truth with an optional PDF render). Not a memo subtype —
        selects no memo rubric overlay. Registered per the
        #386/#408/#432/#440/#460/#686 precedent so a shared project BRIEF
        can declare which skill owns a spec thread, and so the optional
        ``code_ref`` companion-input key (the mirror image of primer's
        ``spec_ref`` — the implementation the spec normatively describes)
        parses under the STRICT unknown-key rejection.
    MEMOIR
        Skill-identity value (#740): an ``anvil:memoir`` chaptered
        narrative-nonfiction thread reconstructed from a private
        evidentiary corpus (family memoirs, oral histories,
        biography-from-archive). Not a memo subtype — selects no memo
        rubric overlay. Registered per the
        #386/#408/#432/#440/#460/#486/#686/#697 precedent so a shared
        project BRIEF can declare which skill owns a chapter thread. The
        already-general top-level ``corpus:`` (#597) and ``voice:``
        ``subjects:`` (#598) keys need no memoir-specific BRIEF grammar —
        both parse under the STRICT unknown-key rejection today; this
        registration only adds the ``artifact_type: memoir`` value
        itself.
    """

    INVESTMENT_MEMO = "investment-memo"
    POSITION_PAPER = "position-paper"
    TACTICAL_PLAN = "tactical-plan"
    VISION_DOCUMENT = "vision-document"
    DESCRIPTIVE_THESIS = "descriptive-thesis"
    CHALLENGE_MEMO = "challenge-memo"
    STRATEGY_MEMO = "strategy-memo"
    DECK = "deck"
    SLIDES = "slides"
    PROPOSAL = "proposal"
    PAPER = "paper"
    REPORT = "report"
    IP_USPTO = "ip-uspto"
    IP_USPTO_PROVISIONAL = "ip-uspto-provisional"
    ESSAY = "essay"
    DATASHEET = "datasheet"
    PRIMER = "primer"
    SPEC = "spec"
    MEMOIR = "memoir"


# Populate the legacy input-alias map now that the enum exists (issue
# #694). See the map's definition above for the input-only contract.
_ARTIFACT_TYPE_INPUT_ALIASES["pub"] = ArtifactType.PAPER


# The memo-scoped subset of the registry: values that select a memo
# rubric overlay (one overlay JSON per member ships under
# `anvil/skills/memo/rubric_overlays/`). Skill-identity values (deck /
# slides / proposal / paper) are deliberately excluded — memo's overlay dispatch
# (`anvil/skills/memo/lib/rubric_overlays.py::select_overlay_for_thread`)
# raises a clear skill-mismatch error for them instead of silently
# scoring a non-memo artifact against the memo rubric (#386).
MEMO_ARTIFACT_TYPES: frozenset = frozenset(
    {
        ArtifactType.INVESTMENT_MEMO,
        ArtifactType.POSITION_PAPER,
        ArtifactType.TACTICAL_PLAN,
        ArtifactType.VISION_DOCUMENT,
        ArtifactType.DESCRIPTIVE_THESIS,
        ArtifactType.CHALLENGE_MEMO,
        ArtifactType.STRATEGY_MEMO,
    }
)


# The skill-identity subset of the registry (issue #386, made explicit
# under #394; ``paper`` (registered as ``pub`` under #408, renamed #694);
# ``report`` added under #432;
# ``ip-uspto`` / ``ip-uspto-provisional`` added under #440; ``essay``
# added under #460; ``datasheet`` added under #486; ``primer`` added
# under #686; ``spec`` added under #697/#706; ``memoir`` added under
# #740):
# values that name which
# NON-memo skill owns a thread in a
# shared project BRIEF. Memo's overlay dispatch
# (`anvil/skills/memo/lib/rubric_overlays.py::select_overlay_for_thread`)
# raises a clear skill-mismatch error for exactly this set. The guard
# is keyed on THIS explicit set rather than "everything outside
# MEMO_ARTIFACT_TYPES" so that consumer-declared memo types (the #394
# extension tier — plain strings outside the enum, backed by a consumer
# overlay JSON) do not trip the deck/slides/proposal rejection.
SKILL_IDENTITY_ARTIFACT_TYPES: frozenset = frozenset(
    {
        ArtifactType.DECK,
        ArtifactType.SLIDES,
        ArtifactType.PROPOSAL,
        ArtifactType.PAPER,
        ArtifactType.REPORT,
        ArtifactType.IP_USPTO,
        ArtifactType.IP_USPTO_PROVISIONAL,
        ArtifactType.ESSAY,
        ArtifactType.DATASHEET,
        ArtifactType.PRIMER,
        ArtifactType.SPEC,
        ArtifactType.MEMOIR,
    }
)


# ---------------------------------------------------------------------------
# Consumer artifact-type extension tier (issue #394)
# ---------------------------------------------------------------------------

# Relative path (under the consumer root) of the consumer-owned memo
# rubric-overlay registry. Mirrors the paper skill's consumer venue-rubric
# tier (`<consumer>/.anvil/skills/paper/rubrics/<venue>.yaml` — see
# `anvil/lib/rubric.py::discover_venue_rubric`).
CONSUMER_MEMO_OVERLAYS_RELPATH: str = ".anvil/skills/memo/rubric_overlays"


def consumer_overlay_dir_for(
    project_dir: Path, consumer_root: Optional[Path] = None
) -> Optional[Path]:
    """Return the consumer memo-overlay directory for ``project_dir``.

    Resolves the consumer root (the directory carrying the ``.anvil/``
    install marker) by walking upward from ``project_dir`` via
    :func:`anvil.lib.theme.find_consumer_root`, unless an explicit
    ``consumer_root`` override is supplied (test fixtures / callers
    that already know the root). Returns ``None`` when no consumer
    root exists — e.g., source-tree runs without a ``.anvil/``
    ancestor — in which case the #394 consumer tier is simply skipped.

    The returned path is NOT required to exist; callers check
    ``is_dir()`` / ``is_file()`` as appropriate.
    """
    root = (
        Path(consumer_root)
        if consumer_root is not None
        else find_consumer_root(Path(project_dir))
    )
    if root is None:
        return None
    return root / CONSUMER_MEMO_OVERLAYS_RELPATH


def discover_consumer_artifact_types(
    project_dir: Path, consumer_root: Optional[Path] = None
) -> frozenset:
    """Return the set of consumer-declared artifact types (issue #394).

    A consumer declares a memo artifact type — with no framework
    release — by shipping an overlay JSON at
    ``<consumer>/.anvil/skills/memo/rubric_overlays/<type>.json``. The
    declared type is the filename stem. Returns an empty frozenset when
    no consumer root or no overlay directory exists.

    Discovery is filename-only by design: strict parsing of the overlay
    content (schema, dim keys, filename↔declared-type consistency) is
    deferred to load time
    (``anvil/skills/memo/lib/rubric_overlays.py::load_overlay``), where
    a malformed file raises ``OverlayLoadError`` naming the path.
    """
    overlay_dir = consumer_overlay_dir_for(project_dir, consumer_root)
    if overlay_dir is None or not overlay_dir.is_dir():
        return frozenset()
    return frozenset(p.stem for p in overlay_dir.glob("*.json"))


# Words-per-page conversion factor. Mirrors the 600 wpm proxy
# documented in ``anvil/skills/memo/SKILL.md`` §"Length targets".
_WORDS_PER_PAGE = 600

# Artifact types for which a ``target_length: { slides: [min, max] }``
# unit is truthful (issue #742). A deck/slides thread is authored and
# reviewed in slide count, not words or pages — there is no
# words-per-page-style equivalence to convert through, so ``slides`` is
# a TERMINAL unit, never converted. Declaring ``slides`` on any other
# ``artifact_type`` is rejected at parse time (see
# ``_normalize_target_length_range``).
_SLIDES_UNIT_ARTIFACT_TYPES: frozenset = frozenset(
    {ArtifactType.DECK, ArtifactType.SLIDES}
)

# Rubric dimension range for the ``dim_N_calibration`` / ``dim_N_waiver``
# key families: the closed interval [1, 9]. Both shipped consumers (memo
# per ``anvil/skills/memo/rubric.md``, deck per
# ``anvil/skills/deck/rubric.md`` — the issue #393 second consumer) carry
# 9-dimension rubrics, so the range holds as-is. If a future consumer
# ships a rubric with a different dimension count, the range must be
# parameterized per artifact type.
MIN_DIM = 1
MAX_DIM = 9

# `dim_N_calibration` is a templated key; the regex below pins the shape.
_DIM_CALIBRATION_RE = re.compile(r"^dim_(\d+)_calibration$")

# `dim_N_waiver` is the operator-directed dimension-exclusion key family
# (issue #393). Rationale-as-value shape: the YAML value IS the mandatory
# non-empty rationale string (`dim_6_waiver: "<why this dim is excluded>"`).
_DIM_WAIVER_RE = re.compile(r"^dim_(\d+)_waiver$")

# Recognized top-level keys inside a ``rubric_overrides:`` block.
# Anything else is preserved verbatim under ``unknown_keys`` (forward-
# compat surface — a future-shipped ``memo_subtype`` enum or a
# "Concision Discipline" knob can land in BRIEF.md ahead of loader
# support without breaking existing consumers).
_KNOWN_RUBRIC_OVERRIDE_KEYS = {"memo_subtype", "target_length"}

# Recognized sub-keys inside the optional top-level ``voice:`` block
# (issue #461 — the voice/persona grounding-docs contract; see
# ``anvil/lib/snippets/voice_grounding.md``). ``rhetoric_rules`` (issue
# #468) is the companion rhetoric lint's consumer rule file (issue
# #463) — recognized here but lint-side only; it is NOT a grounding
# doc, never joins :data:`VOICE_DOC_KINDS`, and does not activate the
# voice-grounding tier (see :func:`resolve_rhetoric_rules`). Anything
# else is preserved verbatim under ``VoiceDocs.unknown_keys``
# (forward-compat surface — the same lenient-inner-block posture as
# ``rubric_overrides``).
_RECOGNIZED_VOICE_KEYS = {
    "style_guide",
    "vocabulary",
    "values",
    "corpus",
    "rhetoric_rules",
    "subjects",
}

# Recognized sub-keys inside the optional top-level ``ai_byline:`` block
# (issue #941 — the opt-in AI-authorship disclosure contract). Anything
# else is preserved verbatim under ``AiByline.unknown_keys`` (the same
# lenient-inner-block posture as ``_RECOGNIZED_VOICE_KEYS``).
_RECOGNIZED_AI_BYLINE_KEYS = {
    "enabled",
    "text",
    "placement",
    "model_name",
}

# Recognized sub-keys when the optional ``audience:`` block is written
# in the dict shape (issue #546 — the studio's canonical multi-thread
# BRIEF convention). The tuple order IS the precedence used when
# flattening the dict back into the on-the-wire ``List[str]`` shape:
# primary first, then secondary, then tertiary, then any unknown sub-
# keys in YAML insertion order. Mirrors the lenient-inner-block posture
# of ``_normalize_voice`` (forward-compat surface — unknown keys warn
# but do not raise, so studio drafters can add roles ahead of the
# parser learning them).
_RECOGNIZED_AUDIENCE_KEYS: Tuple[str, ...] = ("primary", "secondary", "tertiary")

# Load order for resolved voice docs (issue #461): values first (stances
# / anti-stances / standing), then register rules, then vocabulary
# guidance, then the published-exemplar corpus. Mirrors the consumer
# ground truth (rjwalters.info blog-review step 1 order).
VOICE_DOC_KINDS: Tuple[str, ...] = (
    "values",
    "style_guide",
    "vocabulary",
    "corpus",
)

# Recognized keys on a ``BriefDocument`` entry. Anything else is a
# schema violation (BRIEF-side is STRICT).
_RECOGNIZED_DOCUMENT_KEYS = {
    "slug",
    "artifact_type",
    "target_length",
    "target_length_overrides",
    "rubric_overrides",
    "render_engine",
    "render_template",
    "render_lua_filters",
    "render_metadata",
    "latex_header_includes",
    "max_iterations",
    "iteration_cap_rationale",
    "web_search",
    "spec_ref",
    "code_ref",
    "recommendation_target",
    "voice_corpus_exclude",
}

# Default iteration cap. The override floor mirrors the deck skill's
# precedent in ``anvil/skills/deck/SKILL.md`` §"Per-thread override
# contract": the cap is a discipline tool, an override may **raise** the
# cap but never **lower** it below the principled default. Set the
# floor in one place so deck and memo agree.
DEFAULT_MAX_ITERATIONS = 4

# Valid values for the ``render_engine`` per-doc knob (issue #320). The
# trio mirrors :data:`anvil.lib.render_gate.MEMO_ENGINE_*` and the
# ``_select_memo_engine`` priority order. The BRIEF parser enforces this
# closed set at parse time; the render-gate's ``_select_memo_engine``
# does the runtime fallthrough when the requested engine is not on PATH.
# Per the parallel issue #322 (theme system) and the scope split agreed
# at curation, **per-document `render_engine` wins**; the per-theme
# default is layered underneath by #322.
_VALID_RENDER_ENGINES = ("weasyprint", "xelatex", "wkhtmltopdf")


# Closed set of recognized ``recommendation_target`` values (issue #348).
# Lives here (rather than in ``thread.py``) because it is consumed by BOTH
# the per-document field validator (``fields.py::_validate_recommendation_target``)
# and the thread-level BRIEF.md reader (``thread.py::load_recommendation_target``)
# — a shared registry constant, split-package analog of the pre-#1121 single-
# file module's forward reference. The closed set is the contract: typos like
# ``Undecided`` (capitalized), ``tbd``, ``?``, ``maybe`` are NOT recognized and
# resolve to ``None`` (the reviewer falls back to the legacy dim 1 calibration
# — same behavior as a thread with no BRIEF). This prevents the structured-
# field surface from silently accepting noise.
_RECOGNIZED_RECOMMENDATION_TARGETS = ("invest", "pass", "conditional", "undecided")
