"""Typed parser for the project-level ``BRIEF.md`` (issue #285).

Sub-deliverable 2 of #283 — the **typed schema reader** that the rubric
overlay selector (#286) and cross-thread reference validator (#287)
build on. Sub-deliverable 1 of #283 (the project-root *discovery*
primitive, #284 / PR #290) ships at
``anvil/skills/memo/lib/project_discovery.py``. Discovery answers "where
is the thread root and which project owns it?"; this module answers
"given a confirmed project root, what does the BRIEF say?".

Single source of truth (issue #296)
-----------------------------------
Issue #296 (the project-org model lock, part B) **retires** the
sibling ``.anvil.json`` file and consolidates every project / per-doc
anvil-config knob into ``BRIEF.md``'s YAML frontmatter. Specifically,
the BRIEF schema now absorbs:

- Per-doc ``target_length`` (already present; the per-version
  override surface ``target_length_overrides`` is new — see
  :class:`BriefDocument`).
- Per-doc ``rubric_overrides`` (calibration suffix per PR #265 —
  formerly the ``rubric_overrides`` block at the top level of
  ``<thread>/.anvil.json``; see :class:`RubricOverrides`).
- :func:`body_filename_for` — the issue #295 slug-echo helper.

The ``anvil_config`` module is gone. Lifecycle commands, lib modules,
and tests that previously read ``<thread>/.anvil.json`` now read
``<project>/BRIEF.md`` via :func:`load_project_brief` (or the strict
variant) and look up the per-doc entry by slug
(``ProjectBrief.document_for_slug(slug)``). The
``rubric_overrides_suffix.py`` module that wires per-dim calibration
into the reviewer continues to operate against a typed
:class:`RubricOverrides` instance — the only change is that the
instance is now sourced from BRIEF.md rather than ``.anvil.json``.

Background — why this exists
----------------------------
The Studio canary surfaced a **project-as-thread-root** layout where a
single project-level ``BRIEF.md`` lives at the project root and
enumerates per-document metadata in its YAML frontmatter::

    <project>/
      BRIEF.md                 ← single project brief; documents: list +
                                  per-doc target_length, target_length_overrides,
                                  and rubric_overrides
      <slug-a>/
        <slug-a>.1/ ...
      <slug-b>/
        <slug-b>.1/ ...
      research/                ← shared evidence pool (already shipped, #281)

The project BRIEF frontmatter shape::

    ---
    project: smart-actuators
    audience:
      - Acme internal leadership (primary)
      - VC investors (secondary)
    hard_rules:
      - Avoid speculative claims without an evidence anchor.
      - Cite every number; cite every claim with a defensible mechanism.
    documents:
      - slug: investment-memo
        artifact_type: investment-memo
        target_length: { words: [8000, 11000] }
        target_length_overrides:
          "1": [8000, 11000]
          "2": [7500, 10500]
        rubric_overrides:
          memo_subtype: synthesis-brief
          dim_1_calibration: "decision-framework — score on framework clarity"
          dim_5_calibration: "defers to underlying market models"
          target_length: { words: [9000, 13000] }
      - slug: latency-wall
        artifact_type: position-paper
        target_length: { words: [5000, 8000] }
    ---

    # Free-prose project shared context

This module reads that shape and surfaces it as a typed
:class:`ProjectBrief` with a per-document :class:`BriefDocument` list.

Public API
----------
``ArtifactType``
    Enum of registered artifact types. Unknown values raise a
    validation error listing the registered set — unless backed by a
    consumer overlay JSON (the #394 consumer extension tier; see
    "Artifact-type validation" below). Seed values per the curator's
    confirmation: ``investment-memo``, ``position-paper``,
    ``tactical-plan``, ``vision-document``, ``descriptive-thesis``.
    Issue #386 grew the set with skill-identity values ``deck``,
    ``slides``, ``proposal`` — for non-memo documents ``artifact_type``
    identifies which skill owns the thread rather than selecting a memo
    rubric overlay subtype. Issue #394 grew the memo-scoped subset with
    the canary-proven ``challenge-memo`` and ``strategy-memo`` genres.
    Issue #408 added the skill-identity value ``paper`` (registered as
    ``pub``, renamed under #694) (research-paper
    threads, the project-migrate BRIEF-synthesis registry gap).

``MEMO_ARTIFACT_TYPES``
    The memo-scoped subset of :class:`ArtifactType` — the registered
    values that select a shipped memo rubric overlay. Consumer-declared
    types (issue #394) are additionally memo-scoped by construction
    (their overlay JSONs live under the memo consumer registry).

``SKILL_IDENTITY_ARTIFACT_TYPES``
    The skill-identity subset of :class:`ArtifactType` (``deck`` /
    ``slides`` / ``proposal`` / ``paper``). Memo's overlay dispatch fails
    loudly for exactly this set (issue #386, re-keyed explicit under
    #394 so consumer-declared memo types don't trip the rejection).

``BriefDocument``
    Pydantic model for one entry in the ``documents:`` list. Carries
    ``slug``, ``artifact_type``, optional ``target_length``, optional
    ``target_length_overrides`` (per-version), and optional
    ``rubric_overrides`` (subtype calibration).

``TargetLengthRange``
    Word-count range. Used for both ``BriefDocument.target_length`` and
    the inner ``RubricOverrides.target_length``.

``TargetLengthOverrides``
    Per-version override map. Keys are version numbers (as strings:
    ``"1"``, ``"2"``, …); values are
    ``[min_words, max_words]`` ranges. Mirrors the historical
    ``.anvil.json`` ``target_length.overrides`` shape but lifted to the
    per-doc surface.

``RubricOverrides``
    Pydantic model holding the parsed per-doc ``rubric_overrides``
    block. Optional fields default to ``None`` so callers can check
    presence with ``is not None`` rather than a sentinel string.

``CalibrationOverride``
    Per-dimension override: holds the dimension number (1-9) and the
    calibration prose. Returned by ``RubricOverrides.calibrations``.

``WaiverOverride``
    Per-dimension waiver (issue #393): holds the dimension number (1-9)
    and the mandatory operator rationale (rationale-as-value on disk:
    ``dim_6_waiver: "<why>"``). Returned by ``RubricOverrides.waivers``.
    A waived dimension is removed from both the numerator and the
    denominator at verdict time; critical flags are NOT waivable.

``ProjectBrief``
    Pydantic model for the parsed BRIEF. Carries ``project``,
    ``audience``, ``hard_rules``, and ``documents``.

``load_project_brief(project_dir: Path) -> Optional[ProjectBrief]``
    Lenient loader. Returns ``None`` when ``<project_dir>/BRIEF.md``
    does not exist, has no YAML frontmatter, or its frontmatter is
    malformed. Raises ``ValueError`` for schema violations (the BRIEF
    is present but structurally wrong — a typo in ``artifact_type``,
    a duplicate slug, etc.).

``load_project_brief_strict(project_dir: Path) -> ProjectBrief``
    Strict loader. Raises ``FileNotFoundError`` when the BRIEF is
    missing, ``ValueError`` when frontmatter is missing or malformed,
    and propagates the same schema-violation ``ValueError`` as the
    lenient form.

``load_rubric_overrides_for_slug(project_dir: Path, slug: str) ->``
``RubricOverrides``
    Convenience wrapper: read the BRIEF, look up the document by
    ``slug``, and return its ``rubric_overrides`` block (or an empty
    :class:`RubricOverrides` when absent / malformed). This is the
    replacement for the retired
    ``anvil_config.load_rubric_overrides(thread_dir)`` API. The
    contract — empty instance on every absence path, never raise —
    mirrors the prior lenient form exactly.

``VoiceDocs`` / ``ResolvedVoiceDoc`` / ``resolve_voice_docs``
    The voice/persona grounding-docs contract (issue #461). The
    optional top-level ``voice:`` BRIEF block declares up to four
    voice artifacts (``style_guide`` / ``vocabulary`` / ``values`` /
    ``corpus`` glob); ``resolve_voice_docs(project_dir,
    consumer_root=None)`` resolves them project-root-first then
    consumer-root (never raising on absence — missing files come back
    as structured ``missing: true`` entries). Absent block →
    byte-identical behavior. See
    ``anvil/lib/snippets/voice_grounding.md`` for the drafter /
    reviewer role contracts.

``SubjectVoiceEntry`` / ``ResolvedSubjectVoice`` / ``resolve_subject_voice_docs``
    The **subject voice tier** (issue #598) — the parallel, independently
    activated tier for third-party dialogue grounded in a spoken corpus
    (interview transcripts) rather than the author's published prose. The
    optional ``voice.subjects`` list declares one entry per speaker
    (``name`` + ``corpus`` glob + optional ``voice_doc``);
    ``resolve_subject_voice_docs(project_dir, consumer_root=None)``
    resolves each with the same project-root-first, consumer-root-fallback
    walk and the same never-raise, structured ``missing: true`` posture.
    The subject tier and the author tier activate independently — a
    subjects-only block keeps ``VoiceDocs.is_empty == True``. See the
    ``voice_grounding.md`` §"Subject voice tier".

``body_filename_for(slug: str) -> str``
    Return the body markdown filename for a thread (``f"{slug}.md"``).
    Issue #295's slug-echo convention; the only recognized shape. Lives
    here because it's a one-line helper and ``project_brief.py`` is the
    project-config schema-of-record after the #296 consolidation.

Slug-directory divergence (Open Question #1 resolution)
-------------------------------------------------------
Both loaders accept an optional ``validate_dirs: bool = False`` flag. When
``True``, after parsing the BRIEF the loader walks ``<project_dir>`` for
slug-shaped subdirectories and applies the curator-confirmed asymmetric
rule:

- **Listed-but-missing** (BRIEF entry has no matching ``<project>/<slug>/``
  directory) → **warn but proceed**. A draft hasn't been started yet —
  common case. Surfaced via ``warnings.warn(UserWarning)``; the returned
  ``ProjectBrief`` is unchanged.
- **On-disk-but-unlisted** (``<project>/<slug>/`` exists with version
  dirs but no ``documents:`` entry names it) → **hard error**.
  Configuration drift — load-bearing. The reviewer can't pick a rubric
  overlay for a slug the BRIEF doesn't acknowledge. Raised as
  ``ValueError`` with the offending slug names.

When ``validate_dirs=False`` (default) the divergence check is skipped
entirely. Lifecycle commands that already know which slug they're
operating on (e.g., the reviewer with a thread root in hand) can opt into
the check; pure parser consumers don't need to.

Artifact-type validation (Open Question #5 resolution; two-tier per #394)
-------------------------------------------------------------------------
**Closed-ended with a consumer extension tier.** Unknown
``artifact_type`` values raise a clear ``ValueError`` listing the
registered set (and any discovered consumer-declared types). This
prevents typos silently degrading to no-overlay behavior. The
registered values are :data:`REGISTERED_ARTIFACT_TYPES`. Two kinds of
registered value coexist (#386):

- **Memo overlay subtypes** (the seven memo-scoped values): adding one
  requires a code change here, membership in
  :data:`MEMO_ARTIFACT_TYPES`, AND a matching overlay JSON in the memo
  skill's ``rubric_overlays/`` registry (#286).
- **Skill-identity values** (``deck``, ``slides``, ``proposal`` —
  enumerated in :data:`SKILL_IDENTITY_ARTIFACT_TYPES`): identify which
  non-memo skill owns the thread. Adding one requires a code change
  here plus SKILL.md documentation in the owning skill — and it must be
  left OUT of :data:`MEMO_ARTIFACT_TYPES` (no memo overlay JSON; memo
  commands fail loudly on these types).

Issue #394 adds a **second validation tier**: an unregistered
``artifact_type`` is accepted IFF a consumer overlay JSON exists at
``<consumer>/.anvil/skills/memo/rubric_overlays/<type>.json``, where
``<consumer>`` is the directory carrying the ``.anvil/`` install marker
(located via :func:`anvil.lib.theme.find_consumer_root`, the same walk
the theme catalog and the paper skill's consumer venue-rubric tier use).
This lets a consumer register memo genres without a framework PR while
keeping the enum honest — an unknown type with NO consumer overlay
still fails loudly at parse time. Consumer-declared values are carried
as validated plain ``str`` on :class:`BriefDocument` (str-enum members
and plain strings interoperate for equality, hashing, and frozenset
membership, so downstream ``in MEMO_ARTIFACT_TYPES`` checks keep
working). The loaders compute the consumer-types set once per parse;
an explicit ``consumer_root`` parameter override keeps the parser
testable from tmp dirs (source-tree runs without a ``.anvil/`` ancestor
simply skip the consumer tier).

Validation discipline — BRIEF-side is STRICT
--------------------------------------------
The BRIEF parser is intentionally STRICT on schema violations (raises
``ValueError`` with field path + suggested fix). Per-doc metadata is
load-bearing for overlay selection in #286, so a malformed entry must
fail loudly rather than degrading silently. This is the opposite of the
prior ``anvil_config.py`` ``rubric_overrides`` loader, which was
**lenient** (warned + dropped fields) because ``.anvil.json`` was
optional config and the lenient form preserved zero-impact backwards
compat for threads without overrides.

The consolidation under #296 keeps both contracts intact by routing them
to two different entry points:

- :func:`load_project_brief` (and strict variant): full BRIEF parser,
  STRICT on every field.
- :func:`load_rubric_overrides_for_slug`: convenience wrapper, returns
  an empty :class:`RubricOverrides` on every absence path (missing
  BRIEF, missing document, missing ``rubric_overrides`` block).
  Mirrors the prior lenient ``anvil_config.load_rubric_overrides``
  surface exactly.

No new Python deps
------------------
YAML frontmatter parsing uses ``yaml.safe_load`` (``pyyaml`` is a declared
base dep — fix #268). Validation uses ``pydantic`` (declared base dep). No
new dependencies are introduced.

Skill-local first
-----------------
Lives under ``anvil/skills/memo/lib/`` per the CLAUDE.md "skill-local
first, lib promotion later" pattern. Promotion to ``anvil/lib/`` is queued
for the second-consumer trigger (likely ``anvil:proposal`` if it adopts
the project-BRIEF shape, or ``anvil:paper``).

Relationship to ``project_discovery.py``
----------------------------------------
The discovery primitive (#284) hands back a ``DiscoveryResult`` whose
``project_root`` field is the directory this module's loaders take as
input. The shared on-disk constants — ``BRIEF_FILENAME`` and
``DOCUMENTS_FRONTMATTER_KEY`` — are re-imported from
``project_discovery`` so a rename there propagates here automatically.

Package split (issue #1121)
----------------------------
This module was a single 5,816-line file that grew incrementally,
issue-by-issue, along nine internally-commented section boundaries. Issue
#1121 splits it into a package along those same boundaries, purely for
maintainability — **no behavior change, no consumer import-line change**:

- ``types.py`` — :class:`ArtifactType` + the registered/memo/skill-identity
  type sets, the #394 consumer-overlay extension tier, and shared
  field-family constants.
- ``models.py`` — every typed model (:class:`ProjectBrief`,
  :class:`BriefDocument`, :class:`VoiceDocs`, :class:`RubricOverrides`, etc).
- ``fields.py`` — every ``_normalize_*`` / ``_validate_*`` frontmatter-field
  helper plus :func:`_normalize_documents`.
- ``loader.py`` — the slug-directory divergence validator and the
  lenient/strict parsing entry points (:func:`load_project_brief` /
  :func:`load_project_brief_strict` / :func:`load_rubric_overrides_for_slug`).
- ``refs.py`` — the spec_ref (#686) / code_ref (#697/#706) companion-input
  resolvers.
- ``voice.py`` — the voice/persona grounding-docs resolution (#461), subject
  voice tier (#598), AI-byline resolution (#941), and rhetoric-rules
  resolution (#468).
- ``thread.py`` — thread-level (not project-level) helpers: the
  ``recommendation_target`` reader (#348/#837), the ``pending_sources``
  companion knob (#842), and :func:`body_filename_for` (#295).

This ``__init__.py`` re-exports every name the pre-split module exposed —
both its ``__all__`` surface and the handful of non-``__all__`` names
(``BRIEF_FILENAME``, ``DOCUMENTS_FRONTMATTER_KEY``,
:class:`CompanionRefTypeError`, :class:`PendingSource`,
``_validate_pending_sources``) that existing call sites import directly —
so every existing ``from anvil.lib.project_brief import X`` across all 14
skills plus tests keeps working unchanged. The one internal-only change is
:data:`_RECOGNIZED_RECOMMENDATION_TARGETS`, relocated from the thread-level
section into ``types.py`` because it is consumed by both ``fields.py`` and
``thread.py``, which cannot import from each other without a cycle — see
``types.py`` for detail. See ``anvil/lib/project_brief/*.py`` docstrings for
the per-module detail.
"""

from __future__ import annotations

from anvil.lib.project_brief.fields import CompanionRefTypeError as CompanionRefTypeError
from anvil.lib.project_brief.loader import (
    load_project_brief,
    load_project_brief_strict,
    load_rubric_overrides_for_slug,
)
from anvil.lib.project_brief.models import (
    AiByline,
    BriefDocument,
    CalibrationOverride,
    ProjectBrief,
    ResolvedCorpusDir,
    ResolvedSubjectVoice,
    ResolvedVoiceDoc,
    RubricOverrides,
    SubjectVoiceEntry,
    TargetLengthOverrides,
    TargetLengthRange,
    VoiceDocs,
    WaiverOverride,
)
from anvil.lib.project_brief.refs import (
    ResolvedCodeRef,
    ResolvedSpecRef,
    resolve_code_ref,
    resolve_spec_ref,
)
from anvil.lib.project_brief.thread import (
    PendingSource,
    PendingSourcesTypeError,
    body_filename_for,
    load_recommendation_target,
    load_recommendation_target_resolved,
    resolve_pending_sources,
)
from anvil.lib.project_brief.thread import (
    _validate_pending_sources as _validate_pending_sources,
)
from anvil.lib.project_brief.types import (
    ArtifactType,
    CONSUMER_MEMO_OVERLAYS_RELPATH,
    DEFAULT_MAX_ITERATIONS,
    MAX_DIM,
    MEMO_ARTIFACT_TYPES,
    MIN_DIM,
    REGISTERED_ARTIFACT_TYPES,
    SKILL_IDENTITY_ARTIFACT_TYPES,
    VOICE_DOC_KINDS,
    consumer_overlay_dir_for,
    discover_consumer_artifact_types,
)
from anvil.lib.project_brief.voice import (
    ResolvedAiByline,
    resolve_ai_byline,
    resolve_corpus_dirs,
    resolve_rhetoric_rules,
    resolve_subject_voice_docs,
    resolve_voice_docs,
)

# Re-exported unchanged from ``anvil.lib.project_discovery`` — historically
# importable from this module's top level (not just via ``loader.py``'s
# internal use), e.g. ``from anvil.lib.project_brief import BRIEF_FILENAME``.
from anvil.lib.project_discovery import BRIEF_FILENAME as BRIEF_FILENAME
from anvil.lib.project_discovery import (
    DOCUMENTS_FRONTMATTER_KEY as DOCUMENTS_FRONTMATTER_KEY,
)

__all__ = [
    "AiByline",
    "ArtifactType",
    "BriefDocument",
    "CONSUMER_MEMO_OVERLAYS_RELPATH",
    "CalibrationOverride",
    "DEFAULT_MAX_ITERATIONS",
    "MAX_DIM",
    "MEMO_ARTIFACT_TYPES",
    "MIN_DIM",
    "PendingSource",
    "PendingSourcesTypeError",
    "ProjectBrief",
    "REGISTERED_ARTIFACT_TYPES",
    "ResolvedAiByline",
    "ResolvedCodeRef",
    "ResolvedCorpusDir",
    "ResolvedSpecRef",
    "ResolvedSubjectVoice",
    "ResolvedVoiceDoc",
    "RubricOverrides",
    "SKILL_IDENTITY_ARTIFACT_TYPES",
    "SubjectVoiceEntry",
    "TargetLengthOverrides",
    "TargetLengthRange",
    "VOICE_DOC_KINDS",
    "VoiceDocs",
    "WaiverOverride",
    "body_filename_for",
    "consumer_overlay_dir_for",
    "discover_consumer_artifact_types",
    "load_project_brief",
    "load_project_brief_strict",
    "load_recommendation_target",
    "load_recommendation_target_resolved",
    "load_rubric_overrides_for_slug",
    "resolve_ai_byline",
    "resolve_code_ref",
    "resolve_corpus_dirs",
    "resolve_pending_sources",
    "resolve_rhetoric_rules",
    "resolve_spec_ref",
    "resolve_subject_voice_docs",
    "resolve_voice_docs",
]
