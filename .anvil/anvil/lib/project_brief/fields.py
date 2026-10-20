"""Per-field normalizers + validators for the BRIEF schema (issue #1121 split).

Part of the ``anvil.lib.project_brief`` package — see the package
``__init__.py`` docstring for the full module. This submodule owns every
``_normalize_*`` / ``_validate_*`` frontmatter-field helper, the
:class:`CompanionRefTypeError` diagnostic type, and :func:`_normalize_documents`
— the per-document assembly function that dispatches every field helper
below to build one :class:`~anvil.lib.project_brief.models.BriefDocument`.

Split from the pre-#1121 monolithic ``anvil/lib/project_brief.py`` along its
existing "Field normalizers" section boundary (the "YAML frontmatter
extraction" sub-heading that used to precede it was a stale historical note
about ``_extract_frontmatter``'s #1075 promotion to
``anvil/lib/frontmatter.py`` — dropped here as dead commentary, no code was
under it). No behavior change.
"""

from __future__ import annotations

import warnings
from pathlib import Path
from typing import Any, Dict, List, Literal, Optional, Union

from pydantic import ValidationError

from anvil.lib.ai_byline import DEFAULT_PLACEMENT as DEFAULT_AI_BYLINE_PLACEMENT
from anvil.lib.ai_byline import VALID_PLACEMENTS as VALID_AI_BYLINE_PLACEMENTS
from anvil.lib.project_brief.models import (
    AiByline,
    BriefDocument,
    CalibrationOverride,
    RubricOverrides,
    SubjectVoiceEntry,
    TargetLengthOverrides,
    TargetLengthRange,
    VoiceDocs,
    WaiverOverride,
)
from anvil.lib.project_brief.types import (
    ArtifactType,
    CONSUMER_MEMO_OVERLAYS_RELPATH,
    DEFAULT_MAX_ITERATIONS,
    MAX_DIM,
    MIN_DIM,
    REGISTERED_ARTIFACT_TYPES,
    _ARTIFACT_TYPE_INPUT_ALIASES,
    _DIM_CALIBRATION_RE,
    _DIM_WAIVER_RE,
    _RECOGNIZED_AI_BYLINE_KEYS,
    _RECOGNIZED_AUDIENCE_KEYS,
    _RECOGNIZED_DOCUMENT_KEYS,
    _RECOGNIZED_RECOMMENDATION_TARGETS,
    _RECOGNIZED_VOICE_KEYS,
    _SLIDES_UNIT_ARTIFACT_TYPES,
    _VALID_RENDER_ENGINES,
    _WORDS_PER_PAGE,
)

# ---------------------------------------------------------------------------
# Field normalizers
# ---------------------------------------------------------------------------


def _normalize_string_list(
    value: Any, field_name: str
) -> List[str]:
    """Normalize a list-of-strings frontmatter value.

    YAML's flow / block syntax both surface as Python lists when present.
    A missing key yields an empty list (the field is allowed to be
    empty per the schema). A non-list value raises ``ValueError`` with
    the field path.
    """
    if value is None:
        return []
    if not isinstance(value, list):
        raise ValueError(
            f"BRIEF.{field_name} must be a list of strings; got "
            f"{type(value).__name__} — suggested fix: write the value "
            f"as a YAML list (`- item` lines or `[item, item]`)."
        )
    out: List[str] = []
    for i, entry in enumerate(value):
        if not isinstance(entry, str):
            raise ValueError(
                f"BRIEF.{field_name}[{i}] must be a string; got "
                f"{type(entry).__name__}: {entry!r} — suggested fix: "
                f"quote the entry or remove the non-string value."
            )
        out.append(entry)
    return out


def _normalize_theme(value: Any) -> Optional[str]:
    """Normalize the optional ``theme:`` frontmatter key (issue #322).

    Returns ``None`` when the key is absent, an explicit ``null``, or an
    empty / whitespace-only string. A non-empty string is returned with
    surrounding whitespace stripped. Any other type raises
    ``ValueError`` — the field is strictly a string when present, to
    catch fat-finger errors (``theme: [foo]``, ``theme: 42``).
    """
    if value is None:
        return None
    if not isinstance(value, str):
        raise ValueError(
            f"BRIEF.theme must be a string when set; got "
            f"{type(value).__name__}: {value!r} — suggested fix: "
            f"quote the theme name (`theme: my-brand`) or remove the "
            f"key to fall through to framework defaults."
        )
    stripped = value.strip()
    if not stripped:
        return None
    return stripped


def _normalize_voice(value: Any) -> Optional[VoiceDocs]:
    """Normalize the optional top-level ``voice:`` block (issue #461).

    Returns ``None`` when the key is absent or an explicit ``null``.
    A mapping is normalized to a :class:`VoiceDocs`:

    - Recognized sub-keys (``style_guide`` / ``vocabulary`` /
      ``values`` / ``corpus`` / ``rhetoric_rules``) must be strings
      when present — non-string values raise ``ValueError`` with the
      field path (STRICT on recognized keys, catching fat-finger
      shapes like ``corpus: [a.md, b.md]``). Empty / whitespace-only
      strings normalize to ``None`` (same as ``theme``).
    - Unknown sub-keys are **preserved verbatim** under
      ``unknown_keys`` with a ``warnings.warn`` breadcrumb — the
      lenient inner-block posture of ``rubric_overrides``, kept here
      so forward-shipped sub-keys don't break this parser.

    Any non-mapping value raises ``ValueError`` — the block is
    strictly a mapping when present.
    """
    if value is None:
        return None
    if not isinstance(value, dict):
        raise ValueError(
            f"BRIEF.voice must be a mapping when set; got "
            f"{type(value).__name__}: {value!r} — suggested fix: use "
            f"the block shape with optional sub-keys "
            f"{sorted(_RECOGNIZED_VOICE_KEYS)} (see "
            f"anvil/lib/snippets/voice_grounding.md), or remove the "
            f"key for byte-identical no-voice behavior."
        )

    recognized: Dict[str, Optional[str]] = {}
    subjects: Optional[List[SubjectVoiceEntry]] = None
    unknown_keys: Dict[str, Any] = {}
    for key, raw in value.items():
        if key not in _RECOGNIZED_VOICE_KEYS:
            unknown_keys[key] = raw
            warnings.warn(
                f"BRIEF.voice.{key}: unknown sub-key — preserved "
                f"verbatim under unknown_keys (forward-compat); the "
                f"voice-grounding consumers will not act on it. "
                f"Recognized sub-keys: {sorted(_RECOGNIZED_VOICE_KEYS)}.",
                UserWarning,
                stacklevel=2,
            )
            continue
        if key == "subjects":
            # The one non-string recognized sub-key (issue #598): a list
            # of speaker entries, normalized by the dedicated helper.
            subjects = _normalize_subjects(raw)
            continue
        if raw is None:
            recognized[key] = None
            continue
        if not isinstance(raw, str):
            example = {
                "corpus": "writing-corpus/**/*.md",
                "rhetoric_rules": "rhetoric-rules.json",
            }.get(key, "VALUES.md")
            raise ValueError(
                f"BRIEF.voice.{key} must be a string path"
                f"{' / glob' if key == 'corpus' else ''} when set; got "
                f"{type(raw).__name__}: {raw!r} — suggested fix: quote "
                f"a single path (e.g. `{key}: {example}`) "
                f"or remove the sub-key."
            )
        stripped = raw.strip()
        recognized[key] = stripped if stripped else None

    return VoiceDocs(**recognized, subjects=subjects, unknown_keys=unknown_keys)


def _normalize_subjects(value: Any) -> Optional[List[SubjectVoiceEntry]]:
    """Normalize the optional ``voice.subjects`` list (issue #598).

    The subject voice tier: a list of speaker entries, each a mapping
    with a required ``name`` and ``corpus`` and an optional ``voice_doc``.
    STRICT on the recognized structural shape (a fat-fingered
    non-mapping entry or a missing / non-string required field raises
    ``ValueError`` with the offending index and field), mirroring the
    ``documents:`` list's strictness — a broken subject declaration is a
    schema error, not a silent drop.

    - ``None`` / absent → ``None`` (tier inactive).
    - Empty list (``subjects: []``) → ``None`` (treated as absent per the
      #598 contract — an empty list does not activate the tier).
    - Unknown sub-keys *inside* a subject entry are preserved-by-warning
      (the lenient inner-block posture of :func:`_normalize_voice`): they
      warn and are dropped, so a forward-shipped subject sub-key does not
      break this parser.
    - ``voice_doc`` is optional; a whitespace-only value normalizes to
      ``None`` (corpus alone activates the entry).
    """
    if value is None:
        return None
    if not isinstance(value, list):
        raise ValueError(
            f"BRIEF.voice.subjects must be a list of speaker mappings "
            f"when set; got {type(value).__name__}: {value!r} — suggested "
            f"fix: use the list shape (`- name: <speaker>` / `corpus: "
            f"<glob>` / optional `voice_doc: <path>`), or remove the "
            f"sub-key for byte-identical no-subject behavior."
        )

    _SUBJECT_KEYS = {"name", "corpus", "voice_doc"}
    entries: List[SubjectVoiceEntry] = []
    for idx, raw in enumerate(value):
        if not isinstance(raw, dict):
            raise ValueError(
                f"BRIEF.voice.subjects[{idx}] must be a mapping with "
                f"`name` and `corpus` (and optional `voice_doc`); got "
                f"{type(raw).__name__}: {raw!r}."
            )
        for req in ("name", "corpus"):
            val = raw.get(req)
            if not isinstance(val, str) or not val.strip():
                raise ValueError(
                    f"BRIEF.voice.subjects[{idx}].{req} is required and "
                    f"must be a non-empty string; got {val!r} — suggested "
                    f"fix: set `{req}:` to "
                    f"{'the speaker name' if req == 'name' else 'a transcript glob (e.g. transcripts/<speaker>/**/*.md)'}."
                )
        voice_doc_raw = raw.get("voice_doc")
        if voice_doc_raw is None:
            voice_doc: Optional[str] = None
        elif not isinstance(voice_doc_raw, str):
            raise ValueError(
                f"BRIEF.voice.subjects[{idx}].voice_doc must be a string "
                f"path when set; got {type(voice_doc_raw).__name__}: "
                f"{voice_doc_raw!r} — suggested fix: quote a single path "
                f"(e.g. `voice_doc: planning/{raw['name'].strip()}-voice.md`) "
                f"or remove the key (corpus alone activates the entry)."
            )
        else:
            stripped_vd = voice_doc_raw.strip()
            voice_doc = stripped_vd if stripped_vd else None

        for unknown in set(raw) - _SUBJECT_KEYS:
            warnings.warn(
                f"BRIEF.voice.subjects[{idx}].{unknown}: unknown sub-key "
                f"— ignored (forward-compat); recognized subject sub-keys "
                f"are {sorted(_SUBJECT_KEYS)}.",
                UserWarning,
                stacklevel=2,
            )

        entries.append(
            SubjectVoiceEntry(
                name=raw["name"].strip(),
                corpus=raw["corpus"].strip(),
                voice_doc=voice_doc,
            )
        )

    return entries or None


def _normalize_corpus_dirs(value: Any) -> Optional[List[str]]:
    """Normalize the optional top-level ``corpus:`` key (issue #597).

    The factual ground-truth corpus declaration — a list of read-only
    directory paths (interview transcripts, family letters, engagement
    notes). Distinct from ``voice.corpus`` (a single glob nested under
    ``voice:`` for author-persona published exemplars); this is a
    top-level list of directories for substance verification.

    Accepted shapes:

    - **Absent / ``null`` / empty list** → ``None`` (tier INACTIVE;
      byte-identical no-corpus behavior).
    - **A single string** (``corpus: transcripts/``) → normalized to a
      one-element list (``["transcripts/"]``), the fat-finger-friendly
      shorthand.
    - **A list of strings** (``corpus: [transcripts/, letters/]``) →
      returned in declared order. Whitespace-only entries are dropped;
      a list that reduces to empty normalizes to ``None``.

    A non-string list element raises ``ValueError`` with the field path
    (e.g. ``BRIEF.corpus[1]``) — STRICT on element type, catching
    fat-finger shapes like ``corpus: [transcripts/, {nested: x}]``. Any
    other non-list / non-string value (a mapping, a number) raises a
    ``ValueError`` naming the recognized shapes, mirroring the strict
    posture of the other typed BRIEF keys.
    """
    if value is None:
        return None
    if isinstance(value, str):
        stripped = value.strip()
        return [stripped] if stripped else None
    if not isinstance(value, list):
        raise ValueError(
            f"BRIEF.corpus must be a list of directory-path strings (or a "
            f"single string) when set; got {type(value).__name__}: "
            f"{value!r} — suggested fix: write the value as a YAML list "
            f"(`- transcripts/` lines or `[transcripts/, letters/]`), a "
            f"single quoted path, or remove the key for byte-identical "
            f"no-corpus behavior."
        )
    out: List[str] = []
    for i, entry in enumerate(value):
        if not isinstance(entry, str):
            raise ValueError(
                f"BRIEF.corpus[{i}] must be a string directory path; got "
                f"{type(entry).__name__}: {entry!r} — suggested fix: quote "
                f"the path or remove the non-string value."
            )
        stripped = entry.strip()
        if stripped:
            out.append(stripped)
    return out or None


def _normalize_ai_byline(value: Any) -> Optional[AiByline]:
    """Normalize the optional top-level ``ai_byline:`` block (issue #941).

    Returns ``None`` when the key is absent or an explicit ``null`` —
    the byte-identical inactive path (mirrors :func:`_normalize_voice`).
    A mapping is normalized to an :class:`AiByline`:

    - ``enabled`` must be a bool when present (STRICT — a fat-fingered
      ``enabled: "true"`` string is a schema error, not a silent
      no-op, since this is the field that gates whether anything is
      ever rendered). Absent ``enabled`` defaults to ``False``.
    - ``text`` / ``placement`` / ``model_name`` must be strings when
      present; empty/whitespace-only values normalize to ``None`` (same
      posture as the ``voice:`` sub-keys). ``placement`` is validated
      against :data:`anvil.lib.ai_byline.VALID_PLACEMENTS` — an
      unrecognized value raises (STRICT, catching a typo'd placement
      before it silently falls back to the default).
    - Unknown sub-keys are **preserved verbatim** under
      ``unknown_keys`` with a ``warnings.warn`` breadcrumb — the same
      lenient inner-block posture as ``rubric_overrides`` / ``voice``.

    Any non-mapping value raises ``ValueError`` — the block is strictly
    a mapping when present.
    """
    if value is None:
        return None
    if not isinstance(value, dict):
        raise ValueError(
            f"BRIEF.ai_byline must be a mapping when set; got "
            f"{type(value).__name__}: {value!r} — suggested fix: use "
            f"the block shape with optional sub-keys "
            f"{sorted(_RECOGNIZED_AI_BYLINE_KEYS)} (see "
            f"anvil/lib/ai_byline.py), or remove the key for "
            f"byte-identical no-byline behavior."
        )

    enabled = False
    text: Optional[str] = None
    placement: Optional[str] = None
    model_name: Optional[str] = None
    unknown_keys: Dict[str, Any] = {}

    for key, raw in value.items():
        if key not in _RECOGNIZED_AI_BYLINE_KEYS:
            unknown_keys[key] = raw
            warnings.warn(
                f"BRIEF.ai_byline.{key}: unknown sub-key — preserved "
                f"verbatim under unknown_keys (forward-compat); the "
                f"byline renderer will not act on it. Recognized "
                f"sub-keys: {sorted(_RECOGNIZED_AI_BYLINE_KEYS)}.",
                UserWarning,
                stacklevel=2,
            )
            continue
        if key == "enabled":
            if not isinstance(raw, bool):
                raise ValueError(
                    f"BRIEF.ai_byline.enabled must be a bool when set; "
                    f"got {type(raw).__name__}: {raw!r} — suggested "
                    f"fix: use `enabled: true` or `enabled: false` "
                    f"(unquoted YAML boolean)."
                )
            enabled = raw
            continue
        if raw is None:
            continue
        if not isinstance(raw, str):
            raise ValueError(
                f"BRIEF.ai_byline.{key} must be a string when set; got "
                f"{type(raw).__name__}: {raw!r} — suggested fix: quote "
                f"a single string value or remove the sub-key."
            )
        stripped = raw.strip()
        if not stripped:
            continue
        if key == "text":
            text = stripped
        elif key == "placement":
            if stripped not in VALID_AI_BYLINE_PLACEMENTS:
                raise ValueError(
                    f"BRIEF.ai_byline.placement must be one of "
                    f"{sorted(VALID_AI_BYLINE_PLACEMENTS)}; got "
                    f"{stripped!r} — suggested fix: use one of the "
                    f"recognized placements or remove the sub-key for "
                    f"the default ({DEFAULT_AI_BYLINE_PLACEMENT!r})."
                )
            placement = stripped
        elif key == "model_name":
            model_name = stripped

    return AiByline(
        enabled=enabled,
        text=text,
        placement=placement,
        model_name=model_name,
        unknown_keys=unknown_keys,
    )


def _normalize_audience(value: Any) -> List[str]:
    """Normalize the ``audience:`` frontmatter key (issues #285, #546).

    Accepts three shapes, normalizing all of them to the on-the-wire
    ``List[str]`` field shape so downstream consumers (which iterate /
    pass through as ``Iterable[str]``) are unaffected:

    - **Absent / None** → empty list. The field is optional per the
      schema.
    - **List of strings** → unchanged (legacy + canonical flat form;
      this is the back-compat path that keeps every existing BRIEF
      parsing identically).
    - **Dict mapping role → string-or-list-of-strings** → flattened in
      role-precedence order (``primary``, ``secondary``, ``tertiary``,
      then any unknown sub-keys in YAML insertion order). This is the
      studio's canonical multi-thread BRIEF convention (#546).

    Dict-shape values may be either a single string (one audience per
    role) or a list of strings (multiple audiences per role); a non-
    string entry — at the top level OR inside a per-role list — raises
    ``ValueError`` with the field path. Unknown sub-keys are preserved
    at the END of the flattened list and emit a ``warnings.warn``
    breadcrumb naming the recognized set (forward-compat surface,
    mirroring ``_normalize_voice``).

    The dict shape is a parser-only convenience: ``brief.audience``
    remains ``List[str]`` on the schema, and the load-bearing
    paired-override / documents-schema validation downstream of this
    helper still runs unchanged (the regression bug this helper fixes:
    drafters who wrote the dict shape were silently routing around the
    entire parser via the bare ``except`` in render_gate's theme
    discovery — see #546).
    """
    if value is None:
        return []
    if isinstance(value, list):
        # Back-compat path: delegate to the existing list normalizer
        # byte-for-byte so the flat-list contract is provably unchanged.
        return _normalize_string_list(value, "audience")
    if not isinstance(value, dict):
        raise ValueError(
            f"BRIEF.audience must be a list of strings or a mapping of "
            f"role → string/list (recognized roles: "
            f"{list(_RECOGNIZED_AUDIENCE_KEYS)}); got "
            f"{type(value).__name__}: {value!r} — suggested fix: write "
            f"the value as a YAML list (`- item` lines or "
            f"`[item, item]`) or as a mapping (`audience: {{primary: "
            f"\"...\", secondary: \"...\"}}`)."
        )

    # Split the dict into recognized-role entries (precedence-ordered)
    # and unknown-role entries (insertion-ordered). We materialize the
    # YAML insertion order from ``value.items()`` so unknown sub-keys
    # land deterministically at the tail of the flattened list.
    recognized_entries: Dict[str, Any] = {}
    unknown_entries: Dict[str, Any] = {}
    for key, raw in value.items():
        if key in _RECOGNIZED_AUDIENCE_KEYS:
            recognized_entries[key] = raw
        else:
            unknown_entries[key] = raw
            warnings.warn(
                f"BRIEF.audience.{key}: unknown sub-key — preserved "
                f"verbatim at the tail of the flattened audience list "
                f"(forward-compat). Recognized sub-keys (in precedence "
                f"order): {list(_RECOGNIZED_AUDIENCE_KEYS)}.",
                UserWarning,
                stacklevel=2,
            )

    def _coerce_role_value(role: str, raw: Any) -> List[str]:
        """Convert one role's right-hand side into a list of strings."""
        if isinstance(raw, str):
            return [raw]
        if isinstance(raw, list):
            out: List[str] = []
            for i, entry in enumerate(raw):
                if not isinstance(entry, str):
                    raise ValueError(
                        f"BRIEF.audience.{role}[{i}] must be a string; "
                        f"got {type(entry).__name__}: {entry!r} — "
                        f"suggested fix: quote the entry or remove the "
                        f"non-string value."
                    )
                out.append(entry)
            return out
        raise ValueError(
            f"BRIEF.audience.{role} must be a string or a list of "
            f"strings; got {type(raw).__name__}: {raw!r} — suggested "
            f"fix: write the value as a quoted string (one audience) "
            f"or a YAML list (multiple audiences per role)."
        )

    flattened: List[str] = []
    # Recognized keys in precedence order (NOT YAML insertion order).
    for role in _RECOGNIZED_AUDIENCE_KEYS:
        if role not in recognized_entries:
            continue
        flattened.extend(_coerce_role_value(role, recognized_entries[role]))
    # Unknown keys in YAML insertion order at the tail.
    for role, raw in unknown_entries.items():
        flattened.extend(_coerce_role_value(role, raw))
    return flattened


def _slides_unit_allowed(
    artifact_type: Optional[Union["ArtifactType", str]],
) -> bool:
    """Return whether ``target_length: { slides: [...] }`` is truthful.

    ``None`` (no artifact-type context available at the call site) fails
    closed — see :func:`_normalize_target_length_range`.
    """
    if artifact_type is None:
        return False
    return artifact_type in _SLIDES_UNIT_ARTIFACT_TYPES


def _normalize_target_length_range(
    raw: Any,
    field_path: str,
    *,
    artifact_type: Optional[Union["ArtifactType", str]] = None,
) -> TargetLengthRange:
    """Convert a raw ``{words: [...]}`` / ``{pages: [...]}`` to a typed range.

    Raises ``ValueError`` for any malformed shape — the BRIEF parser is
    STRICT (unlike the prior rubric_overrides loader, which warned).

    Accepts the **flat shape** only — ``{"words": [min, max]}``,
    ``{"pages": [min, max]}``, or (issue #742, ``deck`` / ``slides``
    ``artifact_type`` only) ``{"slides": [min, max]}``. Extended-shape
    keys (``default``, ``overrides``) are rejected explicitly — the
    per-version surface has moved to ``target_length_overrides`` per
    the #296 consolidation.

    Parameters
    ----------
    artifact_type
        The owning document entry's ``artifact_type``, when known.
        Gates the ``slides`` unit: it is only accepted when
        ``artifact_type`` is ``deck`` or ``slides`` (see
        :data:`_SLIDES_UNIT_ARTIFACT_TYPES`) — a slide deck is authored
        and reviewed in slide count, not words or pages, so the
        ``slides`` unit is rejected for every other artifact type
        (there is no truthful words/pages-equivalent for a deck).
        ``None`` (the default, used by callers with no artifact-type
        context, e.g. the ``rubric_overrides.target_length`` and
        ``target_length_overrides`` call sites) also rejects ``slides``
        — fail closed rather than silently accepting an unvalidated
        unit.
    """
    if not isinstance(raw, dict):
        shape_hint = "`{ words: [min, max] }` or `{ pages: [min, max] }`"
        if _slides_unit_allowed(artifact_type):
            shape_hint += " (or `{ slides: [min, max] }` for a deck/slides thread)"
        raise ValueError(
            f"BRIEF.{field_path} must be a dict; got "
            f"{type(raw).__name__} — suggested fix: use the shape "
            f"{shape_hint}."
        )

    # Reject extended-shape keys explicitly so a copy-paste from the
    # historical .anvil.json shape produces a clear error rather than
    # silent acceptance.
    forbidden = {"default", "overrides"} & set(raw.keys())
    if forbidden:
        raise ValueError(
            f"BRIEF.{field_path} does not accept extended-shape keys "
            f"{sorted(forbidden)} — per-doc target_length is flat "
            f'(`{{ words: [min, max] }}` or `{{ pages: [min, max] }}`); '
            f"per-version overrides live in `target_length_overrides:` "
            f"on the document entry."
        )

    has_words = "words" in raw
    has_pages = "pages" in raw
    has_slides = "slides" in raw

    declared_keys = [
        key
        for key, present in (("words", has_words), ("pages", has_pages), ("slides", has_slides))
        if present
    ]

    if len(declared_keys) > 1:
        raise ValueError(
            f"BRIEF.{field_path} has more than one of 'words' / 'pages' / "
            f"'slides' ({declared_keys}) — ambiguous shape; pick exactly "
            f"one key."
        )

    if not declared_keys:
        raise ValueError(
            f"BRIEF.{field_path} has none of 'words', 'pages', or "
            f"'slides' — suggested fix: add `words: [min, max]` or "
            f"`pages: [min, max]` (or, for a deck/slides thread, "
            f"`slides: [min, max]`)."
        )

    source_key = declared_keys[0]

    if source_key == "slides" and not _slides_unit_allowed(artifact_type):
        artifact_type_display = getattr(artifact_type, "value", artifact_type)
        raise ValueError(
            f"BRIEF.{field_path}.slides is only accepted when the "
            f"document's artifact_type is 'deck' or 'slides' (got "
            f"{artifact_type_display!r}) — a slide deck is "
            f"authored/reviewed in slide count, not words or pages, so "
            f"'slides' is not a truthful unit here. Suggested fix: use "
            f"`words: [min, max]` or `pages: [min, max]` instead."
        )

    range_value = raw[source_key]

    if not isinstance(range_value, list) or len(range_value) != 2:
        raise ValueError(
            f"BRIEF.{field_path}.{source_key} must be a 2-element list; "
            f"got {range_value!r} — suggested fix: write "
            f"`[{source_key}_min, {source_key}_max]`."
        )

    lo_raw, hi_raw = range_value
    # bool is a subclass of int; reject explicitly so True/False can't
    # masquerade as 1/0 in a length range.
    if (
        isinstance(lo_raw, bool)
        or isinstance(hi_raw, bool)
        or not isinstance(lo_raw, int)
        or not isinstance(hi_raw, int)
    ):
        raise ValueError(
            f"BRIEF.{field_path}.{source_key} must be [int, int]; got "
            f"{range_value!r} — suggested fix: use integer bounds."
        )

    if lo_raw < 0 or hi_raw < 0:
        raise ValueError(
            f"BRIEF.{field_path}.{source_key} must be non-negative; "
            f"got {range_value!r}."
        )

    if lo_raw > hi_raw:
        raise ValueError(
            f"BRIEF.{field_path}.{source_key} requires min <= max; "
            f"got [{lo_raw}, {hi_raw}]."
        )

    if source_key == "pages":
        min_words = lo_raw * _WORDS_PER_PAGE
        max_words = hi_raw * _WORDS_PER_PAGE
    else:
        # "words" passes through unchanged; "slides" is a TERMINAL unit
        # (issue #742) — it is NEVER run through the words-per-page
        # conversion. ``min_words`` / ``max_words`` hold the raw slide
        # count verbatim in that case; ``source_key`` is the
        # discriminator a consumer must check before treating the
        # bounds as an actual word count.
        min_words = lo_raw
        max_words = hi_raw

    return TargetLengthRange(
        min_words=min_words,
        max_words=max_words,
        source_key=source_key,
    )


def _normalize_target_length_overrides(
    raw: Any,
    field_path: str,
    *,
    artifact_type: Optional[Union["ArtifactType", str]] = None,
) -> Optional[TargetLengthOverrides]:
    """Convert a raw ``target_length_overrides`` dict to a typed model.

    Accepts a dict whose keys are version-number strings (``"1"``,
    ``"2"``, …) and values are ``[min, max]``-style range dicts. Empty
    dict → returns a :class:`TargetLengthOverrides` with empty
    ``overrides``. Absent (``None``) → returns ``None``.

    ``artifact_type`` (issue #742) is forwarded to each per-version
    :func:`_normalize_target_length_range` call so a ``slides:``
    override is gated the same way as the top-level ``target_length``.

    Raises ``ValueError`` for malformed shape (non-dict, non-integer-
    string key, malformed range).
    """
    if raw is None:
        return None

    if not isinstance(raw, dict):
        raise ValueError(
            f"BRIEF.{field_path} must be a dict; got "
            f"{type(raw).__name__} — suggested fix: write each version "
            f"override on its own line under `target_length_overrides:`."
        )

    overrides: Dict[str, TargetLengthRange] = {}
    for key, value in raw.items():
        # YAML mappings can have int keys; normalize to string and
        # validate the integer-string shape.
        if isinstance(key, bool):
            raise ValueError(
                f"BRIEF.{field_path} key {key!r} is a boolean; version "
                f"keys must be positive integers (e.g., `\"1\"`)."
            )
        if isinstance(key, int):
            key_str = str(key)
        elif isinstance(key, str):
            key_str = key
        else:
            raise ValueError(
                f"BRIEF.{field_path} key must be a string or integer; "
                f"got {type(key).__name__}: {key!r}."
            )
        if not key_str.isdigit() or int(key_str) < 1:
            raise ValueError(
                f"BRIEF.{field_path} key {key_str!r} must be a positive "
                f"integer string (the version number); suggested fix: "
                f'write the key as `"1"`, `"2"`, etc.'
            )
        range_typed = _normalize_target_length_range(
            value,
            field_path=f"{field_path}[{key_str!r}]",
            artifact_type=artifact_type,
        )
        overrides[key_str] = range_typed

    return TargetLengthOverrides(overrides=overrides)


def _parse_dim_calibration_key(key: str) -> Optional[int]:
    """Return the dimension number from a ``dim_<N>_calibration`` key, or ``None``."""
    m = _DIM_CALIBRATION_RE.match(key)
    if not m:
        return None
    try:
        return int(m.group(1))
    except ValueError:
        return None


def _parse_dim_waiver_key(key: str) -> Optional[int]:
    """Return the dimension number from a ``dim_<N>_waiver`` key, or ``None`` (issue #393)."""
    m = _DIM_WAIVER_RE.match(key)
    if not m:
        return None
    try:
        return int(m.group(1))
    except ValueError:
        return None


def _normalize_rubric_overrides(
    raw: Any,
    field_path: str,
    *,
    artifact_type: Optional[Union["ArtifactType", str]] = None,
) -> Optional[RubricOverrides]:
    """Convert a raw ``rubric_overrides`` dict to a typed model.

    BRIEF-side schema is STRICT on shape errors at the dict level
    (non-dict raises) but tolerant on field-level oddities per the
    forward-compat contract: unknown keys are preserved verbatim under
    ``RubricOverrides.unknown_keys``; the parser warns via
    ``warnings.warn`` but does NOT raise. This is the load-bearing
    backwards-compat surface from the prior ``.anvil.json`` lenient
    loader: a future shipped ``concision_discipline`` knob lands in
    BRIEF.md ahead of loader support without breaking existing
    consumers.

    Per-field validation is STRICT however: a malformed
    ``memo_subtype`` (non-string, empty), a ``dim_N_calibration`` with
    a non-string value, a ``dim_N_waiver`` with a missing / empty /
    non-string rationale (issue #393 — an unjustified waiver is rejected
    at parse time), an out-of-range dim number, a dimension that is BOTH
    waived and calibrated (contradictory — the error names both keys), or
    a malformed ``target_length`` raises ``ValueError`` with the field
    path. The BRIEF-side reader is the schema-of-record now — silent
    drops would confuse the operator.

    Returns ``None`` for an absent value (raw is None). Returns an
    empty :class:`RubricOverrides` for a non-dict or empty dict (with
    appropriate diagnostic when non-dict).
    """
    if raw is None:
        return None

    if not isinstance(raw, dict):
        raise ValueError(
            f"BRIEF.{field_path} must be a dict; got "
            f"{type(raw).__name__} — suggested fix: write the overrides "
            f"as a nested mapping under `rubric_overrides:`."
        )

    memo_subtype: Optional[str] = None
    calibrations: List[CalibrationOverride] = []
    waivers: List[WaiverOverride] = []
    target_length: Optional[TargetLengthRange] = None
    unknown_keys: Dict[str, Any] = {}

    seen_dims: set[int] = set()
    seen_waiver_dims: set[int] = set()

    for key, value in raw.items():
        if key == "memo_subtype":
            if not isinstance(value, str) or not value.strip():
                raise ValueError(
                    f"BRIEF.{field_path}.memo_subtype must be a non-empty "
                    f"string; got {value!r}."
                )
            memo_subtype = value
            continue

        if key == "target_length":
            target_length = _normalize_target_length_range(
                value,
                field_path=f"{field_path}.target_length",
                artifact_type=artifact_type,
            )
            continue

        dim = _parse_dim_calibration_key(key)
        if dim is not None:
            if dim < MIN_DIM or dim > MAX_DIM:
                raise ValueError(
                    f"BRIEF.{field_path}.{key}: dimension {dim} out of "
                    f"range [{MIN_DIM}, {MAX_DIM}]."
                )
            if dim in seen_dims:
                raise ValueError(
                    f"BRIEF.{field_path}.{key}: dimension {dim} "
                    f"declared more than once (canonical form is "
                    f"`dim_{dim}_calibration`)."
                )
            if not isinstance(value, str) or not value.strip():
                raise ValueError(
                    f"BRIEF.{field_path}.{key} must be a non-empty "
                    f"string; got {value!r}."
                )
            seen_dims.add(dim)
            calibrations.append(CalibrationOverride(dimension=dim, text=value))
            continue

        waiver_dim = _parse_dim_waiver_key(key)
        if waiver_dim is not None:
            if waiver_dim < MIN_DIM or waiver_dim > MAX_DIM:
                raise ValueError(
                    f"BRIEF.{field_path}.{key}: dimension {waiver_dim} out "
                    f"of range [{MIN_DIM}, {MAX_DIM}]."
                )
            if waiver_dim in seen_waiver_dims:
                raise ValueError(
                    f"BRIEF.{field_path}.{key}: dimension {waiver_dim} "
                    f"waived more than once (canonical form is "
                    f"`dim_{waiver_dim}_waiver`)."
                )
            # Rationale-as-value shape (issue #393): the YAML value IS the
            # mandatory rationale. An unjustified waiver (missing / empty /
            # whitespace-only / non-string value) is rejected at parse time
            # — paired-rationale discipline, same as the iteration-cap
            # override precedent.
            if not isinstance(value, str) or not value.strip():
                raise ValueError(
                    f"BRIEF.{field_path}.{key}: a waiver REQUIRES a "
                    f"non-empty rationale string as its value (got "
                    f"{value!r}); suggested fix: write "
                    f'`dim_{waiver_dim}_waiver: "<why this dimension is '
                    f'excluded, e.g. an operator directive>"`.'
                )
            seen_waiver_dims.add(waiver_dim)
            waivers.append(WaiverOverride(dimension=waiver_dim, rationale=value))
            continue

        # Unknown key — preserve verbatim with a warning so a future
        # shipped key (e.g. concision_discipline) can land in BRIEF.md
        # ahead of loader support without breaking existing consumers.
        unknown_keys[key] = value
        warnings.warn(
            f"BRIEF.{field_path}.{key}: unknown key — preserved verbatim "
            f"under unknown_keys (forward-compat); reviewer will not "
            f"apply it",
            UserWarning,
            stacklevel=4,
        )

    # A dimension that is BOTH waived and calibrated is contradictory —
    # a waiver excludes the dimension from judgment; a calibration tunes
    # how the dimension is judged. Reject with an error naming both keys
    # (issue #393 AC3). Checked after the loop so the rejection is
    # independent of YAML key order.
    conflicted = sorted(seen_dims & seen_waiver_dims)
    if conflicted:
        dim = conflicted[0]
        raise ValueError(
            f"BRIEF.{field_path}: dimension {dim} is both waived and "
            f"calibrated — `dim_{dim}_waiver` and `dim_{dim}_calibration` "
            f"are contradictory (a waiver excludes the dimension from "
            f"judgment; a calibration tunes how it is judged). Keep "
            f"exactly one of the two keys."
        )

    # Sort calibrations + waivers by dimension for deterministic iteration
    # order.
    calibrations.sort(key=lambda c: c.dimension)
    waivers.sort(key=lambda w: w.dimension)

    return RubricOverrides(
        memo_subtype=memo_subtype,
        calibrations=calibrations,
        waivers=waivers,
        target_length=target_length,
        unknown_keys=unknown_keys,
    )


def _validate_artifact_type(
    raw: Any,
    field_path: str,
    consumer_types: frozenset = frozenset(),
    consumer_overlay_dir: Optional[Path] = None,
) -> Union[ArtifactType, str]:
    """Validate a raw ``artifact_type`` string — two-tier per #394.

    Tier 1 (closed-ended per Open Question #5): values in
    :data:`REGISTERED_ARTIFACT_TYPES` normalize to the typed enum.
    Tier 2 (consumer extension, issue #394): values backed by a
    consumer overlay JSON (``consumer_types`` — the filename stems
    discovered under
    ``<consumer>/.anvil/skills/memo/rubric_overlays/``) are accepted as
    validated plain strings. Anything else raises ``ValueError``
    listing the registered set, any discovered consumer types, and the
    consumer-overlay extension path, so a typo produces a
    self-correcting error.
    """
    if not isinstance(raw, str):
        raise ValueError(
            f"BRIEF.{field_path} must be a string; got "
            f"{type(raw).__name__}: {raw!r} — suggested fix: quote "
            f"the value (one of {list(REGISTERED_ARTIFACT_TYPES)})."
        )
    try:
        return ArtifactType(raw)
    except ValueError:
        pass
    # Legacy input alias (issue #694): a renamed artifact type may still
    # appear as its old string in a consumer BRIEF authored before the
    # rename. Normalize to the canonical enum member. Input-only —
    # nothing downstream emits the legacy string.
    if raw in _ARTIFACT_TYPE_INPUT_ALIASES:
        return _ARTIFACT_TYPE_INPUT_ALIASES[raw]
    if raw in consumer_types:
        return raw
    registered = list(REGISTERED_ARTIFACT_TYPES)
    discovered = sorted(consumer_types)
    where = (
        str(consumer_overlay_dir)
        if consumer_overlay_dir is not None
        else f"<consumer>/{CONSUMER_MEMO_OVERLAYS_RELPATH}"
    )
    raise ValueError(
        f"BRIEF.{field_path}: unknown artifact_type {raw!r}. "
        f"Registered values: {registered}. "
        f"Consumer-declared types (overlay JSONs at {where}): "
        f"{discovered}. "
        f"Suggested fix: replace with one of the registered or "
        f"consumer-declared values, add a consumer overlay JSON at "
        f"{where}/{raw}.json (no framework release needed — issue "
        f"#394), or open an issue to register a new artifact type."
    )


def _validate_render_engine(raw: Any, field_path: str) -> Optional[str]:
    """Validate a raw ``render_engine`` value against the closed allowlist.

    Closed-ended per issue #320: unknown values raise ``ValueError`` listing
    the valid trio so a typo produces a self-correcting error. ``None`` is
    valid and short-circuits — the field is optional. The actual runtime
    fallthrough (requested-but-unavailable-on-PATH) is handled in
    :func:`anvil.lib.render_gate._select_memo_engine`, not here — this
    validator only gates parse-time correctness.
    """
    if raw is None:
        return None
    if not isinstance(raw, str):
        raise ValueError(
            f"BRIEF.{field_path} must be a string; got "
            f"{type(raw).__name__}: {raw!r} — suggested fix: quote "
            f"the value (one of {list(_VALID_RENDER_ENGINES)})."
        )
    if raw not in _VALID_RENDER_ENGINES:
        raise ValueError(
            f"BRIEF.{field_path}: unknown render_engine {raw!r}. "
            f"Valid values: {list(_VALID_RENDER_ENGINES)}. "
            f"Suggested fix: replace with one of the valid values "
            f"or omit the key to use the default auto-priority "
            f"(weasyprint > wkhtmltopdf > xelatex)."
        )
    return raw


def _validate_latex_header_includes(raw: Any, field_path: str) -> Optional[str]:
    """Validate a raw ``latex_header_includes`` value (issue #347).

    The contents are opaque LaTeX — the validator only enforces type
    (``str`` or ``None``) and normalizes empty / whitespace-only inputs
    to ``None`` so the BRIEF author can write
    ``latex_header_includes:`` with an empty value and get back-compat
    behavior. Non-string types raise ``ValueError`` with a clear
    field-path message.

    Engine-scoping (xelatex-only) is *not* enforced at parse time — a
    BRIEF may set ``latex_header_includes`` alongside
    ``render_engine: weasyprint`` and the value will be carried
    through. The downstream render path
    (:func:`anvil.lib.render_gate._render_memo_source`) silently skips
    the include when the dispatched engine is not xelatex and records
    the skip in the gate's ``reasons`` audit trail. Parse-time
    enforcement would lock out the legitimate "I render with xelatex
    locally but the field falls through to weasyprint on CI" flow.
    """
    if raw is None:
        return None
    if not isinstance(raw, str):
        raise ValueError(
            f"BRIEF.{field_path} must be a string; got "
            f"{type(raw).__name__}: {raw!r} — suggested fix: write the "
            f"value as a YAML block-literal (``|``) or quoted string of "
            f"LaTeX preamble text."
        )
    if not raw.strip():
        return None
    return raw


def _validate_render_template(raw: Any, field_path: str) -> Optional[str]:
    """Validate a raw ``render_template`` value (issue #391).

    Type-and-emptiness only: the value must be a string; empty /
    whitespace-only normalizes to ``None`` (back-compat — a YAML author
    can write ``render_template:`` with nothing on the right-hand side).
    Surrounding whitespace is stripped (a path with accidental trailing
    whitespace is never intentional).

    No file-existence check at parse time — BRIEF parsing must not
    depend on cwd, and the template is a render-time input (a missing
    file at render time produces a breadcrumb + fallback to the default
    chain, per the non-blocking render contract). Engine-scoping
    (extension match against the dispatched chain) is likewise a
    render-time concern, for the same reason documented in
    :func:`_validate_latex_header_includes`: the requested engine can
    legitimately fall through on a machine missing the binary.
    """
    if raw is None:
        return None
    if not isinstance(raw, str):
        raise ValueError(
            f"BRIEF.{field_path} must be a string path; got "
            f"{type(raw).__name__}: {raw!r} — suggested fix: write the "
            f"value as a path relative to the directory containing "
            f"BRIEF.md (e.g., `render_template: sphere-memo-template.tex`)."
        )
    stripped = raw.strip()
    if not stripped:
        return None
    return stripped


class CompanionRefTypeError(ValueError):
    """Raised when a companion-ref field is declared with the wrong type (issue #718).

    A distinguishable ``ValueError`` subclass for the ``spec_ref`` /
    ``code_ref`` companion-input fields (:func:`_validate_spec_ref` /
    :func:`_validate_code_ref`) when the declared value is present but not
    a string (e.g. a YAML list, int, or dict).

    Why a dedicated subclass: the companion-ref resolvers
    (:func:`resolve_spec_ref` / :func:`resolve_code_ref`) load the BRIEF
    leniently and blanket-swallow a plain ``ValueError`` to ``None`` (the
    "BRIEF doesn't parse → tier INACTIVE" path). That blanket swallow
    cannot distinguish "the whole BRIEF is structurally invalid" from
    "this one companion-ref field is malformed" — so a malformed
    ``spec_ref`` / ``code_ref`` was silently reclassified as *absent*,
    disabling the consistency tier with no operator-visible signal
    (exactly the state the SKILL.md §Spec-ref / §Code-ref contracts say
    should never carry a broken-but-undetected declaration).

    Because this subclasses ``ValueError``, every *other* caller of
    :func:`load_project_brief` (and the strict loader) treats it exactly
    as before — a malformed companion-ref is still a hard schema error for
    them. Only the two lenient companion-ref resolvers catch it
    *specially*, converting it into the existing ``missing: true``
    structured-defect result (tier ACTIVE, ``major`` finding) rather than
    swallowing it to ``None`` (tier inactive).

    The ``field`` attribute (``"spec_ref"`` / ``"code_ref"``) lets each
    resolver recognize a malformed value of *its own* field and ignore an
    unrelated companion-ref field's malformed value (which should still
    swallow to ``None`` for it, exactly as any other unrelated BRIEF-parse
    failure would).
    """

    def __init__(self, message: str, *, field: str) -> None:
        super().__init__(message)
        self.field = field


def _validate_companion_ref(
    raw: Any,
    field_path: str,
    *,
    field: str,
    scalar_example: str,
    list_example: str,
) -> Optional[List[str]]:
    """Validate a raw companion-ref value (``spec_ref`` / ``code_ref``).

    Shared normalizer for the two structurally-identical companion-input
    fields (issue #719). Accepts either a scalar string (back-compat) or a
    YAML list of path/glob strings, and always normalizes to
    ``Optional[List[str]]`` so the resolvers see one shape.

    Normalization rules (mirroring the :func:`_validate_render_lua_filters`
    list-field precedent, with the #718 malformed-→-``missing`` posture on
    a wrong-typed value):

    - ``raw is None`` → ``None`` (undeclared; tier INACTIVE).
    - ``raw`` a **string**:
        - empty / whitespace-only → ``None`` (scalar back-compat: a YAML
          author writing ``spec_ref:`` with an empty RHS gets tier-inactive).
        - non-empty → ``[raw.strip()]`` (single-element list).
    - ``raw`` a **list**:
        - empty list → ``None`` (mirrors ``render_lua_filters`` back-compat).
        - every element a non-empty string → the stripped list, **preserving
          declaration order** (dedup happens at resolution time, not here).
        - any element not a non-empty string → raise
          :class:`CompanionRefTypeError` (declared-but-broken; the #718
          posture — the whole field is poisoned, not the single element
          skipped).
    - ``raw`` any other type (int, dict, …) → raise
      :class:`CompanionRefTypeError` (unchanged #718 behavior).

    No file-existence check at parse time — BRIEF parsing must not depend
    on cwd, and the companion is a resolution-time input. A declared-but-
    missing path surfaces at resolution time via the resolver as a
    structured ``missing: true`` / ``unresolved`` entry, never a
    parse-time raise.
    """
    if raw is None:
        return None
    if isinstance(raw, str):
        stripped = raw.strip()
        if not stripped:
            return None
        return [stripped]
    if isinstance(raw, list):
        if len(raw) == 0:
            return None
        out: List[str] = []
        for j, item in enumerate(raw):
            if not isinstance(item, str) or not item.strip():
                raise CompanionRefTypeError(
                    f"BRIEF.{field_path}[{j}] must be a non-empty string "
                    f"path/glob; got {type(item).__name__}: {item!r} — "
                    f"suggested fix: write each entry as a path relative "
                    f"to the directory containing BRIEF.md (e.g., "
                    f"`{field}: [{list_example}]`).",
                    field=field,
                )
            out.append(item.strip())
        return out
    raise CompanionRefTypeError(
        f"BRIEF.{field_path} must be a string path/glob or a list of "
        f"path/glob strings; got {type(raw).__name__}: {raw!r} — suggested "
        f"fix: write the value as a path relative to the directory "
        f"containing BRIEF.md (e.g., `{field}: {scalar_example}`) or as a "
        f"YAML list (e.g., `{field}: [{list_example}]`).",
        field=field,
    )


def _validate_spec_ref(raw: Any, field_path: str) -> Optional[List[str]]:
    """Validate a raw ``spec_ref`` value (issues #686, #719).

    Accepts a scalar string (back-compat) or a YAML list of path/glob
    strings, normalizing to ``Optional[List[str]]``. See
    :func:`_validate_companion_ref` for the full contract.
    """
    return _validate_companion_ref(
        raw,
        field_path,
        field="spec_ref",
        scalar_example="../whitepaper/whitepaper.5/whitepaper.md",
        list_example="../whitepaper/a.md, ../whitepaper/b.md",
    )


def _validate_code_ref(raw: Any, field_path: str) -> Optional[List[str]]:
    """Validate a raw ``code_ref`` value (issues #697/#706, #719).

    Mirror of :func:`_validate_spec_ref` for the ``anvil:spec`` skill's
    ``code_ref`` companion input (the implementation a normative spec
    describes). Accepts a scalar string (back-compat) or a YAML list of
    path/glob strings — the natural shape for a multi-crate / multi-module
    implementation spanning non-contiguous roots — normalizing to
    ``Optional[List[str]]``. See :func:`_validate_companion_ref` for the
    full contract.
    """
    return _validate_companion_ref(
        raw,
        field_path,
        field="code_ref",
        scalar_example="../../src/**/*.rs",
        list_example="crypto/pq/src/**/*.rs, botho/src/block.rs",
    )


def _validate_voice_corpus_exclude(raw: Any, field_path: str) -> Optional[List[str]]:
    """Validate a raw ``voice_corpus_exclude`` value (issue #890).

    Same scalar-or-list normalization as :func:`_validate_spec_ref` /
    :func:`_validate_code_ref` — see :func:`_validate_companion_ref` for
    the full contract. Unlike those two **companion-input** fields (which
    each define their own activation tier, so a malformed declaration
    must still ACTIVATE the tier and surface a ``major`` finding rather
    than silently vanishing), a malformed ``voice_corpus_exclude`` is a
    plain BRIEF parse-time error: this field only ever *narrows* an
    already-resolved ``voice.corpus`` glob, it never defines a tier of
    its own, so there is no "declared-but-broken, stay active" resolve
    -time case to preserve — the ``CompanionRefTypeError`` it raises on a
    malformed value (itself a ``ValueError``) propagates as an ordinary
    BRIEF-parse failure.
    """
    return _validate_companion_ref(
        raw,
        field_path,
        field="voice_corpus_exclude",
        scalar_example="writing-corpus/my-post.md",
        list_example="writing-corpus/a.md, writing-corpus/b.md",
    )


def _validate_render_lua_filters(
    raw: Any, field_path: str
) -> Optional[List[str]]:
    """Validate a raw ``render_lua_filters`` value (issue #391).

    Must be a list of non-empty strings (paths, BRIEF-relative or
    absolute). An empty list normalizes to ``None`` (back-compat).
    Non-list values and non-string / empty elements raise ``ValueError``
    with the offending field path. Declaration order is preserved —
    pandoc applies Lua filters in flag order.

    No file-existence checks at parse time (render-time concern; see
    :func:`_validate_render_template`).
    """
    if raw is None:
        return None
    if not isinstance(raw, list):
        raise ValueError(
            f"BRIEF.{field_path} must be a list of path strings; got "
            f"{type(raw).__name__}: {raw!r} — suggested fix: write the "
            f"value as a YAML list (e.g., "
            f"`render_lua_filters: [strip-alt.lua]`)."
        )
    if len(raw) == 0:
        return None
    out: List[str] = []
    for j, item in enumerate(raw):
        if not isinstance(item, str) or not item.strip():
            raise ValueError(
                f"BRIEF.{field_path}[{j}] must be a non-empty path "
                f"string; got {type(item).__name__}: {item!r} — "
                f"suggested fix: write each entry as a path relative to "
                f"the directory containing BRIEF.md."
            )
        out.append(item.strip())
    return out


# Scalar types accepted as ``render_metadata`` values. ``bool`` is listed
# explicitly (it is also an ``int`` subclass) so the coercion branch below
# can emit pandoc-conventional lowercase ``true`` / ``false``.
_RENDER_METADATA_SCALARS = (str, int, float, bool)


def _validate_render_metadata(
    raw: Any, field_path: str
) -> Optional[Dict[str, str]]:
    """Validate a raw ``render_metadata`` value (issue #391).

    Must be a mapping of non-empty string keys to scalar values
    (str / int / float / bool). Scalars are coerced to strings at parse
    time (bools to lowercase ``"true"`` / ``"false"`` per pandoc/YAML
    convention) so downstream consumers deal in one shape. An empty map
    normalizes to ``None`` (back-compat). Non-mapping values, non-string
    keys, and non-scalar values (lists, maps, ``None``) raise
    ``ValueError`` with the offending field path.

    The ``{N}`` version token in values is *not* expanded here — it is a
    render-time substitution (the version number is unknowable at parse
    time). Values are carried verbatim.
    """
    if raw is None:
        return None
    if not isinstance(raw, dict):
        raise ValueError(
            f"BRIEF.{field_path} must be a mapping of string keys to "
            f"scalar values; got {type(raw).__name__}: {raw!r} — "
            f"suggested fix: write the value as a YAML map (e.g., "
            f'`render_metadata:` then `  doc-type: "Investment Memo"`).'
        )
    if len(raw) == 0:
        return None
    out: Dict[str, str] = {}
    for key, value in raw.items():
        if not isinstance(key, str) or not key.strip():
            raise ValueError(
                f"BRIEF.{field_path} keys must be non-empty strings; "
                f"got {type(key).__name__}: {key!r} — suggested fix: "
                f"quote the key as a string."
            )
        if isinstance(value, bool):
            out[key] = "true" if value else "false"
        elif isinstance(value, _RENDER_METADATA_SCALARS):
            out[key] = str(value)
        else:
            raise ValueError(
                f"BRIEF.{field_path}[{key!r}] must be a scalar "
                f"(str / int / float / bool); got "
                f"{type(value).__name__}: {value!r} — suggested fix: "
                f"flatten nested values into one scalar per key "
                f"(pandoc receives each entry as `-M key=value`)."
            )
    return out


def _normalize_iteration_cap_rationale(raw: Any, field_path: str) -> Optional[str]:
    """Normalize a raw ``iteration_cap_rationale`` value (issue #349).

    The rationale is **required when set** — operator must supply a
    non-empty, non-whitespace string to activate the paired override.
    Empty / whitespace-only values normalize to ``None`` so a YAML
    author can write ``iteration_cap_rationale:`` with nothing on the
    right-hand side and get back-compat behavior (the paired field
    :attr:`BriefDocument.max_iterations` will then trigger the paired-
    override validator's "missing rationale" rejection).

    Non-string types raise ``ValueError`` with a clear field-path
    message. The contents themselves are opaque to the parser — any
    non-empty string survives the validator.
    """
    if raw is None:
        return None
    if not isinstance(raw, str):
        raise ValueError(
            f"BRIEF.{field_path} must be a string; got "
            f"{type(raw).__name__}: {raw!r} — suggested fix: write the "
            f"value as a quoted string or YAML block-literal (``|``) "
            f"naming why this thread deserves more revision passes."
        )
    if not raw.strip():
        return None
    return raw


def _validate_max_iterations(raw: Any, field_path: str) -> Optional[int]:
    """Validate a raw ``max_iterations`` value (issue #349).

    The override is sticky-raise: an integer ``>=``
    :data:`DEFAULT_MAX_ITERATIONS` is honored; values below the
    principled default are rejected at parse time. Non-integer types
    are rejected too (booleans masquerading as ``0``/``1`` would
    silently degrade the override to a no-op). ``None`` is valid and
    short-circuits — the field is optional.

    The paired-override contract — that ``max_iterations`` requires a
    non-empty :attr:`BriefDocument.iteration_cap_rationale` — is enforced
    in :func:`_validate_paired_iteration_cap_override` at the document-
    entry level rather than here so the cross-field error message can
    name both fields explicitly.
    """
    if raw is None:
        return None
    # bool is a subclass of int — reject explicitly so True/False can't
    # masquerade as 1/0 in a cap value.
    if isinstance(raw, bool) or not isinstance(raw, int):
        raise ValueError(
            f"BRIEF.{field_path} must be an integer >= "
            f"{DEFAULT_MAX_ITERATIONS}; got {type(raw).__name__}: "
            f"{raw!r} — suggested fix: write the value as an integer "
            f"(e.g., `max_iterations: 5`)."
        )
    if raw < DEFAULT_MAX_ITERATIONS:
        raise ValueError(
            f"BRIEF.{field_path}: max_iterations ({raw}) must be >= "
            f"{DEFAULT_MAX_ITERATIONS}. The override may raise the cap "
            f"but not lower it below the principled default. Suggested "
            f"fix: set `max_iterations: {DEFAULT_MAX_ITERATIONS}` "
            f"(or higher) or remove the key to fall through to the "
            f"default."
        )
    return raw


def _validate_web_search(raw: Any, field_path: str) -> Optional[bool]:
    """Validate a raw ``web_search`` value (issue #424).

    Strict bool, following the :func:`_validate_max_iterations` strict-
    type precedent: ``None`` short-circuits (the field is optional and
    absent ≡ ``false``); a real YAML boolean passes through; anything
    else — including the strings ``"true"`` / ``"yes"`` and the
    integers ``0`` / ``1`` — raises ``ValueError`` with a field-path
    message. The knob opts a thread into autonomous web literature
    search for ``paper-litsearch`` / ``paper-review``, relaxing an anti-
    hallucination posture, so a silently-coerced truthy value is worse
    than a loud parse failure.
    """
    if raw is None:
        return None
    if not isinstance(raw, bool):
        raise ValueError(
            f"BRIEF.{field_path} must be a boolean; got "
            f"{type(raw).__name__}: {raw!r} — suggested fix: write "
            f"`web_search: true` (YAML boolean, unquoted) to enable "
            f"opt-in web literature search, or remove the key to keep "
            f"the default no-web behavior."
        )
    return raw


def _validate_recommendation_target(
    raw: Any, field_path: str
) -> Optional[Literal["invest", "pass", "conditional", "undecided"]]:
    """Validate a raw per-document ``recommendation_target`` value (issue #837).

    Deliberately **lenient** — the one exception to ``BriefDocument``'s
    otherwise-STRICT per-field validation (contrast :func:`_validate_web_search`,
    :func:`_validate_max_iterations`, which raise on a malformed value).
    Mirrors :func:`load_recommendation_target`'s thread-level closed-set
    contract exactly: ``None`` and every value not in
    :data:`_RECOGNIZED_RECOMMENDATION_TARGETS` (typos like ``"Undecided"``,
    ``"tbd"``, non-string types) normalizes to ``None`` rather than
    raising. This field is operator-declared calibration posture
    metadata consumed by the reviewer's dim 1 calibration — a typo
    should degrade to "no posture declared", not block the whole
    project-level BRIEF from parsing.

    ``field_path`` is accepted (unused in the body) to keep this
    validator's signature consistent with its STRICT siblings in this
    module — none of them are called positionally, so a future
    behavior change here (e.g., a deprecation warning) can add a
    field-path-qualified message without a call-site change.
    """
    del field_path  # unused — see docstring
    if isinstance(raw, str) and raw in _RECOGNIZED_RECOMMENDATION_TARGETS:
        return raw  # type: ignore[return-value]
    return None


def _validate_paired_iteration_cap_override(
    max_iterations: Optional[int],
    iteration_cap_rationale: Optional[str],
    field_path: str,
) -> None:
    """Enforce the paired-override contract for the iteration-cap override.

    The override is **paired**: both ``max_iterations`` and
    ``iteration_cap_rationale`` must be present and well-formed for the
    override to take effect, OR both must be absent. Setting one without
    the other is a schema violation that raises with a field-path
    message naming both keys.

    This is the load-bearing audit-trail contract: an elevated cap
    without a rationale would silently raise the cap without recording
    why. The rationale text — preserved in BRIEF git history — IS the
    audit trail.
    """
    has_cap = max_iterations is not None
    has_rationale = iteration_cap_rationale is not None
    if has_cap and not has_rationale:
        raise ValueError(
            f"BRIEF.{field_path}: max_iterations is set "
            f"({max_iterations}) but iteration_cap_rationale is missing "
            f"or empty. The paired-override contract requires BOTH "
            f"fields to be present and well-formed — the rationale text "
            f"is the audit trail that documents why this thread "
            f"deserves more revision passes. Suggested fix: add a "
            f"non-empty `iteration_cap_rationale:` value explaining why "
            f"the elevated cap is authorized, OR remove the "
            f"`max_iterations:` key to fall through to the default cap "
            f"of {DEFAULT_MAX_ITERATIONS}."
        )
    if has_rationale and not has_cap:
        raise ValueError(
            f"BRIEF.{field_path}: iteration_cap_rationale is set but "
            f"max_iterations is missing. The paired-override contract "
            f"requires BOTH fields to be present and well-formed. "
            f"Suggested fix: add `max_iterations: <N>` (integer "
            f">= {DEFAULT_MAX_ITERATIONS}) naming the elevated cap, OR "
            f"remove the `iteration_cap_rationale:` key."
        )


def _normalize_documents(
    raw: Any,
    consumer_types: frozenset = frozenset(),
    consumer_overlay_dir: Optional[Path] = None,
) -> List[BriefDocument]:
    """Convert the raw ``documents:`` list into typed ``BriefDocument`` entries.

    Validates:

    - ``documents`` is a non-empty list.
    - Each entry is a dict.
    - Each entry has a non-empty string ``slug``.
    - Each entry has a valid ``artifact_type`` (registered enum value,
      or a consumer-overlay-backed type from ``consumer_types`` —
      issue #394).
    - Optional ``target_length`` parses cleanly.
    - Optional ``target_length_overrides`` parses cleanly.
    - Optional ``rubric_overrides`` parses cleanly.
    - Slugs are unique across the list (duplicate raises).
    - No unknown keys on entries (``extra="forbid"`` on
      :class:`BriefDocument`).
    """
    if raw is None:
        raise ValueError(
            "BRIEF.documents is required and must be a non-empty list. "
            "Suggested fix: add a `documents:` frontmatter key with at "
            "least one entry."
        )
    if not isinstance(raw, list):
        raise ValueError(
            f"BRIEF.documents must be a list; got {type(raw).__name__}. "
            f"Suggested fix: write each document as a list entry under "
            f"`documents:`."
        )
    if len(raw) == 0:
        raise ValueError(
            "BRIEF.documents must be a non-empty list. "
            "Suggested fix: add at least one document entry."
        )

    docs: List[BriefDocument] = []
    seen_slugs: Dict[str, int] = {}

    for i, entry in enumerate(raw):
        if not isinstance(entry, dict):
            raise ValueError(
                f"BRIEF.documents[{i}] must be a mapping; got "
                f"{type(entry).__name__}: {entry!r} — suggested fix: "
                f"write the entry with `slug:` and `artifact_type:` keys."
            )

        unknown = set(entry.keys()) - _RECOGNIZED_DOCUMENT_KEYS
        if unknown:
            raise ValueError(
                f"BRIEF.documents[{i}] has unknown keys "
                f"{sorted(unknown)} — recognized keys: "
                f"{sorted(_RECOGNIZED_DOCUMENT_KEYS)}. Suggested fix: "
                f"remove the unknown keys or rename to a recognized key."
            )

        slug_raw = entry.get("slug")
        if not isinstance(slug_raw, str) or not slug_raw.strip():
            raise ValueError(
                f"BRIEF.documents[{i}].slug is required and must be a "
                f"non-empty string; got {slug_raw!r}. Suggested fix: "
                f"add a `slug:` key with the document's directory name."
            )
        slug = slug_raw

        if slug in seen_slugs:
            raise ValueError(
                f"BRIEF.documents[{i}].slug {slug!r} duplicates the slug "
                f"at index {seen_slugs[slug]}. Suggested fix: rename one "
                f"of the duplicates — slugs must be unique within the BRIEF."
            )
        seen_slugs[slug] = i

        artifact_type_raw = entry.get("artifact_type")
        if artifact_type_raw is None:
            raise ValueError(
                f"BRIEF.documents[{i}].artifact_type is required. "
                f"Suggested fix: add an `artifact_type:` key with one of "
                f"{list(REGISTERED_ARTIFACT_TYPES)}."
            )
        artifact_type = _validate_artifact_type(
            artifact_type_raw,
            field_path=f"documents[{i}].artifact_type",
            consumer_types=consumer_types,
            consumer_overlay_dir=consumer_overlay_dir,
        )

        raw_tl = entry.get("target_length")
        target_length = (
            _normalize_target_length_range(
                raw_tl,
                field_path=f"documents[{i}].target_length",
                artifact_type=artifact_type,
            )
            if raw_tl is not None
            else None
        )

        target_length_overrides = _normalize_target_length_overrides(
            entry.get("target_length_overrides"),
            field_path=f"documents[{i}].target_length_overrides",
            artifact_type=artifact_type,
        )

        rubric_overrides = _normalize_rubric_overrides(
            entry.get("rubric_overrides"),
            field_path=f"documents[{i}].rubric_overrides",
            artifact_type=artifact_type,
        )

        render_engine = _validate_render_engine(
            entry.get("render_engine"),
            field_path=f"documents[{i}].render_engine",
        )

        render_template = _validate_render_template(
            entry.get("render_template"),
            field_path=f"documents[{i}].render_template",
        )

        render_lua_filters = _validate_render_lua_filters(
            entry.get("render_lua_filters"),
            field_path=f"documents[{i}].render_lua_filters",
        )

        render_metadata = _validate_render_metadata(
            entry.get("render_metadata"),
            field_path=f"documents[{i}].render_metadata",
        )

        latex_header_includes = _validate_latex_header_includes(
            entry.get("latex_header_includes"),
            field_path=f"documents[{i}].latex_header_includes",
        )

        max_iterations = _validate_max_iterations(
            entry.get("max_iterations"),
            field_path=f"documents[{i}].max_iterations",
        )

        iteration_cap_rationale = _normalize_iteration_cap_rationale(
            entry.get("iteration_cap_rationale"),
            field_path=f"documents[{i}].iteration_cap_rationale",
        )

        web_search = _validate_web_search(
            entry.get("web_search"),
            field_path=f"documents[{i}].web_search",
        )

        spec_ref = _validate_spec_ref(
            entry.get("spec_ref"),
            field_path=f"documents[{i}].spec_ref",
        )

        code_ref = _validate_code_ref(
            entry.get("code_ref"),
            field_path=f"documents[{i}].code_ref",
        )

        recommendation_target = _validate_recommendation_target(
            entry.get("recommendation_target"),
            field_path=f"documents[{i}].recommendation_target",
        )

        voice_corpus_exclude = _validate_voice_corpus_exclude(
            entry.get("voice_corpus_exclude"),
            field_path=f"documents[{i}].voice_corpus_exclude",
        )

        # Paired-override validation runs after the per-field validators
        # so the cross-field error names both keys with already-normalized
        # values (e.g., whitespace-only rationale → None → "missing").
        _validate_paired_iteration_cap_override(
            max_iterations,
            iteration_cap_rationale,
            field_path=f"documents[{i}]",
        )

        try:
            doc = BriefDocument(
                slug=slug,
                artifact_type=artifact_type,
                target_length=target_length,
                target_length_overrides=target_length_overrides,
                rubric_overrides=rubric_overrides,
                render_engine=render_engine,
                render_template=render_template,
                render_lua_filters=render_lua_filters,
                render_metadata=render_metadata,
                latex_header_includes=latex_header_includes,
                max_iterations=max_iterations,
                iteration_cap_rationale=iteration_cap_rationale,
                web_search=web_search,
                spec_ref=spec_ref,
                code_ref=code_ref,
                recommendation_target=recommendation_target,
                voice_corpus_exclude=voice_corpus_exclude,
            )
        except ValidationError as exc:
            raise ValueError(
                f"BRIEF.documents[{i}]: validation failed — {exc}"
            ) from exc

        docs.append(doc)

    return docs

