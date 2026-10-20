"""Pydantic model classes for the BRIEF schema (issue #1121 split).

Part of the ``anvil.lib.project_brief`` package — see the package
``__init__.py`` docstring for the full module. This submodule owns every
typed model the BRIEF parser produces: :class:`TargetLengthRange`,
:class:`TargetLengthOverrides`, :class:`CalibrationOverride`,
:class:`WaiverOverride`, :class:`RubricOverrides`, :class:`SubjectVoiceEntry`,
:class:`VoiceDocs`, :class:`ResolvedVoiceDoc`, :class:`ResolvedSubjectVoice`,
:class:`ResolvedCorpusDir`, :class:`BriefDocument`, :class:`AiByline`, and
:class:`ProjectBrief` itself.

Split from the pre-#1121 monolithic ``anvil/lib/project_brief.py`` along its
existing "Typed models" section boundary. No behavior change.
"""

from __future__ import annotations

from typing import Any, Dict, List, Literal, Optional, Union

from pydantic import BaseModel, ConfigDict, Field

from anvil.lib.project_brief.types import ArtifactType, MAX_DIM, MIN_DIM

# ---------------------------------------------------------------------------
# Typed models
# ---------------------------------------------------------------------------


class TargetLengthRange(BaseModel):
    """Word-count (or slide-count) range from a BRIEF ``target_length`` block.

    Used in two places:

    1. ``BriefDocument.target_length`` — the per-doc default range.
    2. ``RubricOverrides.target_length`` — the subtype-calibration
       override of the per-doc default.

    Both bounds are inclusive integers; ``min_words <= max_words`` is
    enforced. A ``pages`` input is converted at
    :data:`_WORDS_PER_PAGE` (600 wpp) per the SKILL.md convention.

    A ``slides`` input (issue #742; ``deck`` / ``slides``
    ``artifact_type`` only — see :data:`_SLIDES_UNIT_ARTIFACT_TYPES`) is
    the one exception to the words-based contract: slide count is a
    TERMINAL unit for a deck, not a proxy for word/page length, so it is
    passed through UNCONVERTED. For a ``source_key == "slides"`` range,
    ``min_words`` / ``max_words`` hold the raw slide-count bounds
    verbatim (the field names are the words/pages-era names; no
    words-per-page-style conversion is ever applied to them) — always
    check ``source_key`` before interpreting the bounds as a word count.

    Attributes
    ----------
    min_words
        Minimum word count (inclusive) — or, for ``source_key ==
        "slides"``, the minimum slide count (inclusive), unconverted.
    max_words
        Maximum word count (inclusive). Must be ``>= min_words`` — or,
        for ``source_key == "slides"``, the maximum slide count
        (inclusive), unconverted.
    source_key
        ``"words"``, ``"pages"``, or ``"slides"`` — which top-level key
        the on-disk range used. Captured for the audit trail so a
        reader can see whether the BRIEF author wrote in words, pages,
        or slides.
    """

    model_config = ConfigDict(extra="forbid")

    min_words: int = Field(..., ge=0)
    max_words: int = Field(..., ge=0)
    source_key: str = Field(...)


class TargetLengthOverrides(BaseModel):
    """Per-version target-length override map for a BRIEF document entry.

    Maps version number (as a string: ``"1"``, ``"2"``, …) to a
    :class:`TargetLengthRange`. The historical ``.anvil.json`` shape was
    ``target_length.overrides.v1`` / ``v2`` / …; the BRIEF-side shape is
    a bare-integer-string key per entry because YAML mappings carry no
    natural ``v`` prefix. Authors who want to be explicit can quote the
    key (``"1"``) — the YAML parser collapses ``1`` and ``"1"`` to the
    same string anyway.

    Example::

        target_length_overrides:
          "1": [8000, 11000]
          "2": [7500, 10500]
          "3": [7000, 10000]

    The same per-version resolution order documented in SKILL.md
    §"Length targets" applies:

    1. If ``target_length_overrides["<N>"]`` is set, use that range.
    2. Else if ``target_length`` is set, use that.
    3. Else, no target — fall back to the implicit judgment.

    The resolver lives in the drafter / reviser code path; this module
    only surfaces the typed dict.

    Attributes
    ----------
    overrides
        Map from version-number string (e.g., ``"1"``) to a
        :class:`TargetLengthRange`. May be empty.
    """

    model_config = ConfigDict(extra="forbid")

    overrides: Dict[str, TargetLengthRange] = Field(default_factory=dict)

    def for_version(self, version: int) -> Optional[TargetLengthRange]:
        """Return the override for ``version`` or ``None``.

        Convenience accessor for the drafter / reviser resolution
        helper. The key on disk is a string (``"1"``, ``"2"``, …) so
        the lookup converts ``version`` to its string form.
        """
        return self.overrides.get(str(version))


class CalibrationOverride(BaseModel):
    """One per-dimension calibration override.

    Returned by ``RubricOverrides.calibrations`` as a list, sorted by
    dimension number. The reviewer iterates this list and appends
    ``"calibration applied: <text>"`` to each affected dimension's
    justification.

    The ``dimension`` field uses the integer 1-9 namespace from the memo
    rubric, NOT a string id — the rubric markdown uses ordinal-prefixed
    dimension labels ("1 Recommendation clarity", ...) but the on-disk
    override key is ``dim_1_calibration`` etc. and a numeric field is the
    most direct mapping.
    """

    model_config = ConfigDict(extra="forbid")

    dimension: int = Field(
        ...,
        ge=MIN_DIM,
        le=MAX_DIM,
        description=(
            "Memo rubric dimension number (1-9 per "
            "``anvil/skills/memo/rubric.md``). The on-disk key is "
            "``dim_<dimension>_calibration``."
        ),
    )
    text: str = Field(
        ...,
        min_length=1,
        description=(
            "Calibration prose to append to the dimension's reviewer "
            "justification. Verbatim text — no rewording, no truncation. "
            "The author's exact wording is the load-bearing audit trail."
        ),
    )


class WaiverOverride(BaseModel):
    """One per-dimension waiver — an operator-directed content exclusion (issue #393).

    Returned by ``RubricOverrides.waivers`` as a list, sorted by dimension
    number. A waived dimension is removed from BOTH the numerator and the
    denominator of the verdict computation; the advance threshold scales
    proportionally (``nominal_threshold * (nominal_total - waived_weight)
    / nominal_total`` — see
    ``anvil/lib/rubric_overrides_suffix.py::normalized_advance_threshold``).

    The on-disk shape is **rationale-as-value**: ``dim_6_waiver: "<why>"``.
    The rationale is MANDATORY — an unjustified waiver is rejected at
    parse time (paired-rationale discipline, same as the iteration-cap
    override / ``--polish`` reason precedent). The rationale is surfaced
    **verbatim** in the reviewer's ``verdict.md`` so an investor-send
    reader sees what was excluded and why.

    Waivers remove scoring weight ONLY. Critical flags are NOT waivable:
    a dim-6 waiver does not suppress the ``Fabricated team credentials``
    flag machinery — if waived-dimension content appears in the artifact
    anyway, the flag fires in full.
    """

    model_config = ConfigDict(extra="forbid")

    dimension: int = Field(
        ...,
        ge=MIN_DIM,
        le=MAX_DIM,
        description=(
            "Rubric dimension number (1-9). The on-disk key is "
            "``dim_<dimension>_waiver``."
        ),
    )
    rationale: str = Field(
        ...,
        min_length=1,
        description=(
            "Mandatory operator rationale for the exclusion. Verbatim text "
            "— no rewording, no truncation. Quoted verbatim in verdict.md; "
            "the author's exact wording is the load-bearing audit trail."
        ),
    )


class RubricOverrides(BaseModel):
    """Parsed ``rubric_overrides`` block from a BRIEF document entry.

    All fields are optional. An "empty" instance (every field ``None``)
    is the canonical no-overrides state and is returned by
    :func:`load_rubric_overrides_for_slug` for slugs whose BRIEF entry
    has no ``rubric_overrides`` block (or for projects with no BRIEF
    at all).

    Callers check presence with ``is not None`` on individual fields, or
    use the ``is_empty`` property as a fast-path "did the consumer declare
    any overrides at all" check.
    """

    model_config = ConfigDict(extra="forbid")

    memo_subtype: Optional[str] = Field(
        None,
        description=(
            "Free-string label naming the memo shape. Opaque to the loader; "
            "intended for human reference and audit-trail. Two studio-canary "
            "shapes: ``synthesis-brief`` and ``feedback-memo``."
        ),
    )
    calibrations: List[CalibrationOverride] = Field(
        default_factory=list,
        description=(
            "Per-dimension calibration overrides, sorted by dimension. "
            "Each entry corresponds to a ``dim_<N>_calibration`` key on disk."
        ),
    )
    waivers: List[WaiverOverride] = Field(
        default_factory=list,
        description=(
            "Per-dimension waivers (issue #393), sorted by dimension. Each "
            "entry corresponds to a ``dim_<N>_waiver`` key on disk "
            "(rationale-as-value). A dimension may carry a calibration OR "
            "a waiver, never both — the parser rejects the conflict."
        ),
    )
    target_length: Optional[TargetLengthRange] = Field(
        None,
        description=(
            "Optional override of the document's top-level ``target_length``. "
            "When set, the drafter / reviser's resolution helper uses this "
            "value rather than the document's top-level one. Same flat-shape "
            "semantics as the document-level field; per-version overrides "
            "remain at ``target_length_overrides`` (the per-doc surface)."
        ),
    )
    unknown_keys: Dict[str, Any] = Field(
        default_factory=dict,
        description=(
            "Forward-compat passthrough: any keys in ``rubric_overrides`` "
            "that the loader does not recognize land here verbatim. The "
            "BRIEF-side parser raises on unknown keys for the document "
            "entry itself, but ``rubric_overrides`` retains the lenient "
            "forward-compat surface — same as the prior ``.anvil.json`` "
            "shape did — so a future shipped ``memo_subtype`` enum or a "
            "Concision-Discipline knob can land in BRIEF.md ahead of "
            "loader support."
        ),
    )

    @property
    def is_empty(self) -> bool:
        """Return True when no overrides are declared.

        Useful as a fast-path in the reviewer: a doc with ``is_empty`` true
        should produce identical output to a doc with no ``rubric_overrides``
        block at all.
        """
        return (
            self.memo_subtype is None
            and not self.calibrations
            and not self.waivers
            and self.target_length is None
            and not self.unknown_keys
        )

    def calibration_for(self, dimension: int) -> Optional[str]:
        """Return the calibration text for ``dimension`` or ``None``.

        Convenience accessor for the reviewer: ``override.calibration_for(1)``
        returns the calibration prose for memo rubric dim 1, or ``None`` if
        no override is set for that dim.
        """
        for entry in self.calibrations:
            if entry.dimension == dimension:
                return entry.text
        return None

    def waiver_for(self, dimension: int) -> Optional[str]:
        """Return the waiver rationale for ``dimension`` or ``None`` (issue #393).

        Convenience accessor for the reviewer's verdict aggregation:
        ``override.waiver_for(6)`` returns the operator's verbatim waiver
        rationale for rubric dim 6, or ``None`` when the dimension is not
        waived.
        """
        for entry in self.waivers:
            if entry.dimension == dimension:
                return entry.rationale
        return None


class SubjectVoiceEntry(BaseModel):
    """One entry in the optional ``voice.subjects`` list (issue #598).

    The **subject voice tier** grounds a third party's rendered dialogue
    in that person's *spoken* corpus (interview transcripts) — as opposed
    to the author-persona tier (:class:`VoiceDocs`), which grounds the
    author's prose in their *published* exemplars. A memoir reconstructing
    a grandmother's dialogue, a case study quoting a customer, an
    oral-history project — anywhere a real person's speech is rendered
    from recorded source.

    On-disk shape (one entry per speaker)::

        voice:
          subjects:
            - name: grani
              corpus: transcripts/grani/**/*.md   # spoken ground truth (glob)
              voice_doc: planning/grani-voice.md  # cadence + failure modes (optional)
            - name: aunt-jo
              corpus: transcripts/aunt-jo/**/*.md
              # voice_doc optional — corpus alone activates the entry

    Attributes
    ----------
    name
        Speaker identifier used in review findings and the
        ``subject_voice_grounding`` ``_summary.md`` block. Required,
        non-empty.
    corpus
        Glob (project-root-first, consumer-root fallback — same semantics
        as the author :attr:`VoiceDocs.corpus`) selecting the transcript
        files that are this speaker's spoken ground truth. Required,
        non-empty. Resolved by :func:`resolve_subject_voice_docs`; a glob
        matching zero files comes back ``missing: true`` (a defect to
        surface, not a crash).
    voice_doc
        Optional path to a markdown doc documenting this speaker's cadence
        rules, characteristic openers, and named failure modes (e.g.
        "an em-dash inside a spoken line is a strong drift signal; balanced
        multi-clause sentences are polish creep"). Corpus alone is
        sufficient to activate the entry — ``voice_doc`` is a refinement,
        not a requirement.
    """

    model_config = ConfigDict(extra="forbid")

    name: str = Field(..., min_length=1)
    corpus: str = Field(..., min_length=1)
    voice_doc: Optional[str] = Field(default=None)


class VoiceDocs(BaseModel):
    """Parsed optional top-level ``voice:`` block (issue #461).

    The voice/persona grounding-docs contract: a project declares up to
    four voice artifacts that ground the drafter's register and the
    reviewer's voice-fidelity calibration (see
    ``anvil/lib/snippets/voice_grounding.md`` for the role contracts).

    On-disk shape (every sub-key optional; the block itself optional)::

        voice:
          style_guide: STYLE_GUIDE.md        # register / cadence rules
          vocabulary: VOCABULARY.md          # AI-tell guidance (judgment side)
          values: VALUES.md                  # stances / anti-stances / standing
          corpus: writing-corpus/**/*.md     # published exemplars (glob)
          rhetoric_rules: rhetoric-rules.json  # consumer lint rules (gate side)

    **No ``voice:`` block → byte-identical behavior** (the #428/#452
    activation pattern). Declared paths resolve **project-root first,
    then consumer-root** via :func:`resolve_voice_docs` — voice docs
    are usually persona-level repo-root artifacts shared across
    projects, but a project ghostwriting in a different persona can
    shadow them locally.

    File existence is NOT validated at parse time (environment, not
    schema). A declared-but-missing file ACTIVATES the tier and
    surfaces as a ``major`` review finding — "a broken declaration is
    a defect to surface, not an opt-out" (the
    ``report/lib/customer_context.py`` posture).

    **``rhetoric_rules`` is the asymmetric fifth sub-key** (issue
    #468): a path to a consumer **JSON rule file** consumed by the
    render gate's advisory ``memo_rhetoric_lint`` check (issue #463),
    NOT a markdown grounding doc for the drafter/reviewer loop. It
    never joins :data:`VOICE_DOC_KINDS`, is excluded from
    :func:`resolve_voice_docs` output, and does NOT count toward
    :attr:`is_empty` — a ``rhetoric_rules``-only block activates ONLY
    the lint wiring (via :func:`resolve_rhetoric_rules`), never the
    voice-grounding judgment tier.

    Unknown sub-keys are **preserved verbatim** under ``unknown_keys``
    (lenient inner-block posture, same as
    ``RubricOverrides.unknown_keys``) so a forward-shipped sub-key
    can land in BRIEF.md ahead of loader support without
    breaking existing consumers. The loader warns via
    ``warnings.warn`` so the typo case stays visible.
    """

    model_config = ConfigDict(extra="forbid")

    style_guide: Optional[str] = Field(
        None,
        description=(
            "Path to the register/cadence rules doc, relative to the "
            "project root (consumer-root fallback) or absolute."
        ),
    )
    vocabulary: Optional[str] = Field(
        None,
        description=(
            "Path to the vocabulary guidance doc (AI-tell words, "
            "frequency discipline). Judgment-side only — deterministic "
            "screening is the rhetoric lint's job (issue #463)."
        ),
    )
    values: Optional[str] = Field(
        None,
        description=(
            "Path to the values doc (stances / anti-stances / standing "
            "/ voice signatures / failure modes)."
        ),
    )
    corpus: Optional[str] = Field(
        None,
        description=(
            "Glob (relative to project root, consumer-root fallback) "
            "selecting published exemplars quoted as voice ground "
            "truth — e.g. ``writing-corpus/**/*.md``."
        ),
    )
    rhetoric_rules: Optional[str] = Field(
        None,
        description=(
            "Path to a consumer JSON rule file for the render gate's "
            "advisory ``memo_rhetoric_lint`` check (issue #463; wired "
            "by #468). Gate-side only — NOT a grounding doc: excluded "
            "from ``VOICE_DOC_KINDS``, ``resolve_voice_docs``, and "
            "``is_empty``. Resolved by ``resolve_rhetoric_rules``."
        ),
    )
    subjects: Optional[List[SubjectVoiceEntry]] = Field(
        default=None,
        description=(
            "Subject voice tier (issue #598): one entry per third-party "
            "speaker whose dialogue is rendered from a spoken corpus. "
            "Independently activated from the author tier — a "
            "subjects-only block keeps ``is_empty`` True. ``None`` "
            "(absent) or an empty list are equivalent; a non-empty list "
            "activates the tier. Resolved by "
            ":func:`resolve_subject_voice_docs`."
        ),
    )
    unknown_keys: Dict[str, Any] = Field(
        default_factory=dict,
        description=(
            "Forward-compat passthrough: any sub-keys the loader does "
            "not recognize land here verbatim. Surfaced via "
            "``warnings.warn`` at parse time."
        ),
    )

    @property
    def is_empty(self) -> bool:
        """Return True when no recognized author-tier voice doc is declared.

        An empty block (``voice: {}`` or only unknown sub-keys) does
        NOT activate the author voice-grounding tier — consumers treat
        ``is_empty`` exactly like an absent block. ``rhetoric_rules``
        deliberately does NOT count: it is gate-side lint config, not
        drafter/reviewer grounding, so a ``rhetoric_rules``-only block
        is still ``is_empty`` (the lint wiring activates independently
        via :func:`resolve_rhetoric_rules`).

        **``subjects`` does NOT count either** (issue #598): the subject
        voice tier and the author voice tier activate *independently*. A
        ``subjects``-only block (no author-tier keys) is still
        ``is_empty`` — the author tier stays inactive while the subject
        tier activates via :attr:`has_subjects` /
        :func:`resolve_subject_voice_docs`. A memoir may declare both; a
        case study may declare subjects only. Neither tier depends on the
        other.
        """
        return (
            self.style_guide is None
            and self.vocabulary is None
            and self.values is None
            and self.corpus is None
        )

    @property
    def has_subjects(self) -> bool:
        """Return True when the subject voice tier is active (issue #598).

        The subject-tier analog of ``not is_empty`` for the author tier:
        True iff a non-empty :attr:`subjects` list is declared. Empty /
        absent ``subjects`` → False (byte-identical to pre-#598). The two
        tiers are independent — ``has_subjects`` may be True while
        ``is_empty`` is also True (a subjects-only block).
        """
        return bool(self.subjects)


class ResolvedVoiceDoc(BaseModel):
    """One resolved entry from :func:`resolve_voice_docs` (issue #461).

    Missing-file results are carried as **structured entries** —
    resolution never raises on absence. A ``missing: true`` entry is
    the reviewer's signal to surface a ``major`` finding (broken
    declaration) while keeping the tier active.
    """

    model_config = ConfigDict(extra="forbid")

    kind: Literal[
        "values",
        "style_guide",
        "vocabulary",
        "corpus",
        "rhetoric_rules",
        "subject_corpus",
        "subject_voice_doc",
    ] = Field(
        ...,
        description=(
            "Which voice doc this entry resolves. ``rhetoric_rules`` "
            "entries (issue #468) come only from "
            ":func:`resolve_rhetoric_rules` — never from "
            ":func:`resolve_voice_docs`. ``subject_corpus`` / "
            "``subject_voice_doc`` entries (issue #598) come only from "
            ":func:`resolve_subject_voice_docs`, wrapped in a "
            ":class:`ResolvedSubjectVoice`."
        ),
    )
    declared: str = Field(
        ...,
        description="The verbatim path / glob string from the BRIEF.",
    )
    paths: List[str] = Field(
        default_factory=list,
        description=(
            "Absolute path strings of the resolved file(s). Single "
            "element for the three doc kinds; sorted list for the "
            "corpus glob. Empty when ``missing``."
        ),
    )
    missing: bool = Field(
        ...,
        description=(
            "True when the declared path / glob matched nothing at "
            "either resolution root."
        ),
    )
    source: Optional[Literal["project", "consumer", "absolute"]] = Field(
        None,
        description=(
            "Which root the entry resolved against: ``project`` "
            "(project-root hit, first precedence), ``consumer`` "
            "(consumer-root fallback via the ``.anvil/`` marker walk), "
            "``absolute`` (declared as an absolute path). ``None`` "
            "when ``missing``."
        ),
    )
    excluded: List[str] = Field(
        default_factory=list,
        description=(
            "Issue #890: absolute path strings dropped from ``paths`` "
            "by :func:`resolve_voice_docs`'s ``exclude_self_slug`` "
            "self-published-form exclusion and/or a document's declared "
            "``voice_corpus_exclude``. Sorted; always empty for the "
            "three non-``corpus`` doc kinds and for every caller that "
            "does not pass ``exclude_self_slug``, so this field is "
            "fully inert (empty list, byte-identical output) for every "
            "pre-#890 consumer."
        ),
    )
    exclusion_reasons: Dict[str, str] = Field(
        default_factory=dict,
        description=(
            "Issue #890: maps each ``excluded`` path to a short "
            "human-readable reason — ``'published self (inferred from "
            "slug)'`` for the automatic exclusion, or ``\"declared "
            "corpus_exclude: '<pattern>'\"`` for a path matched by the "
            "document's ``voice_corpus_exclude``. Feeds "
            "``_summary.md``'s ``voice_grounding.corpus_excluded`` "
            "block so the calibration base stays auditable."
        ),
    )


class ResolvedSubjectVoice(BaseModel):
    """One resolved entry from :func:`resolve_subject_voice_docs` (issue #598).

    The subject-tier analog of :class:`ResolvedVoiceDoc`, one per
    declared ``voice.subjects`` entry (in declared order). Bundles the
    resolved spoken corpus and the optional resolved voice doc for a
    single speaker. Resolution mirrors the author tier exactly:
    project-root first then consumer-root, never raising on absence —
    a missing corpus glob or a missing voice doc comes back as a
    structured ``missing: true`` :class:`ResolvedVoiceDoc`, the
    reviewer's signal to surface a ``major`` finding while keeping the
    subject tier active.
    """

    model_config = ConfigDict(extra="forbid")

    name: str = Field(
        ...,
        description=(
            "The speaker identifier from the BRIEF (``voice.subjects[].name``), "
            "used in review findings and the ``subject_voice_grounding`` "
            "``_summary.md`` block."
        ),
    )
    corpus: ResolvedVoiceDoc = Field(
        ...,
        description=(
            "The resolved spoken corpus (``kind='subject_corpus'``). A glob "
            "matching zero files at either root is a ``missing: true`` "
            "entry — the reviewer's ``major``-finding signal."
        ),
    )
    voice_doc: Optional[ResolvedVoiceDoc] = Field(
        default=None,
        description=(
            "The resolved cadence / failure-modes doc "
            "(``kind='subject_voice_doc'``), or ``None`` when the subject "
            "entry declared no ``voice_doc``. A declared-but-missing "
            "voice doc is a ``missing: true`` entry (never ``None``)."
        ),
    )


class ResolvedCorpusDir(BaseModel):
    """One resolved entry from :func:`resolve_corpus_dirs` (issue #597).

    The factual-ground-truth analog of :class:`ResolvedVoiceDoc`, but for
    a **directory** rather than a file / glob: one per declared
    ``corpus`` path, in declared order. The declared path names a
    read-only evidence base (interview transcripts, family letters,
    engagement notes, lab notebooks) whose passages the ``provenance.md``
    claim→source map cites and the corpus-audit critic verifies against
    (see ``anvil/lib/snippets/provenance.md``).

    Missing-directory results are carried as **structured entries** —
    resolution never raises on absence. A ``missing: true`` entry
    activates the corpus tier and is the reviewer's signal to surface a
    ``major`` finding (broken declaration), the same defect-to-surface
    posture as the voice tier.

    This is the substance-verification half of the local-corpus contract;
    voice/cadence fidelity is the ``voice.subjects`` tier (issue #598).
    The two tiers are independent and may both be declared by one memoir.
    """

    model_config = ConfigDict(extra="forbid")

    declared: str = Field(
        ...,
        description="The verbatim directory path string from the BRIEF.",
    )
    path: Optional[str] = Field(
        None,
        description=(
            "Absolute resolved directory path. ``None`` when ``missing`` "
            "(the declared dir was absent at every resolution root)."
        ),
    )
    missing: bool = Field(
        ...,
        description=(
            "True when the declared path is not a directory at either "
            "resolution root (project then consumer)."
        ),
    )
    source: Optional[Literal["project", "consumer", "absolute"]] = Field(
        None,
        description=(
            "Which root the entry resolved against: ``project`` "
            "(project-root hit, first precedence), ``consumer`` "
            "(consumer-root fallback via the ``.anvil/`` marker walk), "
            "``absolute`` (declared as an absolute path). ``None`` when "
            "``missing``."
        ),
    )


class BriefDocument(BaseModel):
    """One entry in the project BRIEF's ``documents:`` frontmatter list.

    Attributes
    ----------
    slug
        Document slug. Names the sibling directory under the project
        root (``<project>/<slug>/``) that holds the document's version
        dirs. Required, non-empty, must contain only filesystem-safe
        characters (alphanumerics, hyphens, underscores) — the on-disk
        directory naming convention.
    artifact_type
        Registered artifact type (an :class:`ArtifactType` member) or a
        consumer-declared type (a validated plain ``str`` backed by a
        consumer overlay JSON — issue #394). Drives rubric overlay
        selection in sub-deliverable 3 (#286). Validated two-tier
        against :data:`REGISTERED_ARTIFACT_TYPES` and the discovered
        consumer overlay registry — values in neither tier raise a
        clear error listing both sets and the consumer-overlay
        extension path. Never a free string. Registered values are
        normalized to enum members; consumer values stay plain strings
        (str-enum members and plain strings interoperate for equality
        / hashing, so membership checks against
        :data:`MEMO_ARTIFACT_TYPES` work uniformly).
    target_length
        Optional word-count range for this document. When set, the
        drafter / reviser's resolution helper uses it as the document-
        level length target. When absent, the resolver falls back to
        the rubric overlay's default range.
    target_length_overrides
        Optional per-version overrides on top of ``target_length``. Each
        key is a version-number string (e.g., ``"1"``); each value is a
        ``[min, max]`` range. Mirrors the historical
        ``.anvil.json target_length.overrides`` shape (issue #296
        consolidation moved it here).
    rubric_overrides
        Optional :class:`RubricOverrides` block — subtype calibration
        per PR #265 (issue #233). Mirrors the historical
        ``.anvil.json rubric_overrides`` shape (issue #296
        consolidation moved it here).
    render_engine
        Optional per-document override for the memo HTML/PDF engine
        used by ``anvil/lib/render_gate.py``. One of
        ``"weasyprint"``, ``"xelatex"``, or ``"wkhtmltopdf"`` (issue
        #320). When set, ``_select_memo_engine`` honors this request
        if the named binary is on PATH; otherwise it gracefully
        falls through to the existing
        ``weasyprint > wkhtmltopdf > xelatex`` auto-priority. The
        theme-level default knob shipped by parallel issue #322 sits
        *below* this per-doc value in precedence (per-thread >
        per-project > per-theme > framework default).
    render_template
        Optional per-document consumer-owned pandoc template (issue
        #391). A path string — resolved relative to the directory
        containing ``BRIEF.md`` (the project root) at render time;
        absolute paths are accepted and used as-is. When set, the memo
        render chain passes ``--template <resolved-path>`` to pandoc
        *instead of* the theme/framework template, **iff** the template
        extension matches the dispatched engine chain (``.tex`` /
        ``.latex`` on the ``xelatex`` chain; ``.html`` / ``.htm`` on the
        ``weasyprint`` / ``wkhtmltopdf`` chain). On extension/engine
        mismatch or a missing file, the consumer template is skipped
        with a breadcrumb in ``render_gate.reasons`` and the existing
        resolver chain (theme > framework default) applies — the
        #347-style silent-with-record skip. Precedence: per-doc
        ``render_template`` > theme-resolved template > framework
        default, consistent with the documented
        ``per-thread > per-project > per-theme > framework`` ordering.

        Parse-time validation enforces type only (non-empty string;
        whitespace-only normalizes to ``None``). File existence is a
        render-time concern — BRIEF parsing must not depend on cwd.
    render_lua_filters
        Optional per-document list of pandoc Lua filter paths (issue
        #391). Each entry is resolved like :attr:`render_template`
        (BRIEF-relative or absolute). Engine-agnostic — Lua filters act
        on pandoc's front-end and are valid on every chain; each
        resolved filter is passed as ``--lua-filter <path>`` in
        declaration order. A missing filter file is skipped with a
        breadcrumb in ``render_gate.reasons``; the remaining filters
        still apply. Empty list normalizes to ``None``.
    render_metadata
        Optional per-document map of pandoc metadata entries (issue
        #391). Each ``key: value`` pair becomes one ``-M key=value``
        flag. Values must be scalars (str / int / float / bool) and are
        coerced to strings at parse time (bools to ``"true"`` /
        ``"false"``). Engine-agnostic — always passed when set.

        One recognized token: a literal ``{N}`` in a metadata *value*
        is replaced with the version number (parsed from the
        ``<slug>.{N}`` version-dir name) at render time — e.g.,
        ``doc-version: "Draft v{N}"`` renders as ``Draft v7`` for
        ``<slug>.7/``. No other tokens are recognized; other brace text
        passes through verbatim. Empty map normalizes to ``None``.

        Example (the studio canary's branded-bundle shape)::

            documents:
              - slug: investment-memo
                render_engine: xelatex
                render_template: sphere-memo-template.tex
                render_lua_filters: [strip-alt.lua]
                render_metadata:
                  doc-type: "Investment Memo"
                  doc-version: "Draft v{N}"
    latex_header_includes
        Optional per-document preamble extension threaded into pandoc's
        ``header-includes`` slot when the dispatched engine is
        ``xelatex`` (issue #347). Free-form LaTeX text. Used to load
        consumer-specific packages (e.g., ``xcolor``, ``tabularx``) or
        define named colors / custom environments referenced by
        ``{=latex}`` raw blocks in the memo body, *without* requiring
        the operator to maintain a full ``template.tex`` override.

        Engine-scoped by name: pandoc's ``header-includes`` metadata is
        also honored by the HTML chain (``template.html`` has the same
        ``$for(header-includes)$`` slot), so a generic
        ``header_includes`` could surprise an operator who flips
        ``render_engine`` between ``xelatex`` and ``weasyprint``. The
        explicit ``latex_`` prefix makes it visible that the contents
        are xelatex-only — when the dispatched engine is *not*
        xelatex, ``_render_memo_source`` silently skips the include
        and records the skip in the gate's ``reasons`` audit trail.

        The contents are opaque to the parser: any string survives the
        validator. Empty / whitespace-only values are normalized to
        ``None`` so a YAML author can write ``latex_header_includes:``
        with nothing on the right-hand side and get back-compat
        behavior.

        Example (a table-dense memo using ``{=latex}`` blocks)::

            latex_header_includes: |
              \\usepackage{xcolor}
              \\definecolor{green}{HTML}{059669}
              \\definecolor{ink}{HTML}{0f172a}
              \\usepackage{tabularx}
              \\newcolumntype{Y}{>{\\raggedright\\arraybackslash}X}
    max_iterations
        Optional paired-override of the default iteration cap
        (:data:`DEFAULT_MAX_ITERATIONS` = 4) for the review/revise loop
        on this thread (issue #349). When set, the override **may raise
        but not lower** the principled default — values below
        :data:`DEFAULT_MAX_ITERATIONS` are treated as malformed and
        rejected at parse time.

        The override is **paired** with :attr:`iteration_cap_rationale`:
        both keys must be present and well-formed for the override to
        take effect. Setting :attr:`max_iterations` without a non-empty
        :attr:`iteration_cap_rationale` (or vice-versa) is a schema
        violation — the BRIEF parser raises ``ValueError`` with the
        offending field path so the operator can correct the BRIEF
        before any drafter / reviser pass picks up an unjustified
        override.

        The paired-override design mirrors the deck skill's
        ``<thread>/.anvil.json`` contract documented at
        ``anvil/skills/deck/SKILL.md`` §"Per-thread override contract".
        The deck override lives in ``.anvil.json`` (the per-thread
        carrier predating the #296 consolidation); the memo override
        lives here in the project BRIEF (the post-#296 single-source-
        of-truth carrier).

        Semantics are **sticky raise**, NOT single-use: setting
        ``max_iterations: 5`` raises the cap to 5 until the BRIEF is
        edited again. The required rationale — not single-use semantics
        — is what prevents abuse.

        Drafter and reviser commands mirror the resolved value into
        per-version ``_progress.json.metadata.max_iterations`` and
        ``_progress.json.metadata.iteration_cap_rationale`` so each
        version dir carries an audit trail of the cap in effect when it
        was produced. The reviser's BLOCKED notice (see
        ``commands/memo-revise.md`` §"BLOCKED notice") surfaces the
        rationale verbatim when the elevated cap is hit, so the operator
        sees the prior authorization at the moment they need it.
    iteration_cap_rationale
        Required-when-:attr:`max_iterations`-is-set free-prose
        justification for the elevated cap (issue #349). When set,
        documents *why* this thread deserves more revision passes than
        the principled default. The rationale text is what makes the
        override principled and is preserved in BRIEF git history as the
        audit trail.

        Whitespace-only values are normalized to ``None`` at parse time
        — a YAML author can write ``iteration_cap_rationale:`` with
        nothing on the right-hand side, but that field will not
        activate an override (the parser will raise because the paired
        :attr:`max_iterations` is then set without a valid rationale).

        Example (a memo thread surfacing the cap-bound near-miss
        documented in issue #349)::

            documents:
              - slug: beacon
                artifact_type: investment-memo
                max_iterations: 5
                iteration_cap_rationale: |
                  Operator-extended to 5 on 2026-06-08. Reason: v4 verdict
                  34/44 vs floor 35, gap is design-side (slide 7 figsize +
                  slide 4 preamble drop), reviewer identified memo-revise
                  can close it; founder follow-ups for source-side lift
                  (Dims 3/5/6) are tracked separately at issue X.
    web_search
        Optional consumer-opt-in autonomous web literature search for
        the ``paper`` skill's ``paper-litsearch`` / ``paper-review`` commands
        (issue #424). Strict bool: ``true`` enables web search; absent /
        ``false`` / ``None`` are all equivalent and leave the commands
        byte-identical to their default no-web behavior. Non-bool
        values (including YAML strings like ``"true"`` and the integers
        ``0``/``1``) are rejected at parse time with a field-path
        message — a silently-coerced truthy string must not flip an
        anti-hallucination posture.

        The per-thread ``<thread>/BRIEF.md`` frontmatter is the primary
        carrier of this knob (search appetite is per-paper); this
        document-entry key is the post-#295 project-model equivalent so
        a project BRIEF declaring the knob does not trip the STRICT
        unknown-key rejection. Every web-discovered citation must still
        pass the resolver-verified-or-dropped contract via
        ``anvil/lib/cite.py::resolve()`` — see
        ``anvil/skills/paper/commands/paper-litsearch.md``.

        Example::

            documents:
              - slug: q3-method
                artifact_type: paper
                web_search: true
    spec_ref
        Optional companion-input path/glob for the ``anvil:primer`` skill
        (issue #686): the formal sibling artifact (a whitepaper, spec,
        standard, or API doc) that a primer teaches *alongside*. Resolved
        project-root-first then consumer-root by
        :func:`resolve_spec_ref` — the same walk the ``voice:`` docs and
        ``report``'s ``prior_reports[]`` use. ``primer-audit`` reads the
        resolved document as its spec-consistency oracle (the
        "Contradicts cited spec" critical flag); ``primer-review`` reads
        it for the "Duplicates formal spec section" critical flag.

        Type-and-emptiness only at parse time (non-empty string;
        whitespace-only normalizes to ``None``) — file existence is a
        resolution-time concern (BRIEF parsing must not depend on cwd).
        The activation contract lives in ``anvil/skills/primer/SKILL.md``
        §"Spec-ref contract": **absent** → the spec-consistency tier is
        silent/off and both critics record a ``major`` finding
        recommending the operator declare it; **declared-but-missing** →
        the tier activates but degrades gracefully (a ``major`` finding,
        never a crash, never a false critical flag), mirroring the
        ``customer:`` (#429) / ``voice:`` (#461) declared-but-missing
        posture.

        Example::

            documents:
              - slug: botho-from-the-basics
                artifact_type: primer
                spec_ref: ../whitepaper/whitepaper.5/whitepaper.md
    code_ref
        Optional companion-input path/glob for the ``anvil:spec`` skill
        (issue #697/#706): the **implementation** a normative spec
        describes and must stay truthful to. The mirror image of
        primer's ``spec_ref`` — where a primer teaches *alongside* a
        formal spec, a spec is normatively describing an *implementation*.
        Resolved project-root-first then consumer-root by
        :func:`resolve_code_ref` (structurally identical to
        :func:`resolve_spec_ref`). ``spec-audit`` reads the resolved
        implementation as its consistency oracle; the three-way audit
        verdict ("spec claim contradicts implementation") lands in Phase 2
        (#707).

        Type-and-emptiness only at parse time (non-empty string;
        whitespace-only normalizes to ``None``) — file existence is a
        resolution-time concern. The activation contract lives in
        ``anvil/skills/spec/SKILL.md`` §"Code-ref contract": **absent**
        → the consistency tier is silent/off and both critics record a
        ``major`` finding recommending the operator declare it;
        **declared-but-missing** → the tier activates but degrades
        gracefully (a ``major`` finding, never a crash, never a false
        critical flag), mirroring the ``spec_ref`` (#686) posture.

        Example::

            documents:
              - slug: botho-consensus-spec
                artifact_type: spec
                code_ref: ../../src/**/*.rs
    recommendation_target
        Optional per-document declaration of the memo's decision
        posture (issue #348, project-first fallback via issue #837):
        one of ``"invest"``, ``"pass"``, ``"conditional"``, or
        ``"undecided"``. Mirrors the thread-level ``<thread>/BRIEF.md``
        informal frontmatter key of the same name (see
        :func:`load_recommendation_target`) so a project migrated to
        the canonical post-#295/#296 project-first layout — which has
        no thread-level ``BRIEF.md`` at all — has a typed, on-disk
        place to declare the same signal. :func:`load_recommendation_target_resolved`
        is the dual-surface reader: it prefers a thread-level value
        when present (byte-identical legacy behavior) and falls back
        to this per-document field otherwise.

        Deliberately **lenient**, the one exception to
        ``BriefDocument``'s otherwise-STRICT per-field validation: an
        unrecognized value (a typo like ``"Undecided"``, ``"tbd"``, a
        non-string type) normalizes to ``None`` at parse time rather
        than raising — mirroring the thread-level surface's closed-set
        contract exactly, since this field is operator-declared
        calibration posture, not structural configuration.

        Example::

            documents:
              - slug: investment-memo
                artifact_type: investment-memo
                recommendation_target: undecided
    voice_corpus_exclude
        Optional per-document declaration of extra path/glob strings to
        drop from this document's resolved ``voice.corpus`` when
        **this** document is under review (issue #890). Companion to the
        *automatic* published-self exclusion that
        :func:`resolve_voice_docs` applies when called with
        ``exclude_self_slug=<this slug>`` — that automatic rule infers a
        thread's own published form from its slug (a filename stem
        equal to the slug, optionally after stripping a leading
        ``YYYY-MM-DD-`` date prefix) and cannot cover every consumer's
        publish-path convention (a title-cased filename, a transliterated
        slug, a nested `index.md`-per-post layout, …). This field is the
        documented escape hatch for exactly those cases: declare the
        published artifact's actual path/glob here and it is unioned
        with the automatic exclusion (deduped) rather than replacing it.

        Same on-disk shape as :attr:`spec_ref` / :attr:`code_ref`: a
        scalar string (normalized to a single-element list) or a YAML
        list of path/glob strings. Resolved the same way as the
        ``voice.corpus`` glob itself — project-root first, then
        consumer-root; absolute paths bypass the walk. A pattern that
        resolves to nothing is a silent no-op (there is nothing to
        exclude), never an error — this field only ever narrows an
        already-resolved corpus, it cannot widen or break it.

        Example (the consumer's blog archive keeps published posts under
        a nested per-slug directory the automatic date-prefix rule
        cannot infer)::

            documents:
              - slug: the-loop-is-the-unit
                artifact_type: essay
                voice_corpus_exclude: website/src/notes/posts/the-loop-is-the-unit/index.tsx
    """

    model_config = ConfigDict(extra="forbid")

    slug: str = Field(..., min_length=1)
    # Union keeps registered values as enum members (strict union match
    # on an already-normalized ArtifactType instance) while letting
    # consumer-declared types (issue #394) pass through as plain str.
    # _normalize_documents always routes raw input through
    # _validate_artifact_type first — this field never sees a free
    # string.
    artifact_type: Union[ArtifactType, str] = Field(...)
    target_length: Optional[TargetLengthRange] = Field(default=None)
    target_length_overrides: Optional[TargetLengthOverrides] = Field(default=None)
    rubric_overrides: Optional[RubricOverrides] = Field(default=None)
    render_engine: Optional[
        Literal["weasyprint", "xelatex", "wkhtmltopdf"]
    ] = Field(default=None)
    render_template: Optional[str] = Field(default=None)
    render_lua_filters: Optional[List[str]] = Field(default=None)
    render_metadata: Optional[Dict[str, str]] = Field(default=None)
    latex_header_includes: Optional[str] = Field(default=None)
    max_iterations: Optional[int] = Field(default=None)
    iteration_cap_rationale: Optional[str] = Field(default=None)
    web_search: Optional[bool] = Field(default=None)
    # spec_ref / code_ref accept a scalar string OR a YAML list of
    # path/glob strings on disk (issue #719); the per-field validators
    # (_validate_spec_ref / _validate_code_ref) normalize the scalar form
    # to a single-element list, so downstream code always sees a list.
    spec_ref: Optional[List[str]] = Field(default=None)
    code_ref: Optional[List[str]] = Field(default=None)
    # Hardcoded Literal (not referencing _RECOGNIZED_RECOMMENDATION_TARGETS,
    # defined later in this module in the thread-level BRIEF helpers
    # section) mirrors the render_engine field's precedent above — the
    # constant is only consumed by _validate_recommendation_target, which
    # is called at load_project_brief() runtime, long after module import
    # completes, so no forward-reference reordering is needed.
    recommendation_target: Optional[
        Literal["invest", "pass", "conditional", "undecided"]
    ] = Field(default=None)
    # Same scalar-or-list normalization as spec_ref / code_ref (issue #890),
    # via _validate_voice_corpus_exclude / _validate_companion_ref.
    voice_corpus_exclude: Optional[List[str]] = Field(default=None)


class AiByline(BaseModel):
    """Parsed optional top-level ``ai_byline:`` block (issue #941).

    The opt-in AI-authorship disclosure contract: a project declares this
    block to have anvil append a short, configurable provenance line to
    its rendered artifacts declaring AI-assisted authorship. Distinct
    from — and unrelated to — the intrinsic token-level model-output
    watermark: this is a detachable, discretionary, honest-actor
    transparency mechanism entirely in the consumer's control, and it is
    also distinct from the ``corpus:`` claim-provenance tier (#597),
    which verifies substance, not authorship. See
    ``anvil/lib/snippets/provenance.md`` for the boundary discussion.

    On-disk shape (every sub-key optional except that ``enabled`` must be
    a bool when present; the block itself optional)::

        ai_byline:
          enabled: true                 # default false — strictly opt-in
          text: "Drafted with AI assistance ({model}) and edited by Robb."
          placement: byline             # byline | footer | frontmatter-only
          model_name: Claude            # substitutes {model} in text

    **No ``ai_byline:`` block, or ``enabled: false`` (the default when the
    key is absent) → byte-identical behavior** — no line is ever
    rendered. See :func:`resolve_ai_byline` for the BRIEF → rendered-
    string resolution consumed by lifecycle commands.

    Unknown sub-keys are **preserved verbatim** under ``unknown_keys``
    (the same lenient inner-block posture as :class:`VoiceDocs`) so a
    forward-shipped sub-key can land in BRIEF.md ahead of loader support
    without breaking existing consumers. The loader warns via
    ``warnings.warn`` so the typo case stays visible.
    """

    model_config = ConfigDict(extra="forbid")

    enabled: bool = Field(
        default=False,
        description=(
            "Strictly opt-in (issue #941): the byline is only ever "
            "rendered when this is explicitly true. Absent block or "
            "absent key both default to False."
        ),
    )
    text: Optional[str] = Field(
        None,
        description=(
            "Custom override for the rendered line. May embed literal "
            "`{model}` / `{date}` placeholders (see "
            "`anvil.lib.ai_byline.render_byline`). `None`/absent falls "
            "back to the module default text."
        ),
    )
    placement: Optional[str] = Field(
        None,
        description=(
            "Where the line lands in the rendered artifact: `byline` "
            "(near the title, the default), `footer` (end of the "
            "document / back matter), or `frontmatter-only` (metadata "
            "only, no visible line). Validated against "
            "`anvil.lib.ai_byline.VALID_PLACEMENTS`."
        ),
    )
    model_name: Optional[str] = Field(
        None,
        description=(
            "Optional model/tool name substituted for a `{model}` "
            "placeholder in `text`. Purely descriptive metadata — never "
            "validated against a known-model list."
        ),
    )
    unknown_keys: Dict[str, Any] = Field(
        default_factory=dict,
        description=(
            "Forward-compat passthrough: any sub-keys the loader does "
            "not recognize land here verbatim. Surfaced via "
            "``warnings.warn`` at parse time."
        ),
    )


class ProjectBrief(BaseModel):
    """The parsed project-level ``BRIEF.md`` frontmatter.

    Attributes
    ----------
    project
        Project name. Required, non-empty. Surfaced for human reference
        (printed in reports, headers, audit logs); not used as a
        filesystem key.
    audience
        Free-string descriptors of the project audience. The BRIEF
        author lists them in priority order (primary first); the
        loader does NOT enforce any ordering convention.

        Two on-disk shapes are accepted (issue #546): a YAML list of
        strings (the canonical flat form — drafter controls the
        order), OR a mapping with role-keyed sub-keys (``primary``,
        ``secondary``, ``tertiary``, with unknown roles preserved as
        a forward-compat surface) whose values are strings or lists
        of strings. The dict shape is flattened in role-precedence
        order — ``primary`` first, ``secondary`` next, then
        ``tertiary``, then any unknown sub-keys in YAML insertion
        order — so this field remains ``List[str]`` regardless of the
        on-disk shape. See :func:`_normalize_audience`.
    hard_rules
        Cross-document discipline rules that apply to every document in
        the project. Free strings; the reviewer treats each as a
        critical-check candidate per existing memo-review §"hard rules"
        machinery. Allowed to be empty.
    documents
        Per-document entries. Must be non-empty (a BRIEF with an empty
        documents list does NOT trigger project-brief layout per
        ``project_discovery.has_project_brief`` — this loader only
        accepts BRIEFs that already pass the discovery gate). Slugs are
        guaranteed unique by the parser.
    theme
        Optional brand-theme name (issue #322). When set, the per-skill
        asset resolvers (template + stylesheet + accent) consult
        ``<consumer>/.anvil/themes/<theme>/`` as a precedence tier
        between the consumer single-tenant override and the framework
        default. Free string — theme names are consumer-defined; no
        enum validation is enforced. A name pointing to a missing theme
        directory is tolerated (the resolver falls through to the next
        tier silently).
    voice
        Optional voice/persona grounding-docs block (issue #461). When
        set, the drafter loads the declared docs in the documented
        order (values → style_guide → vocabulary → corpus exemplars)
        and the reviewer calibrates its owned dimension against them
        per ``anvil/lib/snippets/voice_grounding.md``. Absent →
        byte-identical behavior (the #428/#452 activation pattern).
        Path resolution is deferred to :func:`resolve_voice_docs`.
    corpus
        Optional list of read-only ground-truth corpus directory paths
        (issue #597). Distinct from ``voice.corpus`` (a single glob of
        author-persona *published* exemplars): this top-level ``corpus:``
        declares **factual** ground truth — interview transcripts, family
        letters, engagement notes — that the per-version ``provenance.md``
        claim→source map cites and the corpus-audit critic verifies
        against per ``anvil/lib/snippets/provenance.md``. ``None`` = tier
        inactive (absent key, ``null``, or empty list) → byte-identical
        behavior. Path resolution is deferred to
        :func:`resolve_corpus_dirs`.
    quarantine
        Optional list of **literal** figure/range tokens (issue #914) that
        a ``hard_rules`` entry forbids porting from the project's private
        artifacts (e.g. a memo) into its customer-facing siblings (e.g. a
        deck) — the classic shape is a superseded or unverified number
        (``"$400M"`` when the correct disclosure is ``"$256M"``, or an
        unverified ``"20-40%"`` spread). Distinct from ``hard_rules``:
        ``hard_rules`` stays free-form discipline prose for the reviewer
        (``"cite $256M net, not $400M gross"``); ``quarantine`` is the
        machine-matchable token surface a lint can compare against —
        the same split ``corpus`` already draws against ``voice.corpus``
        (structured ground truth vs. prose guidance).

        Consumed by ``anvil/lib/parity.py``'s deck↔memo parity lint via
        the ``quarantine_corpus`` kwarg on ``lint_source()``: a listed
        token found only in the memo body is reframed away from the
        "should you port this?" promotion (``side="only_in_memo_quarantined"``)
        rather than silently dropped, and the SAME token found anywhere
        in the deck body raises a new ``side="quarantine_violation"``
        finding — a real hard-rule violation. Entries are literal
        strings; derived forms (e.g. a quarantined ``"20-40%"`` rate
        reappearing as its arithmetic product) are NOT detected — see
        the "Quarantine corpus" section of ``parity.py``'s module
        docstring. Defaults to an empty list (tier inactive) →
        byte-identical behavior for every BRIEF that does not declare
        this key.
    ai_byline
        Optional AI-authorship disclosure block (issue #941). Strictly
        opt-in: absent block, or a block with ``enabled: false`` (the
        default), leaves every rendered artifact byte-identical to a
        pre-#941 install — no line is ever rendered. When
        ``enabled: true``, ``resolve_ai_byline`` computes the final
        rendered line (custom ``text`` template or the module default)
        and the artifact-class drafter/renderer commands splice it into
        the rendered deliverable at the declared ``placement``. Distinct
        from ``corpus`` (substance-verification provenance) and from the
        intrinsic model-output watermark — this is a detachable,
        editorial disclosure choice, not a tamper-resistant mechanism.
    """

    model_config = ConfigDict(extra="forbid")

    project: str = Field(..., min_length=1)
    audience: List[str] = Field(default_factory=list)
    hard_rules: List[str] = Field(default_factory=list)
    documents: List[BriefDocument] = Field(..., min_length=1)
    theme: Optional[str] = Field(default=None)
    voice: Optional[VoiceDocs] = Field(default=None)
    corpus: Optional[List[str]] = Field(default=None)
    ai_byline: Optional[AiByline] = Field(default=None)
    quarantine: List[str] = Field(default_factory=list)

    def document_for_slug(self, slug: str) -> Optional[BriefDocument]:
        """Return the ``BriefDocument`` whose ``slug`` matches, or ``None``.

        Convenience accessor for the overlay selector (#286) and the
        rubric-overrides reader: given a thread's slug, look up its
        BRIEF entry to read the ``artifact_type``, ``target_length``,
        ``target_length_overrides``, and ``rubric_overrides`` fields.
        """
        for doc in self.documents:
            if doc.slug == slug:
                return doc
        return None
