"""Voice/persona grounding-docs resolution (issue #461) (issue #1121 split).

Part of the ``anvil.lib.project_brief`` package — see the package
``__init__.py`` docstring for the full module. This submodule owns the
voice-grounding-docs resolver (:func:`resolve_voice_docs`), the parallel
subject-voice tier (issue #598, :func:`resolve_subject_voice_docs`), the
standalone corpus-dirs resolver (:func:`resolve_corpus_dirs`), the AI-byline
resolver (issue #941, :func:`resolve_ai_byline`), and the rhetoric-rules
resolver (issue #468, :func:`resolve_rhetoric_rules`) — which reuses the
companion-ref element resolver from ``refs.py``.

Split from the pre-#1121 monolithic ``anvil/lib/project_brief.py`` along its
existing "Voice grounding-docs resolution" section boundary. No behavior
change.
"""

from __future__ import annotations

import glob as _glob
import re
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from pydantic import BaseModel, ConfigDict, Field

from anvil.lib.ai_byline import DEFAULT_PLACEMENT as DEFAULT_AI_BYLINE_PLACEMENT
from anvil.lib.ai_byline import render_byline as _render_ai_byline
from anvil.lib.project_brief.loader import load_project_brief
from anvil.lib.project_brief.models import (
    ResolvedCorpusDir,
    ResolvedSubjectVoice,
    ResolvedVoiceDoc,
)
from anvil.lib.project_brief.refs import _resolve_companion_element
from anvil.lib.project_brief.types import VOICE_DOC_KINDS
from anvil.lib.theme import find_consumer_root

# ---------------------------------------------------------------------------
# Voice grounding-docs resolution (issue #461)
# ---------------------------------------------------------------------------


def _resolve_voice_path(
    declared: str, kind: str, roots: List[Tuple[str, Path]]
) -> ResolvedVoiceDoc:
    """Resolve one non-corpus voice doc path against the root list.

    ``roots`` is the ordered ``[("project", <dir>), ("consumer",
    <dir>)]`` precedence list (consumer entry absent when no
    ``.anvil/`` marker exists). First hit wins. Absolute declared
    paths bypass the root walk entirely.
    """
    declared_path = Path(declared)
    if declared_path.is_absolute():
        if declared_path.is_file():
            return ResolvedVoiceDoc(
                kind=kind,
                declared=declared,
                paths=[str(declared_path)],
                missing=False,
                source="absolute",
            )
        return ResolvedVoiceDoc(kind=kind, declared=declared, missing=True)

    for source, root in roots:
        candidate = root / declared_path
        if candidate.is_file():
            return ResolvedVoiceDoc(
                kind=kind,
                declared=declared,
                paths=[str(candidate.resolve())],
                missing=False,
                source=source,
            )
    return ResolvedVoiceDoc(kind=kind, declared=declared, missing=True)


def _resolve_voice_corpus(
    declared: str,
    roots: List[Tuple[str, Path]],
    kind: str = "corpus",
) -> ResolvedVoiceDoc:
    """Resolve a corpus glob against the root list (first root with
    ≥1 match wins; matches sorted; zero matches everywhere = missing).

    ``kind`` selects the resolved entry's label — ``"corpus"`` for the
    author tier (issue #461), ``"subject_corpus"`` for a subject's spoken
    corpus (issue #598). The glob semantics are identical.
    """
    if Path(declared).is_absolute():
        try:
            matches = sorted(
                p
                for p in _glob.glob(declared, recursive=True)
                if Path(p).is_file()
            )
        except (OSError, ValueError):
            matches = []
        if matches:
            return ResolvedVoiceDoc(
                kind=kind,
                declared=declared,
                paths=matches,
                missing=False,
                source="absolute",
            )
        return ResolvedVoiceDoc(kind=kind, declared=declared, missing=True)

    for source, root in roots:
        try:
            matches = sorted(
                str(p.resolve()) for p in root.glob(declared) if p.is_file()
            )
        except (OSError, ValueError):
            matches = []
        if matches:
            return ResolvedVoiceDoc(
                kind=kind,
                declared=declared,
                paths=matches,
                missing=False,
                source=source,
            )
    return ResolvedVoiceDoc(kind=kind, declared=declared, missing=True)


# A published filename that carries a leading calendar-date prefix
# (``2026-05-27-the-loop-is-the-unit.tsx``) — the shape the rjwalters.info
# blog pipeline that seeded issue #461/#890 actually publishes under.
# Stripped before comparing a resolved corpus filename's stem to a
# thread's slug (see :func:`_infer_self_published_paths`).
_DATE_PREFIX_RE = re.compile(r"^\d{4}-\d{2}-\d{2}-")


def _infer_self_published_paths(paths: List[str], slug: str) -> List[str]:
    """Infer which resolved ``voice.corpus`` paths are ``slug``'s own
    published form (issue #890).

    A deliberately **narrow, high-precision** heuristic — false
    negatives (an un-inferred publish path a consumer must cover via
    :attr:`BriefDocument.voice_corpus_exclude`) are the acceptable
    failure mode here, false positives (excluding a *different*
    thread's legitimate exemplar) are not: dropping the wrong file
    would silently thin the calibration base for a reason no reviewer
    could audit.

    Matches a resolved path's filename **stem**, case-folded and with
    one optional leading ``YYYY-MM-DD-`` date prefix stripped, against
    ``slug`` (also case-folded) for an **exact** match — covering both
    the plain-slug filename convention (``the-loop-is-the-unit.tsx``,
    matching essay's own ``<slug>.md`` body-filename convention) and the
    dated-post convention (``2026-05-27-the-loop-is-the-unit.tsx``).
    Deliberately does NOT do substring/prefix/suffix matching (e.g.
    ``the-loop-is-the-unit-revisited`` must NOT match slug
    ``the-loop-is-the-unit``) — that would risk excluding an unrelated
    published post that merely shares a slug fragment.
    """
    slug_norm = slug.strip().lower()
    if not slug_norm:
        return []
    matches: List[str] = []
    for p in paths:
        stem = Path(p).stem.lower()
        if _DATE_PREFIX_RE.sub("", stem) == slug_norm:
            matches.append(p)
    return matches


def _apply_corpus_self_exclusion(
    entry: ResolvedVoiceDoc,
    slug: str,
    declared_exclude: List[str],
    roots: List[Tuple[str, Path]],
) -> ResolvedVoiceDoc:
    """Drop thread ``slug``'s own published form from a resolved
    ``voice.corpus`` entry (issue #890).

    Two exclusion sources, unioned and deduped (first reason wins when
    both would match the same path):

    1. **Automatic inference** — :func:`_infer_self_published_paths`.
    2. **Declared** ``BriefDocument.voice_corpus_exclude`` — each
       pattern resolved the same way as a ``spec_ref`` / ``code_ref``
       element (:func:`_resolve_companion_element`, same ``roots``),
       for publish-path shapes the automatic rule cannot infer.

    A fully inert no-op when neither source matches anything: returns
    ``entry`` unchanged (same object, no ``excluded``/``paths`` churn) —
    a project that never triggers either exclusion path sees
    byte-identical output.
    """
    reasons: Dict[str, str] = {}
    for p in _infer_self_published_paths(entry.paths, slug):
        reasons[p] = "published self (inferred from slug)"

    for pattern in declared_exclude:
        matches, _source = _resolve_companion_element(pattern, roots)
        for m in matches:
            if m in entry.paths and m not in reasons:
                reasons[m] = f"declared corpus_exclude: {pattern!r}"

    if not reasons:
        return entry

    remaining = [p for p in entry.paths if p not in reasons]
    return entry.model_copy(
        update={
            "paths": remaining,
            "excluded": sorted(reasons),
            "exclusion_reasons": reasons,
        }
    )


def resolve_voice_docs(
    project_dir: Path,
    consumer_root: Optional[Path] = None,
    *,
    exclude_self_slug: Optional[str] = None,
) -> List[ResolvedVoiceDoc]:
    """Resolve the project BRIEF's ``voice:`` block to on-disk paths (issue #461).

    The voice/persona grounding-docs resolution helper. Reads
    ``<project_dir>/BRIEF.md`` leniently, and when an active ``voice:``
    block is declared, resolves each declared doc in the documented
    load order — **values → style_guide → vocabulary → corpus** (the
    order the drafter consumes them per
    ``anvil/lib/snippets/voice_grounding.md``).

    Path resolution — **project root first, then consumer root** (the
    #322/#394 walk; first hit wins):

    1. ``<project_dir>/<declared>`` — a project ghostwriting in a
       different persona shadows the repo-level docs locally.
    2. ``<consumer_root>/<declared>`` — the common case: voice docs
       are persona-level repo-root artifacts (``STYLE_GUIDE.md``,
       ``VOCABULARY.md``, ``VALUES.md``, ``writing-corpus/``) shared
       across every project in the consumer repo. The consumer root
       is the directory carrying the ``.anvil/`` install marker,
       discovered via :func:`anvil.lib.theme.find_consumer_root`
       unless an explicit ``consumer_root`` override is supplied
       (test fixtures / callers that already know the root).

    Absolute declared paths are used as-is. The ``corpus`` value is a
    glob (``Path.glob`` semantics, ``**`` supported); matches are
    sorted; a root "hits" when the glob matches ≥1 file.

    **Git status is never consulted.** Resolution is purely
    filesystem-driven, so a ``.gitignored`` declared doc resolves and
    activates the tier *identically* to a committed one. This is the
    designed, tested posture behind **private voice grounding** (issue
    #577; ``anvil/lib/snippets/voice_grounding.md`` §"Private
    grounding"): a personal ``VALUES.local.md``-class doc can be
    gitignored to keep the source out of the repo while still grounding
    drafting and review. There is no special private code path here — a
    gitignored doc that is declared-but-missing surfaces the same
    ``major`` finding as any other missing declared doc.

    **Never raises on absence.** Missing-file results come back as
    structured ``missing: true`` entries — a broken declaration is a
    defect for the reviewer to surface (``major`` finding), not an
    opt-out and not a crash (the ``customer_context.py`` posture).

    Parameters
    ----------
    exclude_self_slug
        Optional (issue #890): the slug of the thread currently under
        review/draft. When supplied, the resolved ``corpus`` entry has
        that thread's own published form dropped from ``paths`` — the
        circular-calibration fix for reviewing a **revision of an
        already-published** note (the note's own prior published form
        would otherwise sit inside its own voice-fidelity calibration
        base). Two exclusion sources are unioned (deduped):

        1. **Automatic inference** (:func:`_infer_self_published_paths`)
           — a resolved corpus path whose filename stem, after
           optionally stripping one leading ``YYYY-MM-DD-`` date
           prefix, case-insensitively equals ``exclude_self_slug``.
        2. **Declared** ``BriefDocument.voice_corpus_exclude`` for the
           document matching ``exclude_self_slug`` (when the BRIEF
           declares one) — resolved the same way as a ``spec_ref`` /
           ``code_ref`` element, for publish-path shapes the automatic
           rule cannot infer.

        Dropped paths are recorded on the returned entry's ``excluded``
        / ``exclusion_reasons`` fields so a caller can surface the
        exclusion in its own audit trail (e.g. essay-review's
        ``_summary.md.voice_grounding.corpus_excluded``). ``None``
        (the default) is a **complete no-op** — every pre-#890 caller
        that never passes this kwarg gets byte-identical output, and
        even a caller that does pass it sees no change unless the
        corpus glob actually matches something excludable.
    consumer_root
        (unchanged) explicit consumer-root override for callers /
        tests that already know the root.

    Returns
    -------
    List[ResolvedVoiceDoc]
        One entry per **declared grounding-doc** sub-key, in load
        order. ``rhetoric_rules`` (issue #468) NEVER appears here — it
        is gate-side lint config resolved separately by
        :func:`resolve_rhetoric_rules`, keeping this return shape
        stable for existing drafter/reviewer consumers. Empty list
        when the tier is INACTIVE: no BRIEF, malformed / structurally
        invalid BRIEF (lenient swallow, mirroring
        :func:`load_rubric_overrides_for_slug`), no ``voice:`` block,
        or an empty block (``VoiceDocs.is_empty``). Callers branch on
        ``if not resolved:`` for the byte-identical inactive path.
    """
    try:
        brief = load_project_brief(project_dir, consumer_root=consumer_root)
    except ValueError:
        return []
    if brief is None or brief.voice is None or brief.voice.is_empty:
        return []

    roots: List[Tuple[str, Path]] = [("project", Path(project_dir))]
    resolved_consumer = (
        Path(consumer_root)
        if consumer_root is not None
        else find_consumer_root(Path(project_dir))
    )
    if resolved_consumer is not None:
        roots.append(("consumer", resolved_consumer))

    declared_exclude: List[str] = []
    if exclude_self_slug:
        self_doc = brief.document_for_slug(exclude_self_slug)
        if self_doc is not None and self_doc.voice_corpus_exclude:
            declared_exclude = list(self_doc.voice_corpus_exclude)

    out: List[ResolvedVoiceDoc] = []
    for kind in VOICE_DOC_KINDS:
        declared = getattr(brief.voice, kind)
        if declared is None:
            continue
        if kind == "corpus":
            entry = _resolve_voice_corpus(declared, roots)
            if exclude_self_slug and not entry.missing:
                entry = _apply_corpus_self_exclusion(
                    entry, exclude_self_slug, declared_exclude, roots
                )
            out.append(entry)
        else:
            out.append(_resolve_voice_path(declared, kind, roots))
    return out


def resolve_subject_voice_docs(
    project_dir: Path,
    consumer_root: Optional[Path] = None,
) -> List[ResolvedSubjectVoice]:
    """Resolve the BRIEF's ``voice.subjects`` tier to on-disk paths (issue #598).

    The subject-tier analog of :func:`resolve_voice_docs`. Reads
    ``<project_dir>/BRIEF.md`` leniently and, when a non-empty
    ``voice.subjects`` list is declared, resolves each speaker entry in
    **declared order**:

    - ``corpus`` — a glob of transcript files, resolved exactly like the
      author ``corpus`` (``Path.glob`` semantics, ``**`` supported;
      matches sorted; a root "hits" when ≥1 file matches).
    - ``voice_doc`` — an optional single path, resolved like a non-corpus
      author doc. ``None`` in the result when the entry declared no
      ``voice_doc``.

    Both resolve **project root first, then consumer root** (the same
    ``.anvil/`` marker walk as :func:`resolve_voice_docs`; absolute paths
    bypass the walk). Git status is never consulted — a ``.gitignored``
    transcript corpus resolves identically to a committed one (the
    private-grounding posture #577 documents for the author tier applies
    unchanged here).

    **Independent activation.** This resolver gates on
    :attr:`VoiceDocs.has_subjects`, NOT on :attr:`VoiceDocs.is_empty`:
    a subjects-only ``voice:`` block (no author-tier keys) resolves here
    while :func:`resolve_voice_docs` returns ``[]``. The two tiers do not
    depend on each other.

    **Never raises on absence.** A ``corpus`` glob matching nothing, or a
    declared-but-missing ``voice_doc``, comes back as a structured
    ``missing: true`` :class:`ResolvedVoiceDoc` — a defect for the
    reviewer to surface (``major`` finding), not a crash and not an
    opt-out (the author-tier posture).

    Returns
    -------
    List[ResolvedSubjectVoice]
        One entry per declared subject, in declared order. Empty list
        when the subject tier is INACTIVE: no BRIEF, malformed /
        structurally invalid BRIEF (lenient swallow, mirroring
        :func:`resolve_voice_docs`), no ``voice:`` block, or no
        (non-empty) ``subjects`` list. Callers branch on
        ``if not resolved:`` for the byte-identical inactive path.
    """
    try:
        brief = load_project_brief(project_dir, consumer_root=consumer_root)
    except ValueError:
        return []
    if brief is None or brief.voice is None or not brief.voice.has_subjects:
        return []

    roots: List[Tuple[str, Path]] = [("project", Path(project_dir))]
    resolved_consumer = (
        Path(consumer_root)
        if consumer_root is not None
        else find_consumer_root(Path(project_dir))
    )
    if resolved_consumer is not None:
        roots.append(("consumer", resolved_consumer))

    out: List[ResolvedSubjectVoice] = []
    for subject in brief.voice.subjects or []:
        corpus = _resolve_voice_corpus(subject.corpus, roots, kind="subject_corpus")
        voice_doc = (
            _resolve_voice_path(subject.voice_doc, "subject_voice_doc", roots)
            if subject.voice_doc is not None
            else None
        )
        out.append(
            ResolvedSubjectVoice(
                name=subject.name, corpus=corpus, voice_doc=voice_doc
            )
        )
    return out


def resolve_corpus_dirs(
    project_dir: Path,
    consumer_root: Optional[Path] = None,
) -> List[ResolvedCorpusDir]:
    """Resolve the BRIEF's top-level ``corpus:`` list to on-disk dirs (issue #597).

    The factual-ground-truth resolver — the substance-verification analog
    of :func:`resolve_voice_docs`, but resolving each declared path to a
    **directory** (an evidence base of transcripts / letters / notes)
    rather than a file or glob. Reads ``<project_dir>/BRIEF.md`` leniently
    and, when a non-empty ``corpus`` list is declared, resolves each
    declared path in **declared order**.

    Path resolution — **project root first, then consumer root** (the same
    ``.anvil/`` marker walk as :func:`resolve_voice_docs`; first hit wins):

    1. ``<project_dir>/<declared>`` — a project shadowing a repo-level
       corpus locally.
    2. ``<consumer_root>/<declared>`` — the common case: a project-level
       evidence base shared across every thread in the consumer repo. The
       consumer root carries the ``.anvil/`` install marker (discovered
       via :func:`anvil.lib.theme.find_consumer_root` unless an explicit
       ``consumer_root`` override is supplied).

    Absolute declared paths are used as-is (``source="absolute"``). A path
    "resolves" when it names an existing **directory** at a root — a file
    of the same name does not satisfy the corpus contract.

    **Git status is never consulted** — a ``.gitignored`` corpus directory
    resolves identically to a committed one (the private-grounding posture
    #577 documents for the voice tier applies here unchanged).

    **Never raises on absence.** A declared directory absent at every root
    comes back as a structured ``missing: true`` :class:`ResolvedCorpusDir`
    — a defect for the reviewer to surface (``major`` finding), not an
    opt-out and not a crash (the :func:`resolve_voice_docs` posture).

    Returns
    -------
    List[ResolvedCorpusDir]
        One entry per declared corpus path, in declared order. Empty list
        when the tier is INACTIVE: no BRIEF, malformed / structurally
        invalid BRIEF (lenient swallow, mirroring
        :func:`resolve_voice_docs`), no ``corpus:`` key, ``corpus: null``,
        or an empty list. Callers branch on ``if not resolved:`` for the
        byte-identical inactive path.
    """
    try:
        brief = load_project_brief(project_dir, consumer_root=consumer_root)
    except ValueError:
        return []
    if brief is None or not brief.corpus:
        return []

    roots: List[Tuple[str, Path]] = [("project", Path(project_dir))]
    resolved_consumer = (
        Path(consumer_root)
        if consumer_root is not None
        else find_consumer_root(Path(project_dir))
    )
    if resolved_consumer is not None:
        roots.append(("consumer", resolved_consumer))

    out: List[ResolvedCorpusDir] = []
    for declared in brief.corpus:
        out.append(_resolve_corpus_dir(declared, roots))
    return out


def _resolve_corpus_dir(
    declared: str, roots: List[Tuple[str, Path]]
) -> ResolvedCorpusDir:
    """Resolve one corpus directory path against the root list.

    ``roots`` is the ordered ``[("project", <dir>), ("consumer", <dir>)]``
    precedence list (consumer entry absent when no ``.anvil/`` marker
    exists). First root where the path names an existing directory wins.
    Absolute declared paths bypass the root walk entirely.
    """
    declared_path = Path(declared)
    if declared_path.is_absolute():
        if declared_path.is_dir():
            return ResolvedCorpusDir(
                declared=declared,
                path=str(declared_path.resolve()),
                missing=False,
                source="absolute",
            )
        return ResolvedCorpusDir(declared=declared, missing=True)

    for source, root in roots:
        candidate = root / declared_path
        if candidate.is_dir():
            return ResolvedCorpusDir(
                declared=declared,
                path=str(candidate.resolve()),
                missing=False,
                source=source,
            )
    return ResolvedCorpusDir(declared=declared, missing=True)


class ResolvedAiByline(BaseModel):
    """The active, fully-rendered result of :func:`resolve_ai_byline`
    (issue #941).

    Unlike :class:`ResolvedCorpusDir` / :class:`ResolvedVoiceDoc`, there
    is no filesystem resolution here — the byline tier's "resolution" is
    purely "is it active, and if so, what is the final string". A caller
    only ever gets an instance when the tier is active; the inactive
    case is ``None`` (see :func:`resolve_ai_byline`), never a struct with
    a false ``active`` flag — the same "callers branch on falsy" contract
    :func:`resolve_corpus_dirs` uses for its empty-list inactive case.
    """

    model_config = ConfigDict(extra="forbid")

    text: str = Field(
        ...,
        description=(
            "The fully-rendered byline line — the consumer's `text` "
            "template (with `{model}`/`{date}` substituted) or the "
            "module default. Ready to splice into a rendered artifact "
            "as-is."
        ),
    )
    placement: str = Field(
        ...,
        description=(
            "The resolved placement — the declared `placement:` value, "
            "or `anvil.lib.ai_byline.DEFAULT_PLACEMENT` when unset. "
            "Always one of `anvil.lib.ai_byline.VALID_PLACEMENTS`."
        ),
    )


def resolve_ai_byline(
    project_dir: Path,
    consumer_root: Optional[Path] = None,
    *,
    model_name: Optional[str] = None,
    date: Optional[str] = None,
) -> Optional[ResolvedAiByline]:
    """Resolve the BRIEF's top-level ``ai_byline:`` block to a rendered
    line (issue #941).

    Reads ``<project_dir>/BRIEF.md`` leniently. Returns ``None`` — the
    byte-identical inactive path — when: there is no BRIEF, the BRIEF is
    structurally invalid (lenient swallow, mirroring
    :func:`resolve_corpus_dirs` / :func:`resolve_voice_docs`), there is
    no ``ai_byline:`` key, or the block is present but
    ``enabled: false`` (the default). **Never raises.**

    When the tier is active, delegates the pure string-rendering to
    :func:`anvil.lib.ai_byline.render_byline` and returns a
    :class:`ResolvedAiByline` bundling the rendered text with the
    resolved placement (declared, or
    :data:`anvil.lib.ai_byline.DEFAULT_PLACEMENT` when unset).

    Parameters
    ----------
    project_dir
        Directory containing the project BRIEF.
    consumer_root
        Unused by this resolver directly (there is no path resolution
        against project/consumer roots — the byline has no filesystem
        component). Accepted for call-site symmetry with the other
        ``resolve_*`` helpers in this module and threaded through to
        :func:`load_project_brief`.
    model_name
        Optional caller-supplied override for ``{model}`` template
        interpolation. When ``None``, falls back to the BRIEF's declared
        ``ai_byline.model_name``.
    date
        Optional caller-supplied value for ``{date}`` template
        interpolation (callers typically pass the render timestamp; this
        resolver does not read the clock itself, keeping it
        deterministic and easily testable).

    Returns
    -------
    Optional[ResolvedAiByline]
        ``None`` when inactive; otherwise the rendered line + placement.
    """
    try:
        brief = load_project_brief(project_dir, consumer_root=consumer_root)
    except ValueError:
        return None
    if brief is None or brief.ai_byline is None or not brief.ai_byline.enabled:
        return None

    resolved_model_name = model_name if model_name is not None else brief.ai_byline.model_name
    text = _render_ai_byline(
        text=brief.ai_byline.text,
        model_name=resolved_model_name,
        date=date,
    )
    placement = brief.ai_byline.placement or DEFAULT_AI_BYLINE_PLACEMENT
    return ResolvedAiByline(text=text, placement=placement)


def resolve_rhetoric_rules(
    project_dir: Path,
    consumer_root: Optional[Path] = None,
) -> Optional[ResolvedVoiceDoc]:
    """Resolve the BRIEF's ``voice.rhetoric_rules`` JSON rule file (issue #468).

    The render-gate-side companion to :func:`resolve_voice_docs`:
    resolves the optional ``voice.rhetoric_rules`` sub-key — a path to
    a consumer **JSON rule file** for the advisory
    ``memo_rhetoric_lint`` gate check (issue #463;
    ``anvil/lib/rhetoric_lint.py``) — using the same project-root-
    first, consumer-root-fallback walk (absolute paths bypass the
    walk). The value is a plain file path, never a glob.

    Deliberately INDEPENDENT of the voice-grounding tier: this helper
    does NOT gate on ``VoiceDocs.is_empty`` — a ``rhetoric_rules``-only
    ``voice:`` block resolves here while :func:`resolve_voice_docs`
    still returns ``[]`` (the lint wiring activates without the
    judgment tier).

    **Never raises on absence.** A declared-but-missing file comes
    back as a structured ``missing: true`` entry; the caller
    (``memo-render`` step 4g) forwards the project-root-joined
    declared path to ``gate(..., rhetoric_rules_path=...)`` anyway, so
    ``lint_rhetoric``'s graceful-degrade emits the one warning finding
    naming the broken declaration ("a defect to surface, not an
    opt-out") with framework defaults still applied.

    Returns
    -------
    Optional[ResolvedVoiceDoc]
        A ``kind="rhetoric_rules"`` entry when the sub-key is
        declared; ``None`` when INACTIVE: no BRIEF, malformed /
        structurally invalid BRIEF (lenient swallow), no ``voice:``
        block, or no ``rhetoric_rules`` sub-key. ``None`` → the caller
        omits the kwarg for byte-identical defaults-only gate
        behavior.
    """
    try:
        brief = load_project_brief(project_dir, consumer_root=consumer_root)
    except ValueError:
        return None
    if (
        brief is None
        or brief.voice is None
        or brief.voice.rhetoric_rules is None
    ):
        return None

    roots: List[Tuple[str, Path]] = [("project", Path(project_dir))]
    resolved_consumer = (
        Path(consumer_root)
        if consumer_root is not None
        else find_consumer_root(Path(project_dir))
    )
    if resolved_consumer is not None:
        roots.append(("consumer", resolved_consumer))

    return _resolve_voice_path(
        brief.voice.rhetoric_rules, "rhetoric_rules", roots
    )
