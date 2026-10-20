"""Companion-input ref resolution: spec_ref (#686) + code_ref (#697/#706) (issue #1121 split).

Part of the ``anvil.lib.project_brief`` package — see the package
``__init__.py`` docstring for the full module. This submodule owns the
shared companion-ref element resolver (:func:`_resolve_companion_element`)
and both companion-input resolvers built on it: :func:`resolve_spec_ref`
(primer's optional spec-consistency companion input) and
:func:`resolve_code_ref` (spec's optional implementation-consistency
companion input, the mirror image of ``spec_ref``).

Split from the pre-#1121 monolithic ``anvil/lib/project_brief.py`` along its
existing "Primer spec-ref resolution" / "Spec code-ref resolution" section
boundaries (grouped into one module — ``resolve_code_ref`` is a documented
mirror of ``resolve_spec_ref`` and both share ``_resolve_companion_element``).
No behavior change.
"""

from __future__ import annotations

import glob as _glob
from pathlib import Path
from typing import List, Literal, Optional, Tuple

from pydantic import BaseModel, ConfigDict, Field

from anvil.lib.project_brief.fields import CompanionRefTypeError
from anvil.lib.project_brief.loader import load_project_brief
from anvil.lib.theme import find_consumer_root

# ---------------------------------------------------------------------------
# Primer spec-ref resolution (issue #686)
# ---------------------------------------------------------------------------


def _companion_ref_is_glob(s: str) -> bool:
    """True when a companion-ref declaration contains glob metacharacters."""
    return any(ch in s for ch in "*?[")


def _resolve_companion_element(
    element: str,
    roots: List[Tuple[str, Path]],
) -> Tuple[List[str], Optional[str]]:
    """Resolve ONE companion-ref path/glob declaration (issue #719).

    The per-element resolution primitive shared by :func:`resolve_spec_ref`
    and :func:`resolve_code_ref`, so a list declaration loops this once per
    element (issue #719). Preserves the pre-#719 single-declaration
    behavior exactly for the one-element case:

    - Absolute declarations bypass the root walk (glob via
      :func:`glob.glob`, plain path via a direct ``is_file()`` check).
    - Relative declarations walk ``roots`` in order (project-root first,
      then consumer-root); the first root with ≥1 match wins.
    - Glob matches are sorted; a plain path resolves to its single file.

    Returns ``(matches, source)`` — ``matches`` is the (possibly empty)
    sorted list of absolute path strings for this element, and ``source``
    is which root it resolved against (``None`` when it matched nothing).
    """
    declared_path = Path(element)
    if declared_path.is_absolute():
        if _companion_ref_is_glob(element):
            try:
                matches = sorted(
                    p
                    for p in _glob.glob(element, recursive=True)
                    if Path(p).is_file()
                )
            except (OSError, ValueError):
                matches = []
            if matches:
                return matches, "absolute"
            return [], None
        if declared_path.is_file():
            return [str(declared_path)], "absolute"
        return [], None

    for source, root in roots:
        if _companion_ref_is_glob(element):
            try:
                matches = sorted(
                    str(p.resolve())
                    for p in root.glob(element)
                    if p.is_file()
                )
            except (OSError, ValueError):
                matches = []
            if matches:
                return matches, source
        else:
            candidate = root / declared_path
            if candidate.is_file():
                return [str(candidate.resolve())], source
    return [], None


class ResolvedSpecRef(BaseModel):
    """One resolved ``spec_ref`` entry from :func:`resolve_spec_ref` (issue #686).

    The companion-input analog of :class:`ResolvedVoiceDoc`, for the
    ``anvil:primer`` skill: the formal sibling artifact (whitepaper /
    spec / standard / API doc) a primer teaches alongside.
    ``primer-audit`` reads the resolved document as its spec-consistency
    oracle; ``primer-review`` reads it for the duplication sweep.

    Missing-file results are carried as a **structured** ``missing:
    true`` entry — resolution never raises on absence. A ``missing:
    true`` entry ACTIVATES the spec-consistency tier and is the primer
    critics' signal to surface a ``major`` finding (broken declaration)
    while degrading gracefully (no spec cross-check, no false critical
    flag) — the same defect-to-surface posture as the ``voice:`` /
    ``customer:`` declared-but-missing contract.
    """

    model_config = ConfigDict(extra="forbid")

    declared: List[str] = Field(
        default_factory=list,
        description=(
            "The verbatim path / glob string(s) from the BRIEF, in "
            "declaration order (issue #719). A scalar BRIEF value "
            "normalizes to a single-element list. For a malformed "
            "declaration this carries the type-error message text."
        ),
    )
    paths: List[str] = Field(
        default_factory=list,
        description=(
            "Absolute path string(s) of the resolved spec document(s). "
            "The deduped, declaration-ordered union of every declared "
            "element's matches (each element: single path or sorted glob "
            "matches). Empty when ``missing``."
        ),
    )
    missing: bool = Field(
        ...,
        description=(
            "True only when ZERO declared elements resolved to any file "
            "(nothing usable at all) — byte-identical to the single-string "
            "all-missing semantics. A PARTIAL miss (some elements resolve, "
            "some don't) is ``missing=False`` with a non-empty "
            "``unresolved`` (active-with-warning). When ``missing``, the "
            "tier still ACTIVATES; the primer critics surface a ``major`` "
            "finding and skip the cross-check."
        ),
    )
    unresolved: List[str] = Field(
        default_factory=list,
        description=(
            "Declared element strings that matched zero files, in "
            "declaration order (issue #719). Empty for a fully-resolving "
            "declaration (and always empty for a scalar). Non-empty on a "
            "PARTIAL miss (``missing=False``): the sweep runs against "
            "``paths`` while the primer critics add a ``major`` finding "
            "naming these entries."
        ),
    )
    source: Optional[Literal["project", "consumer", "absolute"]] = Field(
        None,
        description=(
            "Which root the FIRST resolved element resolved against: "
            "``project`` (project-root hit, first precedence), "
            "``consumer`` (consumer-root fallback via the ``.anvil/`` "
            "marker walk), ``absolute`` (declared as an absolute path). "
            "``None`` when ``missing``."
        ),
    )


def resolve_spec_ref(
    project_dir: Path,
    slug: str,
    consumer_root: Optional[Path] = None,
) -> Optional[ResolvedSpecRef]:
    """Resolve a primer document's ``spec_ref`` to on-disk path(s) (issue #686).

    The companion-input resolution helper for the ``anvil:primer`` skill.
    Reads ``<project_dir>/BRIEF.md`` leniently, looks up the document by
    ``slug``, and — when that document declares a ``spec_ref`` — resolves
    it **project-root first, then consumer-root** (absolute paths bypass
    the walk), the same walk the ``voice:`` docs and ``report``'s
    ``prior_reports[]`` paths use. A ``spec_ref`` may be a plain path (the
    common case) or a glob; glob matches are sorted and the first root
    with ≥1 match wins.

    **List declarations (issue #719).** ``spec_ref`` may declare a YAML
    list of independent path/glob strings (multi-file formal siblings that
    don't share a common glob root). Each element resolves independently
    (its own root walk); the results are unioned in **declaration order**
    and **deduped** (first-seen order preserved) into ``.paths``. Per-
    element accounting:

    - ALL elements resolve → ``missing=False``, ``unresolved=[]``.
    - SOME resolve, some don't (partial miss) → ``missing=False``,
      ``unresolved`` = the non-matching declared strings (declaration
      order); the sweep still runs against ``.paths`` and the primer
      critics add a ``major`` finding naming the unresolved entries.
    - ZERO resolve → ``missing=True`` (byte-identical to today's single-
      string all-missing case).

    A scalar declaration is the one-element case: ``unresolved`` is always
    empty (a lone bad path is the ZERO-resolve → ``missing=True`` case).

    **Never raises on absence.** A declared-but-missing ``spec_ref``
    comes back as a structured ``missing: true`` :class:`ResolvedSpecRef`
    — the tier still activates and the primer critics surface a ``major``
    finding, degrading gracefully (no crash, no false critical flag; the
    ``customer_context.py`` / ``resolve_voice_docs`` posture).

    A **malformed** ``spec_ref`` (declared but the wrong type — e.g. a
    YAML list, int, or dict) is NOT the inactive path (issue #718): it is
    a declared-but-broken declaration, so it comes back as a structured
    ``missing: true`` :class:`ResolvedSpecRef` (tier ACTIVE, ``major``
    finding) — the same posture as a declared-but-unresolvable path. The
    clear type error from :func:`_validate_spec_ref` is preserved in the
    ``declared`` field so it reaches the operator instead of being
    silently swallowed.

    Returns
    -------
    Optional[ResolvedSpecRef]
        A resolved entry when the document declares a ``spec_ref`` (or
        declares one with the wrong type — a ``missing: true`` entry);
        ``None`` when the tier is **INACTIVE**: no BRIEF, malformed /
        structurally invalid BRIEF (lenient swallow, mirroring
        :func:`resolve_voice_docs`), no matching document for ``slug``,
        or that document declares no ``spec_ref``. Callers branch on
        ``if resolved is None:`` for the byte-identical inactive path.
    """
    try:
        brief = load_project_brief(project_dir, consumer_root=consumer_root)
    except CompanionRefTypeError as exc:
        # A companion-ref field is declared but the wrong type (issue
        # #718). If it is a malformed ``spec_ref``, this is a
        # declared-but-BROKEN declaration — it must ACTIVATE the tier and
        # surface a ``major`` finding via the existing ``missing: true``
        # path, NOT silently swallow to ``None`` (the "undeclared → tier
        # inactive" path). A malformed *other* companion field
        # (``code_ref``) is unrelated to this resolver; swallow it to
        # ``None`` exactly as any other BRIEF-parse failure below.
        if exc.field == "spec_ref":
            return ResolvedSpecRef(declared=[str(exc)], missing=True)
        return None
    except ValueError:
        return None
    if brief is None:
        return None

    doc = brief.document_for_slug(slug)
    if doc is None or doc.spec_ref is None:
        return None

    declared = doc.spec_ref  # normalized to List[str] by _validate_spec_ref

    roots: List[Tuple[str, Path]] = [("project", Path(project_dir))]
    resolved_consumer = (
        Path(consumer_root)
        if consumer_root is not None
        else find_consumer_root(Path(project_dir))
    )
    if resolved_consumer is not None:
        roots.append(("consumer", resolved_consumer))

    # Resolve each declared element independently, then union the results
    # in declaration order with dedup (issue #719). A single-element list
    # (the scalar-normalized case) reduces to today's behavior exactly.
    union_paths: List[str] = []
    seen: set = set()
    unresolved: List[str] = []
    first_source: Optional[str] = None
    for element in declared:
        matches, source = _resolve_companion_element(element, roots)
        if not matches:
            unresolved.append(element)
            continue
        if first_source is None:
            first_source = source
        for m in matches:
            if m not in seen:
                seen.add(m)
                union_paths.append(m)

    if not union_paths:
        # ZERO elements resolved — the whole declaration is unusable
        # (byte-identical to today's single-string all-missing case).
        return ResolvedSpecRef(declared=declared, missing=True)
    return ResolvedSpecRef(
        declared=declared,
        paths=union_paths,
        missing=False,
        unresolved=unresolved,
        source=first_source,
    )


# ---------------------------------------------------------------------------
# Spec code-ref resolution (issue #697/#706)
# ---------------------------------------------------------------------------
#
# DESIGN DECISION — standalone mirror, NOT a generalized resolver.
#
# ``code_ref`` (the implementation an ``anvil:spec`` normatively describes)
# is structurally identical to primer's ``spec_ref`` (the formal sibling a
# primer teaches alongside): a freeform path/glob, resolved project-root-
# first then consumer-root, never raising on absence, carrying a
# ``missing: true`` entry for a declared-but-unresolvable path. It would be
# tempting to fold both into a single ``resolve_companion_ref(kind, ...)``.
#
# We deliberately ship a STANDALONE mirror (``resolve_code_ref`` /
# ``ResolvedCodeRef``) rather than generalizing, for three reasons:
#
#   1. **Zero blast radius to primer.** Generalizing would touch
#      ``resolve_spec_ref``'s call sites across five shipped primer command
#      docs. A Phase-1 skeleton PR should not risk primer's shipped
#      behavior for a DRY win.
#   2. **CLAUDE.md convention: "skill-local first, lib promotion later."**
#      The extraction pattern is "wait for the SECOND consumer before
#      generalizing." ``spec_ref`` and ``code_ref`` are the first two
#      companion-ref consumers; a THIRD plausible consumer is the right
#      trigger to hoist a shared ``resolve_companion_ref`` — not the second.
#   3. **Distinct semantics downstream.** ``spec_ref`` feeds a binary
#      "contradicts / doesn't" audit; ``code_ref`` feeds a THREE-way verdict
#      (spec-wrong / code-wrong / intentional-gap; Phase 2 / #707). Keeping
#      the resolvers separate leaves room for the two to diverge in what
#      they resolve (e.g. code_ref may later want a language-aware walk)
#      without a shared-signature negotiation.
#
# The two resolvers share the SHAPE, not the code path — the small amount
# of glob-walk duplication below is the accepted cost of the isolation. If
# a third companion-ref consumer appears, that is the signal to promote a
# shared ``_resolve_companion_ref_path`` helper both call.


class ResolvedCodeRef(BaseModel):
    """One resolved ``code_ref`` entry from :func:`resolve_code_ref` (issue #706).

    The companion-input analog of :class:`ResolvedSpecRef`, for the
    ``anvil:spec`` skill: the **implementation** (source tree, wire-format
    reference, consensus-rule code) that a normative spec describes and
    must stay truthful to. ``spec-audit`` reads the resolved
    implementation as its consistency oracle; the full three-way verdict
    ("spec claim contradicts implementation" — spec-wrong / code-wrong /
    intentional-gap) lands in Phase 2 (#707).

    Missing-file results are carried as a **structured** ``missing:
    true`` entry — resolution never raises on absence. A ``missing:
    true`` entry ACTIVATES the consistency tier and is the spec critics'
    signal to surface a ``major`` finding (broken declaration) while
    degrading gracefully (no cross-check, no false critical flag) — the
    same defect-to-surface posture as ``spec_ref``.
    """

    model_config = ConfigDict(extra="forbid")

    declared: List[str] = Field(
        default_factory=list,
        description=(
            "The verbatim path / glob string(s) from the BRIEF, in "
            "declaration order (issue #719). A scalar BRIEF value "
            "normalizes to a single-element list. For a malformed "
            "declaration this carries the type-error message text."
        ),
    )
    paths: List[str] = Field(
        default_factory=list,
        description=(
            "Absolute path string(s) of the resolved implementation "
            "file(s). The deduped, declaration-ordered union of every "
            "declared element's matches (each element: single path or "
            "sorted glob matches). Empty when ``missing``."
        ),
    )
    missing: bool = Field(
        ...,
        description=(
            "True only when ZERO declared elements resolved to any file "
            "(nothing usable at all) — byte-identical to the single-string "
            "all-missing semantics. A PARTIAL miss (some elements resolve, "
            "some don't) is ``missing=False`` with a non-empty "
            "``unresolved`` (active-with-warning). When ``missing``, the "
            "tier still ACTIVATES; the spec critics surface a ``major`` "
            "finding and skip the cross-check."
        ),
    )
    unresolved: List[str] = Field(
        default_factory=list,
        description=(
            "Declared element strings that matched zero files, in "
            "declaration order (issue #719). Empty for a fully-resolving "
            "declaration (and always empty for a scalar). Non-empty on a "
            "PARTIAL miss (``missing=False``): the sweep runs against "
            "``paths`` while the spec critics add a ``major`` finding "
            "naming these entries."
        ),
    )
    source: Optional[Literal["project", "consumer", "absolute"]] = Field(
        None,
        description=(
            "Which root the FIRST resolved element resolved against: "
            "``project`` (project-root hit, first precedence), "
            "``consumer`` (consumer-root fallback via the ``.anvil/`` "
            "marker walk), ``absolute`` (declared as an absolute path). "
            "``None`` when ``missing``."
        ),
    )


def resolve_code_ref(
    project_dir: Path,
    slug: str,
    consumer_root: Optional[Path] = None,
) -> Optional[ResolvedCodeRef]:
    """Resolve a spec document's ``code_ref`` to on-disk path(s) (issue #706).

    The companion-input resolution helper for the ``anvil:spec`` skill —
    the mirror image of :func:`resolve_spec_ref`. Reads
    ``<project_dir>/BRIEF.md`` leniently, looks up the document by
    ``slug``, and — when that document declares a ``code_ref`` — resolves
    it **project-root first, then consumer-root** (absolute paths bypass
    the walk), the same walk ``spec_ref`` / the ``voice:`` docs use. A
    ``code_ref`` may be a plain path or a glob (the common case for a
    multi-file implementation, e.g. ``../../src/**/*.rs``); glob matches
    are sorted and the first root with ≥1 match wins.

    **List declarations (issue #719).** ``code_ref`` may declare a YAML
    list of independent path/glob strings — the natural shape for a
    multi-crate / multi-module implementation spanning non-contiguous
    roots (a normative spec's implementation is rarely one glob-contiguous
    tree). Each element resolves independently (its own root walk); the
    results are unioned in **declaration order** and **deduped** (first-
    seen order preserved) into ``.paths``. Per-element accounting:

    - ALL elements resolve → ``missing=False``, ``unresolved=[]``.
    - SOME resolve, some don't (partial miss) → ``missing=False``,
      ``unresolved`` = the non-matching declared strings (declaration
      order); the sweep still runs against ``.paths`` and the spec critics
      add a ``major`` finding naming the unresolved entries.
    - ZERO resolve → ``missing=True`` (byte-identical to today's single-
      string all-missing case).

    A scalar declaration is the one-element case: ``unresolved`` is always
    empty (a lone bad path is the ZERO-resolve → ``missing=True`` case).

    **Never raises on absence.** A declared-but-missing ``code_ref`` comes
    back as a structured ``missing: true`` :class:`ResolvedCodeRef` — the
    tier still activates and the spec critics surface a ``major`` finding,
    degrading gracefully (no crash, no false critical flag).

    A **malformed** ``code_ref`` (declared but the wrong type — e.g. a
    YAML list, int, or dict) is NOT the inactive path (issue #718): it is
    a declared-but-broken declaration, so it comes back as a structured
    ``missing: true`` :class:`ResolvedCodeRef` (tier ACTIVE, ``major``
    finding) — the same posture as a declared-but-unresolvable path. The
    clear type error from :func:`_validate_code_ref` is preserved in the
    ``declared`` field so it reaches the operator instead of being
    silently swallowed.

    Returns
    -------
    Optional[ResolvedCodeRef]
        A resolved entry when the document declares a ``code_ref`` (or
        declares one with the wrong type — a ``missing: true`` entry);
        ``None`` when the tier is **INACTIVE**: no BRIEF, malformed BRIEF
        (lenient swallow), no matching document for ``slug``, or that
        document declares no ``code_ref``. Callers branch on ``if
        resolved is None:`` for the byte-identical inactive path.
    """
    try:
        brief = load_project_brief(project_dir, consumer_root=consumer_root)
    except CompanionRefTypeError as exc:
        # A companion-ref field is declared but the wrong type (issue
        # #718). If it is a malformed ``code_ref``, this is a
        # declared-but-BROKEN declaration — it must ACTIVATE the tier and
        # surface a ``major`` finding via the existing ``missing: true``
        # path, NOT silently swallow to ``None`` (the "undeclared → tier
        # inactive" path). A malformed *other* companion field
        # (``spec_ref``) is unrelated to this resolver; swallow it to
        # ``None`` exactly as any other BRIEF-parse failure below.
        if exc.field == "code_ref":
            return ResolvedCodeRef(declared=[str(exc)], missing=True)
        return None
    except ValueError:
        return None
    if brief is None:
        return None

    doc = brief.document_for_slug(slug)
    if doc is None or doc.code_ref is None:
        return None

    declared = doc.code_ref  # normalized to List[str] by _validate_code_ref

    roots: List[Tuple[str, Path]] = [("project", Path(project_dir))]
    resolved_consumer = (
        Path(consumer_root)
        if consumer_root is not None
        else find_consumer_root(Path(project_dir))
    )
    if resolved_consumer is not None:
        roots.append(("consumer", resolved_consumer))

    # Resolve each declared element independently, then union the results
    # in declaration order with dedup (issue #719). A single-element list
    # (the scalar-normalized case) reduces to today's behavior exactly.
    union_paths: List[str] = []
    seen: set = set()
    unresolved: List[str] = []
    first_source: Optional[str] = None
    for element in declared:
        matches, source = _resolve_companion_element(element, roots)
        if not matches:
            unresolved.append(element)
            continue
        if first_source is None:
            first_source = source
        for m in matches:
            if m not in seen:
                seen.add(m)
                union_paths.append(m)

    if not union_paths:
        # ZERO elements resolved — the whole declaration is unusable
        # (byte-identical to today's single-string all-missing case).
        return ResolvedCodeRef(declared=declared, missing=True)
    return ResolvedCodeRef(
        declared=declared,
        paths=union_paths,
        missing=False,
        unresolved=unresolved,
        source=first_source,
    )
