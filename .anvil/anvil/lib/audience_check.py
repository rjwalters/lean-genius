"""Deterministic audience-fit pre-flight (issue #1322).

Sixth member of the deterministic-checks family (alongside
``anvil/lib/numeric_consistency.py``, ``anvil/lib/pending_marker.py``,
``anvil/lib/render_gate.py``, ``anvil/lib/marp_lint.py`` and
``anvil/lib/revise_consistency.py``).

The problem
-----------

A ``paper`` thread reached READY and then AUDITED at anvil 0.11.6 with
two classes of defect still in reader-facing prose, across four review
passes and two audit passes:

1. **Governance and process notes addressed to the project's operator,
   not the declared audience** — "No replay wave is authorized by this
   estimate", "subject to the operator's publication gate", "goal #39
   authorized the certificate campaign; goal #40 commissioned this
   manuscript". True, traceable, and compiling, so invisible to the
   audit; short, so dim 9 (read as a length check) passed them.
2. **Pointers a reader cannot follow** — repo-relative artifact paths in
   an "Artifacts and receipts" section with no ``\\href``/``\\url``,
   ``s3://`` buckets, and room-transcript message numbers into a private
   database.

Nothing compared a sentence's addressee against the BRIEF's declared
``audience``, and nothing looked for either pattern class.

What this module does
---------------------

A small, fixed vocabulary + pattern scan over the body (``main.tex`` and
its ``\\input``/``\\include`` children, or ``<slug>.md``), reporting three
rule classes:

- ``governance_vocabulary`` — authorization / commissioning statements,
  operator or maintainer gates and approvals, publication gates, budget
  and spend caps, internal goal/ticket/issue/board numbers (``goal #39``).
- ``private_locator`` — object-store URLs (``s3://``, ``gs://``),
  ``file://`` and private-network URLs, home-directory paths
  (``/Users/<name>/...``), and chat/room message numbers
  (``message 31994``).
- ``unlinked_artifact_path`` — a repo-relative file path named inside an
  artifacts / availability / receipts / supplementary-material section
  that is not wrapped in ``\\href``/``\\url`` (or a markdown link) and is
  not explicitly marked "not published" on the same line.

Severity follows the issue's split: ``major`` in the body, ``minor``
after ``\\appendix`` (or an "Appendix" heading). A suppressed hit is
recorded at ``nit``.

Verdict posture: ADVISORY (warn-only), like ``numeric_consistency``
-------------------------------------------------------------------

This is deliberately modeled on ``numeric_consistency.py``'s warn-only
posture, **not** on ``pending_marker.py``'s terminal gate. Whether a
sentence is addressed to the operator is a judgment call the vocabulary
only approximates ("authorized" can be ordinary prose in a paper about
access control; a human "operator" can be a legitimate study subject),
so the scan is evidence for the reviewer's audience-fit sub-rule
(``anvil/skills/paper/rubric.md`` §"Audience fit (dims 7 and 9)"), never
a replacement for it:

- The review carries **no critical flag** and owns **no rubric
  dimension** (its single ``Score`` is ``score=None``), so it never
  changes the aggregated total or forces ``Verdict.BLOCK``.
- Findings carry ``Finding.severity`` ``major`` (body) / ``minor``
  (appendix), which the reviser consumes like any other critic finding.
- The reviewer folds real hits into ``comments.md`` and the dim 7 / dim 9
  scores, and may raise an ordinary critical flag under the rubric's
  open-ended "any other issue that meets the standard" clause when the
  defect warrants it. No new specially-resolved ``CriticalFlag.type`` is
  introduced.

Suppression
-----------

``<!-- anvil-lint-disable: audience_check -->`` (markdown) or
``% anvil-lint-disable: audience_check`` (LaTeX) on the same line or the
line immediately above suppresses a hit. A suppressed hit is recorded at
``nit`` with a "suppressed" rationale (audit trail) and does not count
toward ``passed()``.

Declared audience and public repository URL
-------------------------------------------

Both are reporting aids and never change what is detected:

- The declared audience (:func:`load_declared_audience`) comes from the
  thread ``BRIEF.md`` frontmatter ``audience:`` key, else the first
  paragraph under an ``Audience`` / ``Target audience`` / ``Readership``
  heading, else the project-level ``BRIEF.md`` ``audience:``. It is quoted
  in each governance/locator finding so the reviser sees whom the
  sentence should have been written for.
- The public repository URL (:func:`resolve_public_repo_url`) resolves in
  order from ``<thread>/.anvil.json`` ``public_repo_url``, the thread
  ``BRIEF.md`` frontmatter ``public_repo_url``, then the first public
  forge link (GitHub, GitLab, Codeberg, Bitbucket, Zenodo, DOI, OSF,
  figshare, Hugging Face) inside the paper's artifacts/availability
  section only (a dependency cited elsewhere, e.g. the Mathlib GitHub in
  the introduction, is never the paper's repository). The result carries
  ``public_repo_url_source`` (``anvil_json`` / ``brief`` = declared,
  ``derived`` = guessed). Only a declared URL yields a concrete ``\\href``
  in the ``unlinked_artifact_path`` fix (and, in ``paper-audit``, a
  critical flag); a derived URL is named as a candidate to confirm.
  The link-hygiene rule applies either way — a bare repo-relative path is
  unfollowable whether or not a public repository exists.

Sidecar + discovery contract
----------------------------

``write_review_dir`` writes ``<thread>.{N}.audience/_review.json`` via
``anvil/lib/sidecar.py::write_critic_review_dir`` (``staged_sidecar``
atomic rename). The ``.audience`` tag is a single segment, so
``anvil/lib/critics.py::discover_critics`` picks it up with no aggregator
change. The check is deterministic and cheaply re-runnable, so a prior
pass's sidecar is regenerated (the same carve-out ``pending_marker`` and
``numeric_consistency`` document).

CLI entry-point
---------------

``python -m anvil.lib.audience_check <version_dir> [--write-review]
[--body PATH]``

Writes a JSON summary to stdout. Exit codes: ``0`` no active hits, ``1``
active hits present (an advisory signal — callers must NOT treat it as a
blocking verdict), ``2`` invocation error.
"""

from __future__ import annotations

import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, Iterable, Iterator, List, Optional, Sequence, Tuple

from anvil.lib.body_resolution import record_body_path, resolve_body_path
from anvil.lib.review_schema import Finding, Kind, Review, Score
from anvil.lib.sidecar import write_critic_review_dir

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

CRITIC_ID = "audience"
"""Stable identifier for this critic in ``_review.json.critic_id``."""

CHECK_NAME = "audience_check"
"""Check identifier echoed in JSON payloads (and the suppression rule)."""

DIM_AUDIENCE = "audience_fit"
"""Dimension name surfaced on every emitted Finding (folds into dims 7/9)."""

AUDIENCE_SUFFIX = "audience"
"""Sidecar dir tag: ``<thread>.{N}.audience/``."""

RULE_GOVERNANCE = "governance_vocabulary"
RULE_PRIVATE_LOCATOR = "private_locator"
RULE_UNLINKED_PATH = "unlinked_artifact_path"
RULES: Tuple[str, ...] = (RULE_GOVERNANCE, RULE_PRIVATE_LOCATOR, RULE_UNLINKED_PATH)

REGION_BODY = "body"
REGION_APPENDIX = "appendix"

SEVERITY_BY_REGION = {REGION_BODY: "major", REGION_APPENDIX: "minor"}
SEVERITY_SUPPRESSED = "nit"

BRIEF_FILENAME = "BRIEF.md"
ANVIL_JSON = ".anvil.json"
PUBLIC_REPO_KEY = "public_repo_url"

# Provenance of the resolved public repository URL. Only a *declared* URL
# (``.anvil.json`` / BRIEF frontmatter) is trusted enough to escalate an
# unlinked artifact path to an audit critical flag or to template a concrete
# ``\href`` fix; a URL *derived* from the paper's own artifacts section is a
# candidate the author must confirm (a cited dependency is not the paper's
# repository).
REPO_SOURCE_ANVIL_JSON = "anvil_json"
REPO_SOURCE_BRIEF = "brief"
REPO_SOURCE_DERIVED = "derived"
DECLARED_REPO_SOURCES = (REPO_SOURCE_ANVIL_JSON, REPO_SOURCE_BRIEF)

# ---------------------------------------------------------------------------
# Vocabulary (fixed, small, case-insensitive)
# ---------------------------------------------------------------------------

_GOVERNANCE_PATTERNS: Tuple[re.Pattern, ...] = tuple(
    re.compile(p, re.IGNORECASE)
    for p in (
        # authorized / authorised / authorization / unauthorized ...
        r"\b(?:un)?authori[sz](?:ed|es|e|ing|ations?)\b",
        # commissioned this manuscript / commissioning
        r"\bcommission(?:ed|ing)\b",
        # operator's publication gate / maintainer approval / operator goal
        r"\b(?:operator|maintainer)(?:['’]s)?\s+(?:(?:publication|release|"
        r"merge|spend|budget|final)\s+)?(?:gate|review|approval|sign-?off|"
        r"decision|goal)s?\b",
        r"\bpublication\s+gate\b",
        # goal #39, goal \#39, ticket #12, issue #7, board #40
        r"\b(?:goal|ticket|issue|board|task|epic)s?\s*\\?#\s*\d+",
        # budget cap / spend ceiling / cost approval
        r"\b(?:budget|spend(?:ing)?|cost)\s+(?:cap|ceiling|limit|approval|"
        r"authori[sz]ation)s?\b",
    )
)

_PRIVATE_LOCATOR_PATTERNS: Tuple[re.Pattern, ...] = tuple(
    re.compile(p, re.IGNORECASE)
    for p in (
        r"\b(?:s3|gs|az|abfss?|hdfs)://[^\s}]+",
        r"\bfile://[^\s}]+",
        r"\bhttps?://(?:localhost|127\.0\.0\.1|0\.0\.0\.0|10\.\d+\.\d+\.\d+|"
        r"192\.168\.\d+\.\d+)[^\s}]*",
        r"(?<![\w/])/(?:Users|home|Volumes)/[\w.\-/]+",
        r"\b(?:room\s+)?(?:messages?|msgs?)\s*(?:\\?#\s*)?\d{3,}",
    )
)

# Repo-relative file path: >=1 slash, final segment with a letter-led
# extension. Applied only inside an artifacts section, after link masking.
_PATH_RE = re.compile(
    r"(?<![\w/.:~\-])((?:[A-Za-z0-9_.\-]+/)+[A-Za-z0-9_\-][A-Za-z0-9_.\-]*"
    r"\.[A-Za-z][A-Za-z0-9]{0,7})(?![\w/])"
)

_ARTIFACTS_HEADING_RE = re.compile(
    r"\b(?:artifacts?|artefacts?|availability|receipts?|supplementary\s+"
    r"(?:material|materials|data|files)|code\s+and\s+data|data\s+and\s+code|"
    r"reproducibility\s+(?:package|materials?))\b",
    re.IGNORECASE,
)

_NOT_PUBLISHED_RE = re.compile(
    r"not\s+(?:yet\s+)?published|unpublished|not\s+publicly\s+(?:available|"
    r"released)|not\s+released|available\s+(?:on|upon)\s+request",
    re.IGNORECASE,
)

_PUBLIC_FORGE_RE = re.compile(
    r"https?://(?:www\.)?(?:github\.com|gitlab\.com|codeberg\.org|"
    r"bitbucket\.org|zenodo\.org|doi\.org|osf\.io|figshare\.com|"
    r"huggingface\.co)/[^\s}\)\]>\"']+",
    re.IGNORECASE,
)
_FORGE_REPO_HOSTS = ("github.com", "gitlab.com", "codeberg.org", "bitbucket.org")

# ---------------------------------------------------------------------------
# Masking
# ---------------------------------------------------------------------------

_LINT_DISABLE_RE = re.compile(
    r"(?:<!--|%)\s*anvil-lint-disable:\s*(?P<rules>[a-zA-Z0-9_,\- ]+?)\s*(?:-->|$)",
)

_FENCE_RE = re.compile(r"(```|~~~).*?\1", re.DOTALL)
_HTML_COMMENT_RE = re.compile(r"<!--.*?-->", re.DOTALL)
_INLINE_CODE_RE = re.compile(r"`[^`\n]*`")
_LATEX_COMMENT_RE = re.compile(r"(?<!\\)%[^\n]*")
_LATEX_VERBATIM_RE = re.compile(
    r"\\begin\{(verbatim\*?|lstlisting|minted|Verbatim)\}.*?\\end\{\1\}",
    re.DOTALL,
)
_LATEX_VERB_RE = re.compile(r"\\verb\*?(\S).*?\1")

# Link constructs blanked before path detection (a linked path is fine).
_LINK_MASKS: Tuple[re.Pattern, ...] = (
    re.compile(r"\\href\s*\{[^}]*\}\s*\{(?:[^{}]|\{[^{}]*\})*\}"),
    re.compile(r"\\(?:url|nolinkurl)\s*\{[^}]*\}"),
    re.compile(r"\[[^\]\n]*\]\([^)\n]*\)"),
    re.compile(r"<https?://[^>\n]*>"),
    re.compile(r"\b[a-z][a-z0-9+.\-]*://\S+", re.IGNORECASE),
)


def _blank(m: "re.Match[str]") -> str:
    return "".join(c if c == "\n" else " " for c in m.group(0))


def _mask_base(text: str, *, latex: bool) -> str:
    """Mask regions that are never reader-visible prose.

    Code fences and HTML comments always; LaTeX comments and verbatim
    environments for ``.tex`` bodies. Offsets and newlines are preserved.
    """
    masked = _FENCE_RE.sub(_blank, text)
    masked = _HTML_COMMENT_RE.sub(_blank, masked)
    if latex:
        masked = _LATEX_VERBATIM_RE.sub(_blank, masked)
        masked = _LATEX_COMMENT_RE.sub(_blank, masked)
    return masked


def _mask_prose(base: str, *, latex: bool) -> str:
    """Additionally mask inline code (markdown) / ``\\verb`` (LaTeX)."""
    masked = _INLINE_CODE_RE.sub(_blank, base)
    if latex:
        masked = _LATEX_VERB_RE.sub(_blank, masked)
    return masked


def _mask_links(line: str) -> str:
    for pattern in _LINK_MASKS:
        line = pattern.sub(_blank, line)
    return line


def _suppressed_lines(text: str) -> frozenset:
    suppressed = set()
    for lineno, line in enumerate(text.splitlines(), start=1):
        for m in _LINT_DISABLE_RE.finditer(line):
            rules = {r.strip() for r in m.group("rules").split(",")}
            if CHECK_NAME in rules:
                suppressed.add(lineno)
                suppressed.add(lineno + 1)
    return frozenset(suppressed)


# ---------------------------------------------------------------------------
# Document model: an ordered stream of lines across included files
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class _Line:
    path: str
    lineno: int
    raw: str
    base: str  # comments / fences / verbatim masked
    prose: str  # base + inline code masked
    suppressed: bool


_LATEX_INPUT_RE = re.compile(r"\\(?:input|include)\s*\{([^}]+)\}")
_LATEX_HEADING_RE = re.compile(
    r"\\(part|chapter|section|subsection|subsubsection|paragraph)\*?\s*"
    r"(?:\[[^\]]*\])?\s*\{([^}]*)\}"
)
_LATEX_LEVELS = {
    "part": 0,
    "chapter": 1,
    "section": 2,
    "subsection": 3,
    "subsubsection": 4,
    "paragraph": 5,
}
_LATEX_APPENDIX_RE = re.compile(r"\\appendix\b|\\begin\{appendices\}")
_MD_HEADING_RE = re.compile(r"^(#{1,6})\s+(.*?)\s*#*\s*$")
_APPENDIX_TITLE_RE = re.compile(r"^\s*appendi(?:x|ces)\b", re.IGNORECASE)


def _file_lines(text: str, path: str, *, latex: bool) -> List[_Line]:
    base = _mask_base(text, latex=latex)
    prose = _mask_prose(base, latex=latex)
    suppressed = _suppressed_lines(text)
    raw_lines = text.split("\n")
    base_lines = base.split("\n")
    prose_lines = prose.split("\n")
    return [
        _Line(
            path=path,
            lineno=i,
            raw=raw_lines[i - 1],
            base=base_lines[i - 1],
            prose=prose_lines[i - 1],
            suppressed=i in suppressed,
        )
        for i in range(1, len(raw_lines) + 1)
    ]


def _candidate_children(target: str, including: Path, job_dir: Path) -> List[Path]:
    target = target.strip()
    names = [target] if target.endswith(".tex") else [f"{target}.tex", target]
    out: List[Path] = []
    for base in (job_dir, including.parent):
        for name in names:
            cand = Path(name) if Path(name).is_absolute() else base / name
            if cand not in out:
                out.append(cand)
    return out


def _relative_label(path: Path, version_dir: Path) -> str:
    try:
        return path.resolve().relative_to(version_dir.resolve()).as_posix()
    except ValueError:
        return str(path)


def _document_lines(
    body_file: Path, version_dir: Path, *, body_label: str
) -> Tuple[List[_Line], List[str]]:
    """Expand ``\\input``/``\\include`` inline, in document order.

    Returns the flattened line stream and the list of file labels scanned
    (master first). Missing children are skipped silently — a dangling
    include is ``render_gate``/audit territory, not this check's.
    """
    latex = body_file.suffix == ".tex"
    files: List[str] = []
    visited: set = set()
    job_dir = body_file.parent

    def walk(path: Path, label: str) -> List[_Line]:
        real = path.resolve()
        if real in visited:
            return []
        visited.add(real)
        try:
            text = real.read_text(encoding="utf-8")
        except OSError:
            return []
        files.append(label)
        out: List[_Line] = []
        for line in _file_lines(text, label, latex=latex):
            out.append(line)
            if not latex:
                continue
            for m in _LATEX_INPUT_RE.finditer(line.base):
                hit = next(
                    (c for c in _candidate_children(m.group(1), real, job_dir) if c.is_file()),
                    None,
                )
                if hit is not None:
                    out.extend(walk(hit, _relative_label(hit, version_dir)))
        return out

    return walk(body_file, body_label), files


# ---------------------------------------------------------------------------
# Result types
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class AudienceHit:
    """One (file, line, rule) hit, grouping every matched term on the line."""

    rule: str
    terms: Tuple[str, ...]
    path: str
    line: int
    region: str
    section: str
    excerpt: str
    suppressed: bool = False

    @property
    def severity(self) -> str:
        if self.suppressed:
            return SEVERITY_SUPPRESSED
        return SEVERITY_BY_REGION[self.region]

    def to_dict(self) -> dict:
        return {
            "rule": self.rule,
            "terms": list(self.terms),
            "path": self.path,
            "line": self.line,
            "region": self.region,
            "section": self.section,
            "severity": self.severity,
            "suppressed": self.suppressed,
            "excerpt": self.excerpt,
        }


def _excerpt(raw: str, limit: int = 160) -> str:
    s = " ".join(raw.split())
    return s if len(s) <= limit else s[: limit - 1] + "…"


def _dedupe(terms: Iterable[str]) -> Tuple[str, ...]:
    out: List[str] = []
    for t in terms:
        t = t.strip().rstrip(".,;:)")
        if t and t not in out:
            out.append(t)
    return tuple(out)


def _walk_scopes(
    lines: Sequence[_Line], *, latex: bool
) -> Iterator[Tuple[_Line, bool, str, str, bool]]:
    """Yield ``(line, is_heading, region, section, in_artifacts)`` per line.

    ``in_artifacts`` is ``True`` for a non-heading line inside an
    artifacts/availability section (scope closes at the next heading of
    the same or a higher level).
    """
    region = REGION_BODY
    section = ""
    artifacts_level: Optional[int] = None  # heading level that opened scope

    for ln in lines:
        heading: Optional[Tuple[int, str]] = None
        if latex:
            m = _LATEX_HEADING_RE.search(ln.base)
            if m:
                heading = (_LATEX_LEVELS[m.group(1)], m.group(2))
            if _LATEX_APPENDIX_RE.search(ln.base):
                region = REGION_APPENDIX
        else:
            m = _MD_HEADING_RE.match(ln.base)
            if m:
                heading = (len(m.group(1)), m.group(2))
        if heading is not None:
            level, title = heading
            section = title.strip()
            if _APPENDIX_TITLE_RE.match(title):
                region = REGION_APPENDIX
            if artifacts_level is not None and level <= artifacts_level:
                artifacts_level = None
            if _ARTIFACTS_HEADING_RE.search(title):
                artifacts_level = level
        yield (
            ln,
            heading is not None,
            region,
            section,
            artifacts_level is not None and heading is None,
        )


def _artifacts_text(lines: Sequence[_Line], *, latex: bool) -> str:
    """The (comment/code-masked) text of every artifacts-section line."""
    return "\n".join(
        ln.base for ln, _h, _r, _s, in_art in _walk_scopes(lines, latex=latex) if in_art
    )


def _scan_lines(lines: Sequence[_Line], *, latex: bool) -> List[AudienceHit]:
    hits: List[AudienceHit] = []

    for ln, _is_heading, region, section, in_artifacts in _walk_scopes(lines, latex=latex):

        def emit(rule: str, terms: Iterable[str]) -> None:
            t = _dedupe(terms)
            if t:
                hits.append(
                    AudienceHit(
                        rule=rule,
                        terms=t,
                        path=ln.path,
                        line=ln.lineno,
                        region=region,
                        section=section,
                        excerpt=_excerpt(ln.raw),
                        suppressed=ln.suppressed,
                    )
                )

        emit(
            RULE_GOVERNANCE,
            (m.group(0) for p in _GOVERNANCE_PATTERNS for m in p.finditer(ln.prose)),
        )
        emit(
            RULE_PRIVATE_LOCATOR,
            (m.group(0) for p in _PRIVATE_LOCATOR_PATTERNS for m in p.finditer(ln.base)),
        )
        if in_artifacts:
            if not _NOT_PUBLISHED_RE.search(ln.raw):
                linkless = _mask_links(ln.base).replace("\\_", "_")
                emit(RULE_UNLINKED_PATH, (m.group(1) for m in _PATH_RE.finditer(linkless)))
    return hits


def find_audience_hits(
    text: str, *, latex: bool = False, path: str = "main.tex"
) -> List[AudienceHit]:
    """Scan one body text (no ``\\input`` expansion). Pure function.

    Set ``latex=True`` for ``.tex`` bodies (LaTeX comment / verbatim
    masking, ``\\section``/``\\appendix`` structure). Suppressed hits are
    returned with ``suppressed=True``.
    """
    return _scan_lines(_file_lines(text, path, latex=latex), latex=latex)


# ---------------------------------------------------------------------------
# BRIEF: declared audience + public repository URL
# ---------------------------------------------------------------------------


def _read_frontmatter(brief: Path) -> dict:
    if not brief.is_file():
        return {}
    try:
        from anvil.lib.frontmatter import extract_frontmatter

        fm = extract_frontmatter(brief.read_text(encoding="utf-8"))
    except Exception:  # tolerant: a reporting aid never fails the check
        return {}
    return fm if isinstance(fm, dict) else {}


def _flatten_audience(value) -> List[str]:
    if isinstance(value, str):
        return [value.strip()] if value.strip() else []
    if isinstance(value, list):
        return [v.strip() for v in value if isinstance(v, str) and v.strip()]
    if isinstance(value, dict):
        out: List[str] = []
        for v in value.values():
            out.extend(_flatten_audience(v))
        return out
    return []


_AUDIENCE_HEADING_RE = re.compile(
    r"^#{1,6}\s+(?:target\s+)?(?:audience|readership)\b.*$",
    re.IGNORECASE | re.MULTILINE,
)


def load_declared_audience(thread_dir: Path) -> List[str]:
    """Return the BRIEF's declared audience (reporting aid; tolerant).

    Order: thread ``BRIEF.md`` frontmatter ``audience:`` → first paragraph
    under an ``Audience`` / ``Target audience`` / ``Readership`` heading →
    project ``BRIEF.md`` (``thread_dir.parent``) frontmatter ``audience:``.
    Returns ``[]`` when none is declared.
    """
    thread_dir = Path(thread_dir)
    brief = thread_dir / BRIEF_FILENAME
    declared = _flatten_audience(_read_frontmatter(brief).get("audience"))
    if declared:
        return declared
    if brief.is_file():
        try:
            text = brief.read_text(encoding="utf-8")
        except OSError:
            text = ""
        m = _AUDIENCE_HEADING_RE.search(text)
        if m:
            rest = text[m.end():].lstrip("\n")
            para = rest.split("\n\n", 1)[0].strip()
            if para and not para.startswith("#"):
                return [" ".join(para.split())]
    return _flatten_audience(
        _read_frontmatter(thread_dir.parent / BRIEF_FILENAME).get("audience")
    )


def _normalize_repo_url(url: str) -> str:
    url = url.rstrip(".,;:")
    m = re.match(r"(https?://(?:www\.)?([^/]+))/([^/]+)/([^/#?]+)", url)
    if m and m.group(2).lower() in _FORGE_REPO_HOSTS:
        repo = m.group(4)
        if repo.endswith(".git"):
            repo = repo[:-4]
        return f"{m.group(1)}/{m.group(3)}/{repo}"
    return url


def resolve_public_repo_url_with_source(
    thread_dir: Path, text: str = ""
) -> Tuple[Optional[str], Optional[str]]:
    """Resolve the thread's public repository URL and where it came from.

    Returns ``(url, source)``; ``source`` is ``"anvil_json"`` or ``"brief"``
    for a declared URL, ``"derived"`` for the first public-forge link in
    ``text``, and ``None`` (with ``url=None``) when nothing resolves.
    :func:`check_audience` passes only the artifacts/availability-section
    text as ``text``, so a dependency cited in the introduction (e.g. the
    Mathlib GitHub) is never mistaken for the paper's own repository.
    Forge repo links are normalized to ``https://host/owner/repo``.
    """
    thread_dir = Path(thread_dir)
    anvil_json = thread_dir / ANVIL_JSON
    if anvil_json.is_file():
        try:
            cfg = json.loads(anvil_json.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            cfg = {}
        val = cfg.get(PUBLIC_REPO_KEY) if isinstance(cfg, dict) else None
        if isinstance(val, str) and val.strip():
            return val.strip().rstrip("/"), REPO_SOURCE_ANVIL_JSON
    val = _read_frontmatter(thread_dir / BRIEF_FILENAME).get(PUBLIC_REPO_KEY)
    if isinstance(val, str) and val.strip():
        return val.strip().rstrip("/"), REPO_SOURCE_BRIEF
    m = _PUBLIC_FORGE_RE.search(text or "")
    if m:
        return _normalize_repo_url(m.group(0)), REPO_SOURCE_DERIVED
    return None, None


def resolve_public_repo_url(thread_dir: Path, text: str = "") -> Optional[str]:
    """Resolve the thread's public repository URL, or ``None``.

    Order: ``<thread>/.anvil.json`` ``public_repo_url`` → thread
    ``BRIEF.md`` frontmatter ``public_repo_url`` → first public-forge link
    in ``text``. See :func:`resolve_public_repo_url_with_source` for the
    provenance, which decides whether the URL is trusted.
    """
    return resolve_public_repo_url_with_source(thread_dir, text)[0]


# ---------------------------------------------------------------------------
# Aggregate result
# ---------------------------------------------------------------------------


@dataclass
class AudienceResult:
    """Outcome of one :func:`check_audience` pass."""

    version_dir: str
    body_path: str
    files: List[str] = field(default_factory=list)
    hits: List[AudienceHit] = field(default_factory=list)
    declared_audience: List[str] = field(default_factory=list)
    public_repo_url: Optional[str] = None
    public_repo_url_source: Optional[str] = None

    @property
    def public_repo_url_declared(self) -> bool:
        """``True`` only for a URL declared in ``.anvil.json`` / BRIEF.md."""
        return bool(self.public_repo_url) and (
            self.public_repo_url_source in DECLARED_REPO_SOURCES
        )

    @property
    def active_hits(self) -> List[AudienceHit]:
        return [h for h in self.hits if not h.suppressed]

    @property
    def suppressed_hits(self) -> List[AudienceHit]:
        return [h for h in self.hits if h.suppressed]

    def passed(self) -> bool:
        """``True`` when no active (unsuppressed) hit remains. Advisory."""
        return not self.active_hits

    def counts(self) -> Dict[str, int]:
        return {r: sum(1 for h in self.active_hits if h.rule == r) for r in RULES}

    def to_json(self) -> dict:
        return {
            "check": CHECK_NAME,
            "version_dir": self.version_dir,
            "body_path": self.body_path,
            "files": list(self.files),
            "declared_audience": list(self.declared_audience),
            "public_repo_url": self.public_repo_url,
            "public_repo_url_source": self.public_repo_url_source,
            "public_repo_url_declared": self.public_repo_url_declared,
            "hits": [h.to_dict() for h in self.hits],
            "counts": self.counts(),
            "suppressed_count": len(self.suppressed_hits),
            "advisory": True,
            "pass": self.passed(),
        }

    # -- review -------------------------------------------------------------

    def _audience_phrase(self) -> str:
        if self.declared_audience:
            return "the BRIEF's declared audience (" + "; ".join(self.declared_audience) + ")"
        return "the paper's reader (no audience declared in BRIEF.md)"

    def _finding_text(self, h: AudienceHit) -> Tuple[str, str]:
        where = f"{h.region}" + (f", section {h.section!r}" if h.section else "")
        terms = ", ".join(repr(t) for t in h.terms)
        if h.rule == RULE_GOVERNANCE:
            rationale = (
                f"Audience fit ({where}): governance vocabulary {terms} "
                f"addresses the project's operator or team — authorization, "
                f"commissioning, publication gates, budget, internal "
                f"goal/ticket numbers — not {self._audience_phrase()}. "
                f"Excerpt: {h.excerpt!r}. Deterministic pre-flight evidence "
                f"for the rubric's audience-fit sub-rule (dims 7/9); confirm "
                f"the addressee before deducting."
            )
            fix = (
                "Delete the sentence or move it to a non-published process "
                "log (the thread's BRIEF.md or a session note). If the fact "
                "matters to the reader, restate it without the governance "
                "framing (what was run, not who approved it)."
            )
        elif h.rule == RULE_PRIVATE_LOCATOR:
            rationale = (
                f"Audience fit ({where}): private locator {terms} points "
                f"somewhere {self._audience_phrase()} cannot follow (a "
                f"private bucket, a local path, or an internal message "
                f"number). Excerpt: {h.excerpt!r}."
            )
            fix = (
                "Replace with a public \\href/\\url, or drop the pointer and "
                "state plainly that the resource is not published."
            )
        else:
            rationale = (
                f"Link hygiene ({where}): artifact path(s) {terms} are named "
                f"as bare repo-relative paths with no \\href/\\url and no "
                f"'not published' marker; a reader cannot follow them. "
                f"Excerpt: {h.excerpt!r}."
            )
            if self.public_repo_url_declared:
                first = h.terms[0]
                fix = (
                    f"Link each path to its public location, e.g. "
                    f"\\href{{{self.public_repo_url}/blob/<ref>/{first}}}"
                    f"{{\\texttt{{{first}}}}} (resolved public repository: "
                    f"{self.public_repo_url}), or mark it explicitly "
                    f"'not published'."
                )
            elif self.public_repo_url:
                fix = (
                    f"Link each path to a public location with \\href/\\url, "
                    f"or mark it explicitly 'not published'. Candidate "
                    f"repository {self.public_repo_url} was only derived from a "
                    f"link in this section and is NOT confirmed as the paper's "
                    f"own repository: if it hosts these artifacts, declare it as "
                    f"`public_repo_url` in <thread>/.anvil.json or the thread "
                    f"BRIEF.md frontmatter and link each path there; never "
                    f"invent a URL."
                )
            else:
                fix = (
                    "Link each path to a public location with \\href/\\url, "
                    "or mark it explicitly 'not published'. No public "
                    "repository URL resolved (declare `public_repo_url` in "
                    "<thread>/.anvil.json or the thread BRIEF.md frontmatter)."
                )
        if h.suppressed:
            rationale = (
                f"Suppressed ({CHECK_NAME} lint-disable directive; recorded, "
                f"not counted): " + rationale
            )
        return rationale, fix

    def to_review(self, *, version_dir: str, critic_id: str = CRITIC_ID) -> Review:
        """Build an advisory ``Review`` (``kind=Kind.TOOL_EVIDENCE``).

        No critical flag; the single ``Score`` is ``score=None`` (owns no
        rubric dimension), so the aggregated total and verdict are
        unaffected. Findings are ``major`` (body) / ``minor`` (appendix) /
        ``nit`` (suppressed).
        """
        scores = [
            Score(
                dimension=CHECK_NAME,
                score=None,
                max=1,
                justification=(
                    "audience-fit pre-flight is a deterministic advisory "
                    "scan; owns no rubric dim (evidence for dims 7/9)."
                ),
            )
        ]
        findings: List[Finding] = []
        for h in self.hits:
            rationale, fix = self._finding_text(h)
            findings.append(
                Finding(
                    severity=h.severity,
                    dimension=DIM_AUDIENCE,
                    evidence_span=f"{h.path}:L{h.line}",
                    rationale=rationale,
                    suggested_fix=fix,
                    tool_calls=[],
                )
            )
        return Review(
            schema_version="1",
            kind=Kind.TOOL_EVIDENCE,
            version_dir=version_dir,
            critic_id=critic_id,
            scores=scores,
            findings=findings,
            critical_flags=[],
        )


# ---------------------------------------------------------------------------
# Filesystem entry points
# ---------------------------------------------------------------------------


def check_audience(
    version_dir: Path,
    *,
    body: Optional[Path] = None,
) -> AudienceResult:
    """Run the audience-fit pre-flight against a version directory.

    Scans the body (``<slug>.md`` or ``main.tex``, or ``body`` override)
    and, for a ``.tex`` body, every ``\\input``/``\\include`` child in
    document order. Reads the declared audience and public repository URL
    from the thread root (``version_dir.parent``) as reporting aids.
    """
    version_dir = Path(version_dir).resolve()
    if not version_dir.is_dir():
        raise FileNotFoundError(
            f"audience_check: version_dir {version_dir!s} does not exist "
            f"or is not a directory."
        )
    body_file = resolve_body_path(version_dir, body=body, caller_name="audience_check")
    body_label = record_body_path(version_dir, body_file)
    lines, files = _document_lines(body_file, version_dir, body_label=body_label)
    hits = _scan_lines(lines, latex=body_file.suffix == ".tex")
    thread_dir = version_dir.parent
    repo_url, repo_source = resolve_public_repo_url_with_source(
        thread_dir, _artifacts_text(lines, latex=body_file.suffix == ".tex")
    )
    return AudienceResult(
        version_dir=version_dir.name,
        body_path=body_label,
        files=files,
        hits=hits,
        declared_audience=load_declared_audience(thread_dir),
        public_repo_url=repo_url,
        public_repo_url_source=repo_source,
    )


def write_review_dir(
    version_dir: Path,
    result: AudienceResult,
    *,
    critic_id: str = CRITIC_ID,
) -> Path:
    """Write ``<version_dir>.audience/_review.json`` (atomic, regenerating)."""
    version_dir = Path(version_dir)
    review = result.to_review(version_dir=version_dir.name, critic_id=critic_id)
    return write_critic_review_dir(version_dir, AUDIENCE_SUFFIX, review)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _build_cli_parser():
    import argparse

    p = argparse.ArgumentParser(
        prog="python -m anvil.lib.audience_check",
        description=(
            "Deterministic audience-fit pre-flight (advisory): flags "
            "governance vocabulary addressed to the project's operator, "
            "private locators a reader cannot follow, and bare "
            "repo-relative artifact paths in an artifacts/availability "
            "section. Exit 1 signals findings; it is NOT a blocking verdict."
        ),
    )
    p.add_argument("version_dir", help="Path to <thread>.{N}/.")
    p.add_argument(
        "--write-review",
        action="store_true",
        help="Also write <version_dir>.audience/_review.json (staged_sidecar).",
    )
    p.add_argument(
        "--body",
        metavar="PATH",
        default=None,
        help="Override body-file discovery (adopted-in-place legacy threads).",
    )
    return p


def main(argv: Optional[List[str]] = None) -> int:
    """CLI entry point. ``0`` clean, ``1`` findings (advisory), ``2`` error."""
    args = _build_cli_parser().parse_args(argv)
    try:
        result = check_audience(
            Path(args.version_dir),
            body=Path(args.body) if args.body else None,
        )
    except FileNotFoundError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(result.to_json(), indent=2))
    if args.write_review:
        out = write_review_dir(Path(args.version_dir), result)
        print(f"wrote {out}", file=sys.stderr)
    return 0 if result.passed() else 1


__all__ = [
    "CRITIC_ID",
    "CHECK_NAME",
    "DIM_AUDIENCE",
    "AUDIENCE_SUFFIX",
    "RULE_GOVERNANCE",
    "RULE_PRIVATE_LOCATOR",
    "RULE_UNLINKED_PATH",
    "RULES",
    "AudienceHit",
    "AudienceResult",
    "find_audience_hits",
    "load_declared_audience",
    "resolve_public_repo_url",
    "resolve_public_repo_url_with_source",
    "REPO_SOURCE_ANVIL_JSON",
    "REPO_SOURCE_BRIEF",
    "REPO_SOURCE_DERIVED",
    "DECLARED_REPO_SOURCES",
    "check_audience",
    "write_review_dir",
    "main",
]


if __name__ == "__main__":
    raise SystemExit(main())
