"""Deterministic define-before-use and roadmap-order lint (issue #1401).

Child of #1396 (proposals 2 and 3). Member of the deterministic-checks
family alongside ``anvil/lib/audience_check.py`` (whose body reader, mask
helpers and sidecar writer it reuses) and ``numeric_consistency.py``.

The problem
-----------

A paper can compile, pass every gate and still read badly because of *text
order*: a coined identifier (``S18``) appears in a figure caption pages
before the sentence that defines it; an acronym is used before its
expansion; one concept is named two ways ("family a" / "the first
family"); the introduction's roadmap promises "Section 4 reports accuracy,
Section 5 the results" while the body has the results first. No pre-flight
looked at any of this.

What this module does
---------------------

A conservative scan (precision over recall: it is advisory) over the body
in document order (``main.tex`` plus its ``\\input``/``\\include``
children, or ``<slug>.md``), reporting three rule classes:

- ``define_before_use`` — a token whose first occurrence precedes its
  *defining* occurrence. Token kinds: acronyms (``degrees of freedom
  (DOFs)``), ``\\emph{}`` first definitions ("we call this \\emph{edge}"),
  coined identifiers (``S18``, ``L0``) and inline math symbols
  (``where $\\kappa$ denotes ...``). Captions and floats are counted at
  their source position. A token with no defining occurrence is never
  reported.
- ``variant_pair`` — two spellings that likely name one concept: an
  ordinal/letter pair ("family a" / "first family") or a hyphen/space/
  closed compound ("look-up table" / "lookup table").
- ``roadmap_order`` — the introduction names sections in an order that
  contradicts the body's section order (``Section~\\ref{sec:acc}`` before
  ``Section~\\ref{sec:res}`` while the results section comes first).
  Contribution lists are covered because they are scanned the same way.

Verdict posture: ADVISORY (warn-only)
-------------------------------------

Findings are ``minor`` (``nit`` when suppressed); the review carries **no
critical flag** and its single ``Score`` is ``score=None``, so it never
changes the aggregated total or forces ``Verdict.BLOCK``. The hits are
evidence for the reader-flow lens and rubric dim 7, never a gate.

Suppression
-----------

``<!-- anvil-lint-disable: reader_flow_lint -->`` (markdown) or
``% anvil-lint-disable: reader_flow_lint`` (LaTeX) on the same line or the
line above suppresses a hit; it is recorded at ``nit``.

Sidecar + discovery contract
----------------------------

``write_review_dir`` writes ``<thread>.{N}.readerflowlint/_review.json`` via
``anvil/lib/sidecar.py::write_critic_review_dir``. The single-segment tag
means ``critics.discover_critics`` picks it up with no aggregator change.

CLI
---

``python -m anvil.lib.reader_flow_lint <version_dir> [--write-review]
[--body PATH]``. Exit ``0`` no active hits, ``1`` active hits (an advisory
signal, not a verdict), ``2`` invocation error.
"""

from __future__ import annotations

import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

from anvil.lib.audience_check import (
    _LATEX_HEADING_RE,
    _LATEX_LEVELS,
    _LINT_DISABLE_RE,
    _MD_HEADING_RE,
    _Line,
    _document_lines,
    _excerpt,
    _walk_scopes,
)
from anvil.lib.body_resolution import record_body_path, resolve_body_path
from anvil.lib.review_schema import Finding, Kind, Review, Score
from anvil.lib.sidecar import write_critic_review_dir

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

CRITIC_ID = "reader_flow_lint"
CHECK_NAME = "reader_flow_lint"
DIM_READER_FLOW = "reader_flow"
READER_FLOW_SUFFIX = "readerflowlint"

RULE_DEFINE_BEFORE_USE = "define_before_use"
RULE_VARIANT_PAIR = "variant_pair"
RULE_ROADMAP_ORDER = "roadmap_order"
RULES = (RULE_DEFINE_BEFORE_USE, RULE_VARIANT_PAIR, RULE_ROADMAP_ORDER)

KIND_ACRONYM = "acronym"
KIND_EMPH = "emph_term"
KIND_IDENTIFIER = "identifier"
KIND_SYMBOL = "symbol"

SEVERITY_ACTIVE = "minor"
SEVERITY_SUPPRESSED = "nit"

# ---------------------------------------------------------------------------
# Line preparation
# ---------------------------------------------------------------------------

_BEGIN_DOC_RE = re.compile(r"\\begin\{document\}")
_MACRO_DEF_RE = re.compile(
    r"^\s*\\(?:re)?newcommand|^\s*\\def\\|^\s*\\DeclareMathOperator"
)
_STRIP_ARG_RES: Tuple[re.Pattern, ...] = (
    re.compile(r"\\(?:auto|c|C|eq|page|name|v)?ref\*?\{[^}]*\}"),
    re.compile(r"\\label\{[^}]*\}"),
    re.compile(r"\\(?:no)?cite[a-z]*\*?(?:\[[^\]]*\])*\{[^}]*\}"),
    re.compile(r"\\(?:url|nolinkurl)\{[^}]*\}"),
    re.compile(r"\\href\{[^}]*\}"),
    re.compile(
        r"\\(?:input|include|includegraphics|bibliography|usepackage)(?:\[[^\]]*\])?\{[^}]*\}"
    ),
    re.compile(r"\b[a-z][a-z0-9+.\-]*://\S+", re.IGNORECASE),
)

_STOP_INITIALS = frozenset(
    {"of", "and", "the", "for", "in", "on", "to", "a", "an", "with", "per"}
)


@dataclass(frozen=True)
class _Row:
    idx: int  # position in the flattened stream
    ln: _Line
    text: str  # prose with ref/label/cite/url arguments and macro defs blanked
    region: str
    section: str
    is_heading: bool
    suppressed: bool


def _blank_args(text: str) -> str:
    for pat in _STRIP_ARG_RES:
        text = pat.sub(lambda m: " " * len(m.group(0)), text)
    return text


def _rows(lines: Sequence[_Line], *, latex: bool) -> List[_Row]:
    start = 0
    if latex:
        for i, ln in enumerate(lines):
            if _BEGIN_DOC_RE.search(ln.base):
                start = i + 1
                break
    suppress_at: set = set()
    for i, ln in enumerate(lines):
        for m in _LINT_DISABLE_RE.finditer(ln.raw):
            if CHECK_NAME in {r.strip() for r in m.group("rules").split(",")}:
                suppress_at.update((i, i + 1))
    rows: List[_Row] = []
    for i, (ln, heading, region, section, _art) in enumerate(
        _walk_scopes(lines, latex=latex)
    ):
        if i < start:
            continue
        text = "" if _MACRO_DEF_RE.match(ln.prose) else _blank_args(ln.prose)
        rows.append(_Row(i, ln, text, region, section, heading, i in suppress_at))
    return rows


# ---------------------------------------------------------------------------
# Hit type
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ReaderFlowHit:
    rule: str
    token: str
    path: str
    line: int
    region: str
    section: str
    excerpt: str
    detail: str
    token_kind: str = ""
    related_path: str = ""
    related_line: int = 0
    suppressed: bool = False

    @property
    def severity(self) -> str:
        return SEVERITY_SUPPRESSED if self.suppressed else SEVERITY_ACTIVE

    def to_dict(self) -> dict:
        return {
            "rule": self.rule,
            "token": self.token,
            "token_kind": self.token_kind,
            "path": self.path,
            "line": self.line,
            "region": self.region,
            "section": self.section,
            "related_path": self.related_path,
            "related_line": self.related_line,
            "severity": self.severity,
            "suppressed": self.suppressed,
            "detail": self.detail,
            "excerpt": self.excerpt,
        }


# ---------------------------------------------------------------------------
# Rule 1: define before use
# ---------------------------------------------------------------------------

_Pos = Tuple[int, int]  # (stream index, column)

_ACRONYM_DEF_RE = re.compile(
    r"((?:[A-Za-z][\w'-]*[ \t~]+){1,6}[A-Za-z][\w'-]*)[ \t~]*\([ \t]*"
    r"(\\emph\{|\\textbf\{)?([A-Z][A-Z0-9]{1,7})(s|\')?\}?[ \t]*\)"
)
_IDENT_RE = re.compile(r"(?<![\w\\{}/.\-$_^])([A-Z][0-9]{1,3})(?![\w$_^])")
_EMPH_RE = re.compile(r"\\(?:emph|textit)\{([^{}]{3,40})\}")
_EMPH_CUE_RE = re.compile(
    r"\b(?:we\s+call|called|termed|we\s+term|known\s+as|define[sd]?|defining|"
    r"denote[sd]?|referred\s+to\s+as|we\s+say|so-called|dubbed|we\s+refer\s+to)\b",
    re.IGNORECASE,
)
_SYMBOL_DEF_RES: Tuple[re.Pattern, ...] = (
    re.compile(
        r"\$([^$\n]{1,24})\$\s*(?:denotes?|stands\s+for|is\s+the|is\s+a|are\s+the|:=)"
    ),
    re.compile(r"\b[Ll]et\s+\$([^$\n]{1,24})\$\s+(?:be|denote)"),
)
_MATH_RE = re.compile(r"\$([^$\n]{1,24})\$")
_APPENDIX_POINTER_RE = re.compile(
    r"appendi(?:x|ces)|\\ref\{app|\\ref\{sec:app", re.IGNORECASE
)


def _initials_match(words: List[str], acronym: str) -> bool:
    letters = [w[0].upper() for w in words if w.lower() not in _STOP_INITIALS]
    full = [w[0].upper() for w in words]
    for cand in (letters, full):
        n = len(acronym)
        if len(cand) >= n and "".join(cand[-n:]) == acronym:
            return True
    # hyphen-split compounds ("non-linear" -> NL)
    split = [p[0].upper() for w in words for p in w.split("-") if p]
    return len(split) >= len(acronym) and "".join(split[-len(acronym) :]) == acronym


def _first_use(
    rows: Sequence[_Row], pattern: "re.Pattern", before: _Pos
) -> Optional[Tuple[_Row, int]]:
    for row in rows:
        if row.idx > before[0]:
            break
        for m in pattern.finditer(row.text):
            if (row.idx, m.start()) < before:
                return row, m.start()
            break
    return None


def _define_before_use(rows: Sequence[_Row]) -> List[ReaderFlowHit]:
    hits: List[ReaderFlowHit] = []
    seen: set = set()

    def emit(kind: str, token: str, use: _Row, defrow: _Row, how: str) -> None:
        key = (kind, token.lower())
        if key in seen:
            return
        seen.add(key)
        detail = (
            f"{kind.replace('_', ' ')} `{token}` is used at "
            f"{use.ln.path}:L{use.ln.lineno} before it is defined at "
            f"{defrow.ln.path}:L{defrow.ln.lineno} ({how})."
        )
        if defrow.region == "appendix" and use.region == "body":
            detail += " The only definition is in the appendix."
        hits.append(
            ReaderFlowHit(
                rule=RULE_DEFINE_BEFORE_USE,
                token=token,
                token_kind=kind,
                path=use.ln.path,
                line=use.ln.lineno,
                region=use.region,
                section=use.section,
                excerpt=_excerpt(use.ln.raw),
                detail=detail,
                related_path=defrow.ln.path,
                related_line=defrow.ln.lineno,
                suppressed=use.suppressed or defrow.suppressed,
            )
        )

    def flag_if_earlier(
        kind: str, token: str, pat: "re.Pattern", defrow: _Row, col: int, how: str
    ):
        found = _first_use(rows, pat, (defrow.idx, col))
        if found is None:
            return
        use, _c = found
        if _APPENDIX_POINTER_RE.search(use.ln.raw):
            return
        emit(kind, token, use, defrow, how)

    for row in rows:
        text = row.text
        for m in _ACRONYM_DEF_RE.finditer(text):
            acr = m.group(3)
            words = re.split(r"[ \t~]+", m.group(1).strip())
            if _initials_match(words, acr):
                pat = re.compile(rf"(?<![\w\\]){re.escape(acr)}s?(?![\w])")
                flag_if_earlier(
                    KIND_ACRONYM,
                    acr,
                    pat,
                    row,
                    m.start(3) - 1,
                    f'expanded as "{m.group(1).strip()}"',
                )
        for m in _EMPH_RE.finditer(text):
            term = " ".join(m.group(1).split())
            if not _EMPH_CUE_RE.search(text) or len(term) < 4:
                continue
            body_words = r"\s+".join(re.escape(w) for w in term.split())
            pat = re.compile(rf"(?<![\w\\{{]){body_words}s?(?![\w}}])", re.IGNORECASE)
            flag_if_earlier(
                KIND_EMPH, term, pat, row, m.start(), "first \\emph definition"
            )
        for ident in {m.group(1) for m in _IDENT_RE.finditer(text)}:
            e = re.escape(ident)
            if not (
                re.search(rf"\(\s*{e}\s*\)", text)
                or re.search(
                    rf"(?<![\w]){e}\s+(?:denotes?|stands\s+for|refers\s+to|means|"
                    rf"is\s+(?:the|a|an|our|defined))\b",
                    text,
                )
                or re.search(
                    rf"\b(?:called|named|denote|define[sd]?|termed|dubbed|labell?ed)\s+"
                    rf"(?:\\\w+\{{)?{e}\b",
                    text,
                )
                or re.search(rf"\\(?:emph|textbf|textit)\{{{e}\}}", text)
                or re.search(rf"(?<![\w]){e}\s*(?::|:=)", text)
            ):
                continue
            pat = re.compile(rf"(?<![\w\\{{}}/.\-$_^]){e}(?![\w$_^])")
            col = pat.search(text).start() if pat.search(text) else 0
            flag_if_earlier(KIND_IDENTIFIER, ident, pat, row, col, "defining sentence")
        for dpat in _SYMBOL_DEF_RES:
            for m in dpat.finditer(text):
                sym = m.group(1).strip()
                pat = re.compile(rf"\$\s*{re.escape(sym)}\s*\$")
                flag_if_earlier(
                    KIND_SYMBOL, f"${sym}$", pat, row, m.start(), "defining sentence"
                )
    return hits


# ---------------------------------------------------------------------------
# Rule 2: variant pairs
# ---------------------------------------------------------------------------

_ORDINALS = {
    "first": ("a", "1", "i"),
    "second": ("b", "2", "ii"),
    "third": ("c", "3", "iii"),
    "fourth": ("d", "4", "iv"),
}
_ORD_NOUN_RE = re.compile(
    r"\b(first|second|third|fourth)\s+([a-z]{4,})\b", re.IGNORECASE
)
_NOUN_STOP = frozenset(
    "time times place order step steps case cases part parts half stage "
    "that this these those which where there their other approach example "
    "section sections row rows column columns".split()
)
_HYPHEN_RE = re.compile(r"\b([A-Za-z]{3,})-([A-Za-z]{2,})\b")


def _find_text(rows: Sequence[_Row], pattern: "re.Pattern") -> Optional[_Row]:
    for row in rows:
        if pattern.search(row.text):
            return row
    return None


def _variant_pairs(rows: Sequence[_Row]) -> List[ReaderFlowHit]:
    hits: List[ReaderFlowHit] = []
    seen: set = set()

    def emit(a: str, b: str, ra: _Row, rb: _Row, kind: str) -> None:
        later, earlier = (rb, ra) if rb.idx > ra.idx else (ra, rb)
        key = tuple(sorted((a.lower(), b.lower())))
        if key in seen:
            return
        seen.add(key)
        hits.append(
            ReaderFlowHit(
                rule=RULE_VARIANT_PAIR,
                token=f"{a} / {b}",
                token_kind=kind,
                path=later.ln.path,
                line=later.ln.lineno,
                region=later.region,
                section=later.section,
                excerpt=_excerpt(later.ln.raw),
                detail=(
                    f'"{a}" ({ra.ln.path}:L{ra.ln.lineno}) and "{b}" '
                    f"({rb.ln.path}:L{rb.ln.lineno}) likely name one concept; "
                    f"pick one spelling."
                ),
                related_path=earlier.ln.path,
                related_line=earlier.ln.lineno,
                suppressed=ra.suppressed or rb.suppressed,
            )
        )

    for row in rows:
        for m in _ORD_NOUN_RE.finditer(row.text):
            word, noun = m.group(1).lower(), m.group(2).lower()
            if noun in _NOUN_STOP:
                continue
            for tag in _ORDINALS[word]:
                if tag in ("a", "i"):
                    # the bare-letter form must be the labelled one ("family a"),
                    # never an article ("family a lot")
                    other = re.compile(
                        rf"\b{noun}s?\s+{tag}\b(?=\s*(?:[.,;:)]|$)|\s+(?:and|or|is|are|has|have)\b)"
                    )
                else:
                    other = re.compile(rf"\b{noun}s?\s+{tag}\b")
                hit = _find_text(rows, other)
                if hit is not None:
                    emit(
                        m.group(0),
                        re.search(other, hit.text).group(0),
                        row,
                        hit,
                        "ordinal",
                    )
    # compounds: hyphenated vs spaced vs closed
    counts: Dict[Tuple[str, str], _Row] = {}
    for row in rows:
        for m in _HYPHEN_RE.finditer(row.text):
            counts.setdefault((m.group(1).lower(), m.group(2).lower()), row)
    for (x, y), hrow in counts.items():
        for variant in (rf"\b{x}\s+{y}\b", rf"\b{x}{y}\b"):
            vrow = _find_text(rows, re.compile(variant, re.IGNORECASE))
            if vrow is not None:
                shown = re.search(variant, vrow.text, re.IGNORECASE).group(0)
                emit(f"{x}-{y}", " ".join(shown.split()), hrow, vrow, "compound")
    return hits


# ---------------------------------------------------------------------------
# Rule 3: roadmap order
# ---------------------------------------------------------------------------

_REF_MENTION_RE = re.compile(
    r"(?:Sections?|Sec\.|§)[~\s]*\\(?:auto|c|C)?ref\*?\{([^}]+)\}"
)
_NUM_MENTION_RE = re.compile(r"(?:Sections?|Sec\.|§)[~\s]*(\d{1,2})\b")
_LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
_STARRED_RE = re.compile(r"\\(?:part|chapter|section|subsection|subsubsection)\*")
_INTRO_TITLE_RE = re.compile(r"introduc", re.IGNORECASE)


def _heading_of(row: _Row, *, latex: bool) -> Optional[Tuple[int, str]]:
    if latex:
        m = _LATEX_HEADING_RE.search(row.ln.base)
        if m and not _STARRED_RE.search(row.ln.base):
            return _LATEX_LEVELS[m.group(1)], m.group(2).strip()
        return None
    m = _MD_HEADING_RE.match(row.ln.base)
    return (len(m.group(1)), m.group(2).strip()) if m else None


def _roadmap_order(rows: Sequence[_Row], *, latex: bool) -> List[ReaderFlowHit]:
    headings = [(r, _heading_of(r, latex=latex)) for r in rows if r.region == "body"]
    headings = [(r, h) for r, h in headings if h is not None]
    intro = next((h for h in headings if _INTRO_TITLE_RE.search(h[1][1])), None)
    if intro is None:
        return []
    level = intro[1][0]
    ordinals: List[Tuple[int, str, int]] = []  # (ordinal, title, stream idx)
    for r, (lvl, title) in headings:
        if lvl == level:
            ordinals.append((len(ordinals) + 1, title, r.idx))
    intro_ord = next(o for o, _t, i in ordinals if i == intro[0].idx)
    end_idx = next((i for o, _t, i in ordinals if o == intro_ord + 1), None)

    def ordinal_at(idx: int) -> int:
        cur = 0
        for o, _t, i in ordinals:
            if i <= idx:
                cur = o
        return cur

    label_ord: Dict[str, int] = {}
    last_heading = -10
    for r in rows:
        if r.region != "body":
            continue
        if _heading_of(r, latex=latex) is not None:
            last_heading = r.idx
        for m in _LABEL_RE.finditer(r.ln.prose):
            if r.idx - last_heading <= 2 and ordinal_at(r.idx):
                label_ord.setdefault(m.group(1).strip(), ordinal_at(r.idx))
    titles = {o: t for o, t, _i in ordinals}

    seq: List[Tuple[int, _Row]] = []
    for r in rows:
        if (
            r.region != "body"
            or r.idx < intro[0].idx
            or (end_idx is not None and r.idx >= end_idx)
        ):
            continue
        mentions: List[Tuple[int, int]] = []
        for m in _REF_MENTION_RE.finditer(r.ln.prose):
            for lab in m.group(1).split(","):
                o = label_ord.get(lab.strip())
                if o:
                    mentions.append((m.start(), o))
        for m in _NUM_MENTION_RE.finditer(r.ln.prose):
            o = int(m.group(1))
            if o in titles:
                mentions.append((m.start(), o))
        for _pos, o in sorted(mentions):
            if o > intro_ord and all(o != s[0] for s in seq):
                seq.append((o, r))

    hits: List[ReaderFlowHit] = []
    top_o, top_row = 0, None
    for o, r in seq:
        if o < top_o and top_row is not None:
            hits.append(
                ReaderFlowHit(
                    rule=RULE_ROADMAP_ORDER,
                    token=f"{titles[top_o]} → {titles[o]}",
                    path=r.ln.path,
                    line=r.ln.lineno,
                    region=r.region,
                    section=r.section,
                    excerpt=_excerpt(r.ln.raw),
                    detail=(
                        f"The introduction names section {top_o} "
                        f'("{titles[top_o]}") before section {o} '
                        f'("{titles[o]}"), but the body has "{titles[o]}" first.'
                    ),
                    related_path=top_row.ln.path,
                    related_line=top_row.ln.lineno,
                    suppressed=r.suppressed or top_row.suppressed,
                )
            )
        elif o > top_o:
            top_o, top_row = o, r
    return hits


# ---------------------------------------------------------------------------
# Result + review
# ---------------------------------------------------------------------------

_FIXES = {
    RULE_DEFINE_BEFORE_USE: (
        "Define the token at (or before) its first use, or move the first use "
        "after the definition; in a caption, expand it inline."
    ),
    RULE_VARIANT_PAIR: "Use a single name for the concept throughout.",
    RULE_ROADMAP_ORDER: (
        "Reorder the roadmap to match the body, or reorder the sections to "
        "match the roadmap."
    ),
}


@dataclass
class ReaderFlowResult:
    version_dir: str
    body_path: str
    files: List[str]
    hits: List[ReaderFlowHit]

    @property
    def active_hits(self) -> List[ReaderFlowHit]:
        return [h for h in self.hits if not h.suppressed]

    @property
    def suppressed_hits(self) -> List[ReaderFlowHit]:
        return [h for h in self.hits if h.suppressed]

    def passed(self) -> bool:
        return not self.active_hits

    def counts(self) -> Dict[str, int]:
        return {r: sum(1 for h in self.active_hits if h.rule == r) for r in RULES}

    def to_json(self) -> dict:
        return {
            "check": CHECK_NAME,
            "version_dir": self.version_dir,
            "body_path": self.body_path,
            "files": self.files,
            "passed": self.passed(),
            "counts": self.counts(),
            "suppressed": len(self.suppressed_hits),
            "hits": [h.to_dict() for h in self.hits],
        }

    def to_review(self, *, version_dir: str, critic_id: str = CRITIC_ID) -> Review:
        scores = [
            Score(
                dimension=CHECK_NAME,
                score=None,
                max=1,
                justification=(
                    "reader-flow lint is a deterministic advisory scan; owns "
                    "no rubric dim (evidence for the reader-flow lens and dim 7)."
                ),
            )
        ]
        findings: List[Finding] = []
        for h in self.hits:
            rationale = h.detail
            if h.suppressed:
                rationale = (
                    f"Suppressed ({CHECK_NAME} lint-disable directive; recorded, not counted): "
                    + rationale
                )
            findings.append(
                Finding(
                    severity=h.severity,
                    dimension=DIM_READER_FLOW,
                    evidence_span=f"{h.path}:L{h.line}",
                    rationale=rationale,
                    suggested_fix=_FIXES[h.rule],
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


def find_reader_flow_hits(
    lines: Sequence[_Line], *, latex: bool
) -> List[ReaderFlowHit]:
    """Run all three rules over an already-flattened line stream."""
    rows = _rows(lines, latex=latex)
    hits = (
        _define_before_use(rows)
        + _variant_pairs(rows)
        + _roadmap_order(rows, latex=latex)
    )
    return sorted(hits, key=lambda h: (h.path, h.line, h.rule))


def find_reader_flow_hits_in_text(
    text: str, *, latex: bool = False, path: str = "main.tex"
) -> List[ReaderFlowHit]:
    """Scan one body text (no ``\\input`` expansion). Pure function."""
    from anvil.lib.audience_check import _file_lines

    return find_reader_flow_hits(_file_lines(text, path, latex=latex), latex=latex)


def check_reader_flow(
    version_dir: Path, *, body: Optional[Path] = None
) -> ReaderFlowResult:
    """Run the lint against a version directory (``.tex`` or ``.md`` body)."""
    version_dir = Path(version_dir).resolve()
    if not version_dir.is_dir():
        raise FileNotFoundError(
            f"reader_flow_lint: version_dir {version_dir!s} does not exist "
            f"or is not a directory."
        )
    body_file = resolve_body_path(
        version_dir, body=body, caller_name="reader_flow_lint"
    )
    body_label = record_body_path(version_dir, body_file)
    lines, files = _document_lines(body_file, version_dir, body_label=body_label)
    hits = find_reader_flow_hits(lines, latex=body_file.suffix == ".tex")
    return ReaderFlowResult(
        version_dir=version_dir.name, body_path=body_label, files=files, hits=hits
    )


def write_review_dir(
    version_dir: Path, result: ReaderFlowResult, *, critic_id: str = CRITIC_ID
) -> Path:
    """Write ``<version_dir>.readerflowlint/_review.json`` (atomic, regenerating)."""
    version_dir = Path(version_dir)
    review = result.to_review(version_dir=version_dir.name, critic_id=critic_id)
    return write_critic_review_dir(version_dir, READER_FLOW_SUFFIX, review)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _build_cli_parser():
    import argparse

    p = argparse.ArgumentParser(
        prog="python -m anvil.lib.reader_flow_lint",
        description=(
            "Deterministic define-before-use / variant-name / roadmap-order "
            "lint (advisory). Exit 1 signals findings; it is NOT a blocking verdict."
        ),
    )
    p.add_argument("version_dir", help="Path to <thread>.{N}/.")
    p.add_argument(
        "--write-review",
        action="store_true",
        help="Also write <version_dir>.readerflowlint/_review.json (staged_sidecar).",
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
        result = check_reader_flow(
            Path(args.version_dir), body=Path(args.body) if args.body else None
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
    "DIM_READER_FLOW",
    "READER_FLOW_SUFFIX",
    "RULE_DEFINE_BEFORE_USE",
    "RULE_VARIANT_PAIR",
    "RULE_ROADMAP_ORDER",
    "RULES",
    "ReaderFlowHit",
    "ReaderFlowResult",
    "find_reader_flow_hits",
    "find_reader_flow_hits_in_text",
    "check_reader_flow",
    "write_review_dir",
    "main",
]


if __name__ == "__main__":
    raise SystemExit(main())
