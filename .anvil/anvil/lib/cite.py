"""Shared citation primitive for Anvil skills.

This module is the lib-side companion to the markdown convention
documented in ``anvil/lib/snippets/cite.md``. It owns:

- **Identifier parsing.** DOI / arXiv / URL strings normalized to a typed
  ``Identifier``.
- **Resolution.** Crossref (for DOIs) and arXiv (for arXiv IDs) queried
  via ``urllib.request``. DOIs that Crossref does not know (e.g.
  Zenodo / software / dataset DOIs, which return HTTP 404/406) fall back
  to the DataCite REST API before failing, so mechanically-verifiable
  software citations resolve to ``@software`` / ``@misc`` records instead
  of being dropped. Network failures retry with exponential backoff.
  ``UnsupportedIdentifierError`` for v0-deferred kinds (``pmid``, ``url``).
- **Citation key generation.** Deterministic ``<lastname><year><word>``
  with stopword skipping, ASCII folding, and per-file collision suffixes.
- **Cache.** ``~/.cache/anvil/cite/<kind>/<sanitized-value>.json`` with
  atomic writes. ``CITE_CACHE_BYPASS=1`` opts out.
- **Per-version-dir ``refs.bib`` writer.** Idempotent — re-resolving the
  same identifier appends nothing and returns the existing ``@key``.

Design notes
------------

- **Stdlib only.** ``urllib.request`` + ``xml.etree.ElementTree`` only.
  ``pydantic`` is already in use by ``review_schema.py`` so the typed
  models match that convention.
- **CSL boundary.** This lib produces BibTeX. CSL style files are the
  consumer's responsibility; nothing in this module knows about CSL.
- **No live network in tests.** Tests patch ``urllib.request.urlopen``
  with fixture cassettes under ``tests/lib/cassettes/cite/``. A single
  ``@pytest.mark.network`` test exists for smoke checks; CI does not
  run it.

See ``anvil/lib/snippets/cite.md`` for the on-disk convention shared with
LLM-side authoring.
"""

from __future__ import annotations

import json
import os
import re
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
from enum import Enum
from pathlib import Path
from typing import List, Literal, Optional, Union
from xml.etree import ElementTree as ET

from pydantic import BaseModel, ConfigDict, Field

from anvil.lib.atomic_write import atomic_write_text


# ---------------------------------------------------------------------------
# Types
# ---------------------------------------------------------------------------


class IdentifierKind(str, Enum):
    """Citation identifier kind.

    ``DOI`` and ``ARXIV`` are resolved in v0. ``PMID`` and ``URL`` are
    accepted by ``parse_identifier`` but raise
    ``UnsupportedIdentifierError`` at ``resolve()`` time. Track follow-ups
    if a consumer skill needs them.
    """

    DOI = "doi"
    ARXIV = "arxiv"
    PMID = "pmid"
    URL = "url"


class Identifier(BaseModel):
    """A parsed citation identifier.

    ``value`` is the normalized form: DOIs strip the scheme, arXiv IDs
    strip the version suffix, URLs are stored as-is.
    """

    model_config = ConfigDict(extra="forbid")

    kind: IdentifierKind = Field(..., description="The identifier kind.")
    value: str = Field(
        ...,
        description=(
            "The normalized identifier value. DOI: '10.xxxx/yyyy' "
            "(scheme stripped). arXiv: '2305.14325' (version stripped). "
            "URL: the original URL string."
        ),
    )


class BibRecord(BaseModel):
    """A bibliographic record resolved from an external API.

    Field names mirror the BibTeX 0.99 field vocabulary. ``key`` is set
    by ``bib_key()`` at write time; resolvers leave it ``None``.
    """

    model_config = ConfigDict(extra="forbid")

    key: Optional[str] = Field(
        None,
        description=(
            "BibTeX entry key. Filled in by ``bib_key()`` at write time. "
            "Resolvers leave this ``None``."
        ),
    )
    entry_type: Literal["article", "misc", "inproceedings", "book"] = Field(
        ...,
        description=(
            "BibTeX entry type. ``article`` for Crossref journal articles; "
            "``misc`` for arXiv preprints in v0. ``inproceedings`` and "
            "``book`` are reserved for future resolvers."
        ),
    )
    authors: List[str] = Field(
        ...,
        description=(
            "Author list in surname-first canonical form, e.g. "
            "'Smith, John'. BibTeX joins these with ' and ' on emission."
        ),
    )
    title: str = Field(..., description="The work's title.")
    year: int = Field(..., description="4-digit publication year.")
    journal: Optional[str] = Field(
        None, description="Journal / container title (article only)."
    )
    volume: Optional[str] = Field(None, description="Journal volume.")
    issue: Optional[str] = Field(None, description="Journal issue.")
    pages: Optional[str] = Field(None, description="Page range, e.g. '54-58'.")
    doi: Optional[str] = Field(None, description="DOI in '10.xxxx/yyyy' form.")
    eprint: Optional[str] = Field(
        None,
        description=(
            "Preprint ID, e.g. arXiv ID. Paired with ``eprinttype``."
        ),
    )
    eprinttype: Optional[Literal["arxiv"]] = Field(
        None, description="Preprint archive identifier, only 'arxiv' in v0."
    )
    url: Optional[str] = Field(None, description="Canonical URL.")


class CiteResolutionError(Exception):
    """Network or parse failure while resolving an identifier.

    Raised after retries exhaust against Crossref, DataCite, or arXiv. The
    original ``urllib`` error is chained via ``__cause__``.

    ``status_code`` carries the HTTP status when the failure was a
    definitive 4xx (e.g. a Crossref 404 for a DOI not registered there),
    and ``None`` for network / parse failures. The DataCite fallback in
    :func:`_resolve_doi` inspects this to decide whether a Crossref miss
    is worth a second registry lookup.
    """

    def __init__(self, message: str, status_code: Optional[int] = None):
        super().__init__(message)
        self.status_code = status_code


class UnsupportedIdentifierError(Exception):
    """Raised when ``resolve()`` cannot handle the identifier's kind.

    v0 supports ``DOI`` and ``ARXIV``. ``PMID`` and ``URL`` raise this
    exception (track follow-ups when a consumer skill needs them).
    """


# ---------------------------------------------------------------------------
# Identifier parsing
# ---------------------------------------------------------------------------


_DOI_BARE_RE = re.compile(r"^10\.\d{4,9}/\S+$")
_DOI_URL_RE = re.compile(
    r"^https?://(?:dx\.)?doi\.org/(10\.\d{4,9}/\S+)$",
    re.IGNORECASE,
)
_DOI_PREFIX_RE = re.compile(r"^doi:\s*(10\.\d{4,9}/\S+)$", re.IGNORECASE)

_ARXIV_BARE_RE = re.compile(r"^(\d{4}\.\d{4,5})(v\d+)?$")
_ARXIV_OLD_RE = re.compile(
    r"^([a-z\-]+(?:\.[A-Z]{2})?/\d{7})(v\d+)?$",
    re.IGNORECASE,
)
_ARXIV_PREFIX_RE = re.compile(
    r"^arxiv:\s*(\d{4}\.\d{4,5}|[a-z\-]+(?:\.[A-Z]{2})?/\d{7})(v\d+)?$",
    re.IGNORECASE,
)
_ARXIV_URL_RE = re.compile(
    r"^https?://arxiv\.org/abs/"
    r"(\d{4}\.\d{4,5}|[a-z\-]+(?:\.[A-Z]{2})?/\d{7})(v\d+)?/?$",
    re.IGNORECASE,
)

_URL_RE = re.compile(r"^https?://\S+$", re.IGNORECASE)


def parse_identifier(s: str) -> Identifier:
    """Parse a string into a typed :class:`Identifier`.

    Recognized forms:

    - DOI: ``10.xxxx/yyyy``, ``doi:10.xxxx/yyyy``,
      ``https://doi.org/10.xxxx/yyyy``, ``https://dx.doi.org/...``.
    - arXiv: ``2305.14325``, ``2305.14325v3``, ``arxiv:2305.14325``,
      ``https://arxiv.org/abs/2305.14325``. Old-style IDs
      (``cs.LG/0701001``) also parse. Version suffix is stripped.
    - URL: any well-formed ``http(s)://...`` URL not matched above —
      returns ``IdentifierKind.URL``. ``resolve()`` raises
      ``UnsupportedIdentifierError`` for URL kinds in v0.

    Raises:
        ValueError: when ``s`` does not match any recognized form.
    """

    if not s or not isinstance(s, str):
        raise ValueError(f"identifier must be a non-empty string, got {s!r}")

    raw = s.strip()
    if not raw:
        raise ValueError("identifier must not be empty after stripping")

    # DOI variants — check before generic URL.
    m = _DOI_URL_RE.match(raw)
    if m:
        return Identifier(kind=IdentifierKind.DOI, value=m.group(1))
    m = _DOI_PREFIX_RE.match(raw)
    if m:
        return Identifier(kind=IdentifierKind.DOI, value=m.group(1))

    # arXiv variants — check before generic URL / bare DOI.
    m = _ARXIV_URL_RE.match(raw)
    if m:
        return Identifier(kind=IdentifierKind.ARXIV, value=m.group(1))
    m = _ARXIV_PREFIX_RE.match(raw)
    if m:
        return Identifier(kind=IdentifierKind.ARXIV, value=m.group(1))

    # Bare DOI / arXiv. ArXiv bare must come before bare DOI because the
    # DOI prefix '10.xxxx/...' is more permissive and could otherwise
    # accept arXiv-shaped strings (though in practice they share no
    # prefix character set).
    m = _ARXIV_BARE_RE.match(raw)
    if m:
        return Identifier(kind=IdentifierKind.ARXIV, value=m.group(1))
    m = _ARXIV_OLD_RE.match(raw)
    if m:
        return Identifier(kind=IdentifierKind.ARXIV, value=m.group(1))
    if _DOI_BARE_RE.match(raw):
        return Identifier(kind=IdentifierKind.DOI, value=raw)

    # Generic URL fallback. resolve() will raise UnsupportedIdentifierError.
    if _URL_RE.match(raw):
        return Identifier(kind=IdentifierKind.URL, value=raw)

    raise ValueError(
        f"unrecognized identifier shape: {raw!r}. Supported forms: "
        f"DOI ('10.xxxx/yyyy' or 'https://doi.org/...'), "
        f"arXiv ('2305.14325' or 'https://arxiv.org/abs/...'), "
        f"or a well-formed http(s) URL."
    )


# ---------------------------------------------------------------------------
# Cache
# ---------------------------------------------------------------------------


_CACHE_ROOT = Path(os.path.expanduser("~/.cache/anvil/cite"))


def _cache_path(identifier: Identifier) -> Path:
    sanitized = urllib.parse.quote(identifier.value, safe="")
    return _CACHE_ROOT / identifier.kind.value / f"{sanitized}.json"


def _cache_bypass() -> bool:
    return os.environ.get("CITE_CACHE_BYPASS") == "1"


def _cache_read(identifier: Identifier) -> Optional[BibRecord]:
    if _cache_bypass():
        return None
    path = _cache_path(identifier)
    if not path.exists():
        return None
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        return BibRecord.model_validate(data)
    except (OSError, json.JSONDecodeError, ValueError):
        # Corrupt cache: treat as miss; do not surface error to caller.
        return None


def _cache_write(identifier: Identifier, record: BibRecord) -> None:
    if _cache_bypass():
        return
    path = _cache_path(identifier)
    path.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
    atomic_write_text(path, record.model_dump_json())


# ---------------------------------------------------------------------------
# Network helpers
# ---------------------------------------------------------------------------


# Polite-pool User-Agent. Crossref recommends including a contact email
# in the agent string; arXiv has no such requirement but accepts it.
_USER_AGENT = "anvil-cite/0.0.1 (https://github.com/rjwalters/anvil)"

# Per-attempt timeout (seconds) and the backoff schedule. Three attempts
# total: initial + two retries at 1s and 2s. HTTP 4xx is NOT retried.
_TIMEOUT_S = 15.0
_RETRY_DELAYS = (1.0, 2.0)


def _http_get(url: str) -> bytes:
    """Fetch a URL with retry-on-transient-failure.

    Retries up to 2 times after the initial attempt with a 1s, 2s backoff
    on ``URLError`` (DNS / connection / read failures). HTTP 4xx is not
    retried; HTTP 5xx is treated as transient and retried.

    Raises:
        CiteResolutionError: when all attempts fail. The underlying
            ``urllib`` error is chained.
    """

    req = urllib.request.Request(url, headers={"User-Agent": _USER_AGENT})
    last_err: Optional[BaseException] = None
    for attempt in range(len(_RETRY_DELAYS) + 1):
        try:
            with urllib.request.urlopen(req, timeout=_TIMEOUT_S) as resp:
                return resp.read()
        except urllib.error.HTTPError as e:
            # 4xx is a definitive answer — do not retry. Thread the status
            # code through so callers (e.g. the DataCite fallback) can act
            # on a specific code without parsing the message string.
            if 400 <= e.code < 500:
                raise CiteResolutionError(
                    f"HTTP {e.code} fetching {url}: {e.reason}",
                    status_code=e.code,
                ) from e
            last_err = e
        except urllib.error.URLError as e:
            last_err = e
        if attempt < len(_RETRY_DELAYS):
            time.sleep(_RETRY_DELAYS[attempt])
    raise CiteResolutionError(
        f"network failure after {len(_RETRY_DELAYS) + 1} attempts "
        f"fetching {url}"
    ) from last_err


# ---------------------------------------------------------------------------
# Resolvers
# ---------------------------------------------------------------------------


def _crossref_author(a: dict) -> str:
    """Render a Crossref author dict to surname-first BibTeX form.

    Crossref returns ``{"family": "Smith", "given": "John"}``.
    Some entries (corporate authors, software) have only ``name``.
    """

    family = (a.get("family") or "").strip()
    given = (a.get("given") or "").strip()
    if family and given:
        return f"{family}, {given}"
    if family:
        return family
    name = (a.get("name") or "").strip()
    return name


def _crossref_year(message: dict) -> int:
    """Extract a 4-digit year from a Crossref ``message`` dict.

    Preference order: published-print > published-online > issued >
    created. Returns 0 only if every candidate is missing or malformed
    (extremely unusual for Crossref records).
    """

    for field in ("published-print", "published-online", "issued", "created"):
        date = message.get(field)
        if not date:
            continue
        parts = date.get("date-parts")
        if parts and parts[0] and isinstance(parts[0][0], int):
            return int(parts[0][0])
    return 0


# Crossref returns these codes for a DOI it does not have registered
# (Zenodo / software / dataset DOIs live in DataCite, not Crossref).
# Only these trigger the DataCite fallback; other 4xx (e.g. a
# genuinely malformed request) surface as-is.
_CROSSREF_MISS_CODES = frozenset({404, 406})


def _resolve_doi(identifier: Identifier) -> BibRecord:
    """Resolve a DOI, trying Crossref first then DataCite.

    Crossref owns journal-article DOIs; DataCite owns Zenodo / software /
    dataset DOIs. When Crossref returns a definitive miss (HTTP 404/406 —
    "not registered here"), fall back to DataCite before giving up. A DOI
    unknown to *both* registries still raises ``CiteResolutionError``,
    preserving the verified-or-dropped invariant.
    """

    url = f"https://api.crossref.org/works/{urllib.parse.quote(identifier.value, safe='/')}"
    try:
        raw = _http_get(url)
    except CiteResolutionError as e:
        if e.status_code in _CROSSREF_MISS_CODES:
            # Not in Crossref — try DataCite. A DataCite miss re-raises,
            # so garbage DOIs unknown to both registries still fail.
            return _resolve_datacite(identifier)
        raise
    try:
        data = json.loads(raw)
    except json.JSONDecodeError as e:
        raise CiteResolutionError(
            f"non-JSON response from Crossref for {identifier.value}"
        ) from e
    msg = data.get("message")
    if not isinstance(msg, dict):
        raise CiteResolutionError(
            f"Crossref response missing 'message' field for {identifier.value}"
        )
    authors = [_crossref_author(a) for a in msg.get("author") or []]
    authors = [a for a in authors if a]
    title_list = msg.get("title") or []
    title = title_list[0] if title_list else ""
    container_list = msg.get("container-title") or []
    journal = container_list[0] if container_list else None
    return BibRecord(
        entry_type="article",
        authors=authors,
        title=title,
        year=_crossref_year(msg),
        journal=journal,
        volume=(str(msg["volume"]) if msg.get("volume") is not None else None),
        issue=(str(msg["issue"]) if msg.get("issue") is not None else None),
        pages=msg.get("page"),
        doi=msg.get("DOI"),
        url=msg.get("URL"),
    )


# DataCite's ``attributes.types.bibtex`` hint maps CSL/resource types to a
# BibTeX entry type. Values outside the ``BibRecord.entry_type`` Literal
# (e.g. ``phdthesis``, ``techreport``) collapse to ``misc`` — the safe
# catch-all for software / dataset records, and the same type arXiv
# preprints already use.
_DATACITE_BIBTEX_TYPES = frozenset(
    {"article", "misc", "inproceedings", "book"}
)


def _datacite_author(c: dict) -> str:
    """Render a DataCite ``creators`` entry to surname-first BibTeX form.

    DataCite splits some creators into ``familyName`` / ``givenName``;
    organizational and software authors carry only ``name``. Mirror the
    family/given-first fallback used for Crossref (:func:`_crossref_author`)
    so both registries render author names the same way.
    """

    family = (c.get("familyName") or "").strip()
    given = (c.get("givenName") or "").strip()
    if family and given:
        return f"{family}, {given}"
    if family:
        return family
    name = (c.get("name") or "").strip()
    return name


def _datacite_entry_type(
    attrs: dict,
) -> Literal["article", "misc", "inproceedings", "book"]:
    """Choose a BibTeX entry type from a DataCite ``attributes`` dict.

    Honors DataCite's own ``types.bibtex`` hint when it names a type the
    ``BibRecord`` Literal supports; otherwise falls back to ``misc``
    (software, datasets, and anything unrecognized).
    """

    types = attrs.get("types")
    if isinstance(types, dict):
        hint = (types.get("bibtex") or "").strip().lower()
        if hint in _DATACITE_BIBTEX_TYPES:
            return hint  # type: ignore[return-value]
    return "misc"


def _resolve_datacite(identifier: Identifier) -> BibRecord:
    """Resolve a DOI via the DataCite REST API.

    Called only as a Crossref fallback (see :func:`_resolve_doi`). Uses a
    plain unauthenticated ``urllib`` GET — stdlib only, same shape as the
    Crossref path. A DataCite miss (HTTP 404/406) raises
    ``CiteResolutionError`` like any other unresolvable identifier.
    """

    url = (
        "https://api.datacite.org/dois/"
        f"{urllib.parse.quote(identifier.value, safe='/')}"
    )
    raw = _http_get(url)
    try:
        data = json.loads(raw)
    except json.JSONDecodeError as e:
        raise CiteResolutionError(
            f"non-JSON response from DataCite for {identifier.value}"
        ) from e
    attrs = (data.get("data") or {}).get("attributes")
    if not isinstance(attrs, dict):
        raise CiteResolutionError(
            "DataCite response missing 'data.attributes' field for "
            f"{identifier.value}"
        )

    authors = [_datacite_author(c) for c in attrs.get("creators") or []]
    authors = [a for a in authors if a]

    title_list = attrs.get("titles") or []
    title = ""
    if title_list and isinstance(title_list[0], dict):
        title = (title_list[0].get("title") or "").strip()

    year = 0
    pub_year = attrs.get("publicationYear")
    if isinstance(pub_year, int):
        year = pub_year
    elif isinstance(pub_year, str) and pub_year[:4].isdigit():
        year = int(pub_year[:4])

    # Prefer the registry's own canonical URL; fall back to the doi.org
    # resolver form so the field is never empty for a resolved record.
    doi_value = attrs.get("doi") or identifier.value
    url_value = attrs.get("url") or f"https://doi.org/{doi_value}"

    return BibRecord(
        entry_type=_datacite_entry_type(attrs),
        authors=authors,
        title=title,
        year=year,
        doi=doi_value,
        url=url_value,
    )


# arXiv Atom namespace constants.
_ATOM_NS = "{http://www.w3.org/2005/Atom}"


def _resolve_arxiv(identifier: Identifier) -> BibRecord:
    url = (
        "https://export.arxiv.org/api/query?"
        f"id_list={urllib.parse.quote(identifier.value, safe='/')}"
    )
    raw = _http_get(url)
    try:
        feed = ET.fromstring(raw)
    except ET.ParseError as e:
        raise CiteResolutionError(
            f"non-XML response from arXiv for {identifier.value}"
        ) from e
    entry = feed.find(f"{_ATOM_NS}entry")
    if entry is None:
        raise CiteResolutionError(
            f"arXiv response has no <entry> for {identifier.value}"
        )

    # title — collapse interior newlines per the Atom convention.
    title_el = entry.find(f"{_ATOM_NS}title")
    title = ""
    if title_el is not None and title_el.text:
        title = " ".join(title_el.text.split())

    authors: List[str] = []
    for a in entry.findall(f"{_ATOM_NS}author"):
        name_el = a.find(f"{_ATOM_NS}name")
        if name_el is not None and name_el.text:
            # arXiv lists "Given Family"; convert to "Family, Given".
            name = name_el.text.strip()
            parts = name.rsplit(" ", 1)
            if len(parts) == 2:
                authors.append(f"{parts[1]}, {parts[0]}")
            else:
                authors.append(name)

    # year — pull from <published> (preferred) or <updated>.
    year = 0
    for tag in ("published", "updated"):
        el = entry.find(f"{_ATOM_NS}{tag}")
        if el is not None and el.text and len(el.text) >= 4:
            try:
                year = int(el.text[:4])
                break
            except ValueError:
                continue

    # canonical abs URL (without version suffix for stability).
    abs_url = f"https://arxiv.org/abs/{identifier.value}"

    return BibRecord(
        entry_type="misc",
        authors=authors,
        title=title,
        year=year,
        eprint=identifier.value,
        eprinttype="arxiv",
        url=abs_url,
    )


def resolve(identifier: Union[Identifier, str]) -> BibRecord:
    """Resolve an identifier to a :class:`BibRecord`.

    Accepts either a typed :class:`Identifier` or a raw string (which is
    parsed via :func:`parse_identifier` first).

    Cache-first: a hit on ``~/.cache/anvil/cite/`` skips the network.
    Cache misses populate the cache atomically. The cache key is the DOI
    itself, so DataCite-resolved records share the ``doi/`` namespace with
    Crossref-resolved ones — no per-registry cache split.

    DOI resolution tries Crossref first, then DataCite when Crossref
    reports the DOI is not registered there (HTTP 404/406).

    Args:
        identifier: typed identifier or raw string.

    Returns:
        A :class:`BibRecord` with ``key`` left ``None`` (filled in by
        :func:`bib_key` at write time).

    Raises:
        UnsupportedIdentifierError: for ``PMID`` and ``URL`` kinds in v0.
        CiteResolutionError: on persistent network or parse failures, or
            when a DOI is registered with neither Crossref nor DataCite.
    """

    if isinstance(identifier, str):
        identifier = parse_identifier(identifier)

    if identifier.kind in (IdentifierKind.PMID, IdentifierKind.URL):
        raise UnsupportedIdentifierError(
            f"identifier kind {identifier.kind.value!r} is not supported "
            f"in v0; track follow-up issues for PubMed and URL→BibTeX."
        )

    cached = _cache_read(identifier)
    if cached is not None:
        return cached

    if identifier.kind == IdentifierKind.DOI:
        record = _resolve_doi(identifier)
    elif identifier.kind == IdentifierKind.ARXIV:
        record = _resolve_arxiv(identifier)
    else:  # pragma: no cover - exhaustive by enum
        raise UnsupportedIdentifierError(
            f"no resolver for {identifier.kind.value!r}"
        )

    _cache_write(identifier, record)
    return record


# ---------------------------------------------------------------------------
# Citation key generation
# ---------------------------------------------------------------------------


# Standard small stopword list per the curator spec.
_STOPWORDS = frozenset(
    ["a", "an", "the", "on", "in", "of", "for", "to", "with", "and"]
)


def _ascii_fold(s: str) -> str:
    """Fold a string to ASCII via NFKD normalization.

    Diacritics are dropped (``ü`` → ``u``, ``é`` → ``e``). Non-letter,
    non-digit characters are then stripped. Result is lowercase.
    """

    normalized = unicodedata.normalize("NFKD", s)
    ascii_only = "".join(c for c in normalized if not unicodedata.combining(c))
    return "".join(c for c in ascii_only if c.isalnum()).lower()


def _first_nonstop_word(title: str) -> str:
    """First non-stopword from a title, ASCII-folded and lowercased.

    Splits on whitespace and punctuation. Returns empty string if the
    title is empty or contains only stopwords.
    """

    # Replace non-word characters with spaces, then split.
    cleaned = re.sub(r"[^\w\s]", " ", title)
    for word in cleaned.split():
        folded = _ascii_fold(word)
        if folded and folded not in _STOPWORDS:
            return folded
    return ""


def _existing_keys(refs_bib: Path) -> set:
    """Read existing entry keys from a ``refs.bib`` file.

    Returns an empty set if the file does not exist. Detection is
    regex-based: ``@type{key,`` at line start.
    """

    if not refs_bib.exists():
        return set()
    text = refs_bib.read_text(encoding="utf-8")
    return set(re.findall(r"^@\w+\{([^,]+),", text, flags=re.MULTILINE))


def bib_key(record: BibRecord, refs_bib: Optional[Path] = None) -> str:
    """Generate a deterministic, collision-resolved BibTeX key.

    Format: ``<lastname><year><word>``, e.g. ``smith2024transformers``.

    - ``<lastname>``: lowercased ASCII-folded surname of the first
      author. If the canonical form is ``Family, Given``, ``Family`` is
      taken.
    - ``<year>``: 4-digit year as a string.
    - ``<word>``: first non-stopword from the title, lowercased and
      ASCII-folded.

    If ``refs_bib`` is provided and the generated key already appears in
    that file, ``b``, ``c``, ... are appended until the key is unique.
    The collision check is per-file, not global.
    """

    surname = ""
    if record.authors:
        first = record.authors[0]
        # surname-first canonical form: "Family, Given"
        family = first.split(",", 1)[0]
        surname = _ascii_fold(family)
    year = str(record.year) if record.year else "nd"
    word = _first_nonstop_word(record.title or "")
    base = f"{surname}{year}{word}" or "ref"

    if refs_bib is None:
        return base
    existing = _existing_keys(refs_bib)
    if base not in existing:
        return base
    # Append 'b', 'c', ... until unique. Skip 'a' so the base form has
    # no suffix — matches the bibtex/pandoc convention.
    for suffix_ord in range(ord("b"), ord("z") + 1):
        candidate = f"{base}{chr(suffix_ord)}"
        if candidate not in existing:
            return candidate
    raise CiteResolutionError(
        f"more than 25 collisions on bib key {base!r}; refusing to extend "
        f"beyond 'z'. Curate refs.bib manually."
    )


# ---------------------------------------------------------------------------
# BibTeX emission
# ---------------------------------------------------------------------------


# Field emission order per BibTeX 0.99 convention.
_FIELD_ORDER = (
    "author",
    "title",
    "journal",
    "year",
    "volume",
    "number",
    "pages",
    "doi",
    "eprint",
    "eprinttype",
    "url",
)


def _format_entry(record: BibRecord) -> str:
    """Render a :class:`BibRecord` to a BibTeX 0.99 entry string.

    Empty / None fields are omitted entirely. Multi-author lists use
    ``" and "``. The entry's key MUST be filled in (``record.key``).
    """

    if not record.key:
        raise ValueError("BibRecord.key must be set before emission")
    fields = {
        "author": " and ".join(record.authors) if record.authors else None,
        "title": record.title or None,
        "journal": record.journal,
        "year": str(record.year) if record.year else None,
        "volume": record.volume,
        "number": record.issue,
        "pages": record.pages,
        "doi": record.doi,
        "eprint": record.eprint,
        "eprinttype": record.eprinttype,
        "url": record.url,
    }
    lines = [f"@{record.entry_type}{{{record.key},"]
    for name in _FIELD_ORDER:
        val = fields.get(name)
        if not val:
            continue
        lines.append(f"  {name} = {{{val}}},")
    lines.append("}")
    return "\n".join(lines)


def _refs_bib_contains(refs_bib: Path, record: BibRecord) -> Optional[str]:
    """Check whether ``refs_bib`` already has an entry for this record.

    Detection is by DOI (preferred) or arXiv eprint. Returns the existing
    key if found, ``None`` otherwise.

    Full BibTeX parsing is overkill — we only need to match against the
    one or two identifying fields we wrote ourselves.
    """

    if not refs_bib.exists():
        return None
    text = refs_bib.read_text(encoding="utf-8")
    # Split into entries by '@type{...}'. Regex is intentionally loose;
    # we only need to find ``key`` and the doi/eprint field within it.
    entry_re = re.compile(
        r"@\w+\{([^,]+),(.*?)\n\}",
        flags=re.DOTALL,
    )
    for m in entry_re.finditer(text):
        key = m.group(1).strip()
        body = m.group(2)
        if record.doi:
            doi_match = re.search(
                r"\bdoi\s*=\s*\{([^}]+)\}", body, flags=re.IGNORECASE
            )
            if doi_match and doi_match.group(1).strip() == record.doi:
                return key
        if record.eprint:
            ep_match = re.search(
                r"\beprint\s*=\s*\{([^}]+)\}", body, flags=re.IGNORECASE
            )
            if ep_match and ep_match.group(1).strip() == record.eprint:
                return key
    return None


def cite(identifier: Union[Identifier, str], version_dir: Path) -> str:
    """Resolve an identifier and write its BibTeX entry to ``refs.bib``.

    This is the top-level convenience entry point. The full pipeline:

    1. Parse the identifier (string or typed).
    2. Resolve to a :class:`BibRecord` (cache-first).
    3. Check ``<version_dir>/refs.bib`` for an existing entry with the
       same DOI or arXiv eprint. If found, return the existing key.
    4. Otherwise, generate a collision-free bib key via :func:`bib_key`,
       append the formatted entry to ``refs.bib``, and return the key.

    Args:
        identifier: typed :class:`Identifier` or raw string.
        version_dir: the ``<thread>.{N}/`` directory whose ``refs.bib``
            should receive the entry. Created if missing.

    Returns:
        The pandoc-compatible ``@key`` token (e.g. ``"@smith2024foo"``).
    """

    version_dir = Path(version_dir)
    version_dir.mkdir(parents=True, exist_ok=True)
    refs_bib = version_dir / "refs.bib"

    record = resolve(identifier)

    # Idempotency: if this record's DOI / eprint is already in refs.bib,
    # return the existing key without appending.
    existing = _refs_bib_contains(refs_bib, record)
    if existing:
        return f"@{existing}"

    key = bib_key(record, refs_bib=refs_bib)
    # Stamp the key on the record before formatting.
    stamped = record.model_copy(update={"key": key})
    entry_text = _format_entry(stamped)

    # Append with one blank line separator before the new entry when the
    # file is non-empty.
    with refs_bib.open("a", encoding="utf-8") as f:
        if refs_bib.stat().st_size > 0:
            f.write("\n")
        f.write(entry_text)
        f.write("\n")

    return f"@{key}"


__all__ = [
    "Identifier",
    "IdentifierKind",
    "BibRecord",
    "CiteResolutionError",
    "UnsupportedIdentifierError",
    "parse_identifier",
    "resolve",
    "bib_key",
    "cite",
]
