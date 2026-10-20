# Citation primitive — on-disk shape and convention

This snippet documents the shared filesystem convention every Anvil
skill follows when producing citations. The Python lib that implements
it lives at `anvil/lib/cite.py`; LLMs reading this snippet should
expect the lib (or a deterministic shell-out to it) to handle every
step below.

The lib's job ends at `refs.bib`. **Rendering — CSL styles, pandoc
templates, USPTO formatters — is per-skill.** This boundary keeps the
shared primitive small.

## Per-version-dir `refs.bib`

Each `<thread>.{N}/` version dir owns its own `refs.bib`:

```
acme-seed.3/
  memo.md
  refs.bib                       ← cite primitive writes here
  _progress.json
acme-seed.3.review/
  ...
```

The file is BibTeX 0.99-compatible. Entries are appended in resolve
order with one blank line between entries. Field order within each
entry is fixed for diff-friendliness:

```
@article{kucsko2013nanometre,
  author = {Kucsko, G. and Maurer, P. C. and Yao, N. Y.},
  title = {Nanometre-scale thermometry in a living cell},
  journal = {Nature},
  year = {2013},
  volume = {500},
  number = {7460},
  pages = {54-58},
  doi = {10.1038/nature12373},
  url = {https://doi.org/10.1038/nature12373},
}
```

ArXiv preprints emit as `@misc` with `eprint` + `eprinttype`:

```
@misc{vaswani2017attention,
  author = {Vaswani, Ashish and Shazeer, Noam and ...},
  title = {Attention Is All You Need},
  year = {2017},
  eprint = {1706.03762},
  eprinttype = {arxiv},
  url = {https://arxiv.org/abs/1706.03762},
}
```

Software / dataset DOIs (Zenodo and friends) are **DataCite**-registered,
not Crossref-registered. `resolve()` tries Crossref first and, on a
"not here" 404/406, falls back to DataCite. Those records also emit as
`@misc` (per DataCite's own `types.bibtex` hint), carrying `doi` + `url`
but no `journal` / `volume` — the software analog of an arXiv preprint:

```
@misc{mcconkey2021qiskit,
  author = {McConkey, Thomas G and Minev, Zlatko and Qiskit Metal Development Team},
  title = {Qiskit Metal: An Open-Source Framework for Quantum Device Design & Analysis},
  year = {2021},
  doi = {10.5281/zenodo.4618153},
  url = {https://zenodo.org/record/4618153},
}
```

Author rendering mirrors the Crossref path: DataCite `creators` with a
`familyName`/`givenName` split render surname-first, while organizational
or software authors that carry only `name` (e.g. a "…Development Team")
pass through unchanged.

The writer is **idempotent**: calling `cite(identifier, version_dir)`
twice with the same identifier appends only one entry and returns the
existing `@key` on the second call. Detection is by DOI or arXiv
eprint match against existing entries — full BibTeX parsing is not
required.

## Pandoc-compatible `@key` insertion

The lib's `cite()` returns a pandoc-compatible token (the key with a
leading `@`):

```python
key = cite("10.1038/nature12373", Path("acme-seed.3"))
# key == "@kucsko2013nanometre"
```

The skill's drafter inserts the token inline in the markdown source:

```markdown
Nitrogen-vacancy centers can act as nanoscale thermometers in living
cells [see @kucsko2013nanometre for the seminal demonstration].
```

The skill's render pipeline (pandoc `--citeproc`, USPTO formatter, ...)
expands `@kucsko2013nanometre` into the rendered citation form per its
own CSL / template.

## Citation key format

Keys are deterministic: `<lastname><year><word>`.

- `<lastname>` — the lowercased ASCII-folded surname of the first
  author. Non-ASCII characters fold via NFKD normalization (`Müller`
  → `muller`, `Bañuelos` → `banuelos`).
- `<year>` — 4-digit publication year. `nd` when missing.
- `<word>` — first non-stopword from the title, lowercased and
  ASCII-folded. Stopwords: `a`, `an`, `the`, `on`, `in`, `of`, `for`,
  `to`, `with`, `and`.

Collisions are resolved by appending `b`, `c`, ... when the same key
already exists in the target `refs.bib`. The collision check is
per-file, not global, so two skills sharing a key namespace across
threads is not a concern.

## `~/.cache/anvil/cite/` layout

Resolved bibliographic records cache to the user's home directory:

```
~/.cache/anvil/cite/
  doi/
    10.1038%2Fnature12373.json
  arxiv/
    1706.03762.json
```

- Path is `~/.cache/anvil/cite/<kind>/<urlquoted-value>.json`, where
  `<urlquoted-value>` is `urllib.parse.quote(value, safe="")` to
  handle slashes in DOIs.
- Cache hits skip the network entirely. Cache misses populate
  atomically (write to `.tmp`, then rename).
- The directory is created with mode `0700` on first write.
- No TTL — bibliographic records are stable. A future `cite-refresh`
  command can invalidate manually if needed.
- Set `CITE_CACHE_BYPASS=1` to disable both read and write (for
  debugging the live resolver against the cassette tests).

## Identifier kinds supported in v0

- **DOI** — resolved via Crossref's public API. Polite-pool semantics
  apply (the lib sends a descriptive `User-Agent`). DOIs Crossref does
  not know (Zenodo / software / dataset DOIs return HTTP 404/406) fall
  back to the **DataCite** REST API (`https://api.datacite.org/dois/…`,
  plain unauthenticated GET, stdlib only) before failing. A DOI
  registered with neither registry still raises
  `CiteResolutionError` — the fallback widens the *verifiable* set
  without loosening the verified-or-dropped contract.
- **arXiv** — resolved via the arXiv public API (Atom XML).
- **PubMed (PMID)** — *deferred*. `resolve()` raises
  `UnsupportedIdentifierError`. Track a follow-up issue when a
  consumer skill needs it.
- **URL → BibTeX scraping** — *deferred*. `resolve()` raises
  `UnsupportedIdentifierError`. Track a follow-up issue when a
  consumer skill needs HTML-metadata extraction.

The parser accepts canonical forms for each:

| Kind | Examples |
|---|---|
| DOI | `10.1038/nature12373`, `doi:10.1038/nature12373`, `https://doi.org/10.1038/nature12373`, `https://dx.doi.org/10.1038/nature12373` |
| arXiv | `2305.14325`, `2305.14325v3`, `arxiv:2305.14325`, `https://arxiv.org/abs/2305.14325` |
| URL | any well-formed `http(s)://...` URL (parses but does not resolve) |

## Citation quality rubric dimensions

Skills that care about citation quality opt in to two rubric
dimensions (per `rubric.md`):

- **`citation_recall`** — claims-with-citations / total-claims.
- **`citation_precision`** — claims-supported-by-cited-source /
  claims-with-citations.

These are first-class dimensions, not sub-fields of `evidence` or any
other dim, because the `Score` model in `review_schema.py` enforces
one integer score per dimension. The two-dim shape lets each axis
move independently.

STORM (stanford-oval/storm) reports 84.83% / 85.18% on these as
feasible targets — useful calibration anchors for new rubric
authors.

The per-consumer rubric migration (splitting an existing
citation-related dimension into `citation_recall` +
`citation_precision`) is **separate work** from the lib. Each skill
that opts in does so in its own follow-up PR. The lib pins the
dimension naming convention only.

## The CSL boundary

`cite.py` produces BibTeX. CSL style files are not its concern.

Consumer skills ship their own CSL when they want one — typically as
an asset under `.anvil/skills/<skill>/assets/<style>.csl`, picked up
by the skill's render command. The lib documents the convention but
does **not** ship any CSL file. APA-7 is the conventional default
for academic/markdown skills (`paper`, `report`, `memo`); USPTO
formatting is bespoke and renders without CSL.

## BibTeX 0.99 field reference

The lib emits a small subset of BibTeX 0.99:

| Field | Used in | Notes |
|---|---|---|
| `author` | all | ` and `-joined surname-first list |
| `title` | all | |
| `journal` | `@article` | Crossref's first `container-title` |
| `year` | all | 4-digit string |
| `volume` | `@article` | |
| `number` | `@article` | (called "issue" in Crossref) |
| `pages` | `@article` | |
| `doi` | `@article`, `@misc` | Bare `10.xxxx/yyyy` form (DataCite `@misc` software/dataset records carry one too) |
| `eprint` | `@misc` | arXiv ID without version suffix |
| `eprinttype` | `@misc` | always `arxiv` in v0 |
| `url` | all | Canonical URL |

Empty / missing fields are omitted entirely (not written as empty
strings). For the full BibTeX field vocabulary, see
[bibtex.org](http://www.bibtex.org/Format/).

## See also

- `rubric.md` — citation-quality dimension naming convention.
- `critics.md` — how the citation auditor populates its partial
  scorecard.
- `version_layout.md` — the `<thread>.{N}/` convention `refs.bib`
  lives in.
