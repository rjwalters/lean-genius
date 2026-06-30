#!/usr/bin/env python3
"""Pull 1stProof second-batch problem statements from the GitHub source.

The 1stProof benchmark (https://1stproof.org/second-batch.html) published a
second batch of 10 research-level math problems in June 2026. Unlike batch-1 --
which shipped a single ``First_Proof.tex`` with all ten problems inside one
``\\begin{enumerate}`` block under ``\\section{The questions}`` -- batch-2's
canonical machine-readable problem source is a JSON file:

    1stproof/batch-2  ->  batch-2-raw-outputs/Batch2Problems/problems.json

That file is the literal input the AI systems were given. It is a JSON object
``{"problems": [{"id": "prob-001", "latex": "..."}, ...]}`` where each entry's
``latex`` field is the verbatim problem statement (LaTeX fragment, not a full
document). Because the upstream structure is completely different from batch-1
(JSON-of-fragments vs. one enumerate-in-a-.tex), this is a FORK of
``pull-1stproof-first-batch.py`` rather than a parameterisation of it -- see the
issue's "Implementation choices" (Approach B). The two scripts share only the
idempotency / hash-gated-``fetch_date`` / cache-layout conventions, not the
LaTeX extraction logic.

Usage:
    pull-1stproof-second-batch.py                  Pull from the canonical URL
    pull-1stproof-second-batch.py --source PATH    Use a local problems.json
    pull-1stproof-second-batch.py --help           Show this help

Output (relative to repo root):
    research/references/1stproof/
      README.md                          (shared; updated to mention batch-2)
      second-batch/
        problems.json                    # cached upstream JSON (verbatim)
        index.json                       # {problems: [{id, slug, area, ...}]}
        problems/
          01-<slug>.md
          ...
          10-<slug>.md

The script is idempotent: re-running with the same source produces identical
output (modulo the ``fetch_date`` field in ``index.json``, which is bumped only
when the cached source file content changes).
"""

from __future__ import annotations

import argparse
import datetime as _dt
import hashlib
import json
import pathlib
import sys
import urllib.request

# Canonical sources.
#
# The machine-readable problem statements live in the raw-outputs directory of
# the batch-2 repo (the literal input handed to the AI systems). There is no
# single "Second_Proof.tex" analogous to batch-1's First_Proof.tex; the per-AI
# *.tex files under batch-2-AI-solutions/ are SOLUTIONS, not the statements.
_SOURCE_REL = "batch-2-raw-outputs/Batch2Problems/problems.json"
RAW_JSON_URL = f"https://raw.githubusercontent.com/1stproof/batch-2/main/{_SOURCE_REL}"
GITHUB_BLOB_URL = f"https://github.com/1stproof/batch-2/blob/main/{_SOURCE_REL}"
GITHUB_REPO_URL = "https://github.com/1stproof/batch-2"
LANDING_URL = "https://1stproof.org/second-batch.html"

# One-line area + slug + short title per problem, keyed by the upstream ``id``.
#
# As with batch-1, these are NOT extracted from the source automatically: the
# upstream ``problems.json`` carries only an ``id`` and a verbatim ``latex``
# field -- no per-problem area tag, slug, or title. This table is the single
# hand-maintained mapping, produced by reading each problem's LaTeX and
# recording the mathematical subject area. The batch-2 landing page (unlike
# batch-1's) does not list per-problem areas, so the area below is assigned by
# subject-matter classification of the statement itself.
#
# If the upstream source ever reorders, renumbers, or changes its ``id`` scheme,
# this table must be updated (the script keys on ``id`` and fails loudly on a
# mismatch).
PROBLEM_METADATA: list[dict[str, object]] = [
    {
        "id": 1,
        "source_id": "prob-001",
        "slug": "aut-countable-non-sigma1-automorphism",
        "area": "computability theory",
        "short_title": (
            "Computably AUT-countable-on-a-cone structure with no "
            "Sigma^in_1-definable automorphism"
        ),
    },
    {
        "id": 2,
        "source_id": "prob-002",
        "slug": "sqrt3-infimum-squeeze-realized-numbers",
        "area": "geometric topology",
        "short_title": (
            "sqrt(3) as the infimum of realized squeeze-map numbers for "
            "G_beta-invariant clean triangulations"
        ),
    },
    {
        "id": 3,
        "source_id": "prob-003",
        "slug": "weighted-bernoulli-sum-tail-bound",
        "area": "probability theory",
        "short_title": "Values of p with Pr[sum w_i v_i >= p] >= p for weighted Bernoulli sums",
    },
    {
        "id": 4,
        "source_id": "prob-004",
        "slug": "two-dilation-degree-one-rectangle-inequality",
        "area": "metric geometry",
        "short_title": "Area inequality for degree-1, 2-dilation-bounded maps between 4-rectangles",
    },
    {
        "id": 5,
        "source_id": "prob-005",
        "slug": "sticky-reflected-spde-invariant-measure-uniqueness",
        "area": "stochastic PDE",
        "short_title": "Uniqueness of the invariant measure for a sticky-reflected stochastic heat equation",
    },
    {
        "id": 6,
        "source_id": "prob-006",
        "slug": "irreducible-lattice-element-weighted-tree",
        "area": "lattice theory",
        "short_title": "Existence of an irreducible lattice element in a positive-definite weighted tree",
    },
    {
        "id": 7,
        "source_id": "prob-007",
        "slug": "matching-complex-quasi-reduced-word-contractibility",
        "area": "geometric group theory",
        "short_title": "Contractibility of the matching complex F_w of a reducible quasi-reduced word",
    },
    {
        "id": 8,
        "source_id": "prob-008",
        "slug": "relative-dressian-order-reversing-involution",
        "area": "tropical geometry",
        "short_title": "Extending a flat-duality involution to the relative Dressian of a matroid",
    },
    {
        "id": 9,
        "source_id": "prob-009",
        "slug": "multigraded-coinvariant-hook-coefficient-interpretation",
        "area": "algebraic combinatorics",
        "short_title": (
            "Combinatorial interpretation of hook-shape Schur coefficients in the "
            "multigraded coinvariant Hilbert series"
        ),
    },
    {
        "id": 10,
        "source_id": "prob-010",
        "slug": "graph-product-von-neumann-proper-proximality",
        "area": "operator algebras",
        "short_title": "Proper proximality of graph product von Neumann algebras over irreducible graphs",
    },
]


def fetch_json(source: str | None) -> str:
    """Return the raw JSON source text. If source is None, fetch from RAW_JSON_URL."""
    if source is None:
        with urllib.request.urlopen(RAW_JSON_URL, timeout=30) as resp:
            data = resp.read()
        text = data.decode("utf-8")
    else:
        text = pathlib.Path(source).read_text(encoding="utf-8")
    return text


def extract_problem_statements(raw_json: str) -> list[dict[str, str]]:
    """Return the list of problem dicts ``{"source_id", "latex"}`` from the JSON.

    Raises ValueError if the source doesn't have the expected structure. We do
    NOT reformat or re-wrap the ``latex`` field -- it is stored verbatim.
    """
    try:
        payload = json.loads(raw_json)
    except json.JSONDecodeError as exc:
        raise ValueError(
            f"Source is not valid JSON; upstream format may have changed: {exc}"
        ) from exc

    problems = payload.get("problems")
    if not isinstance(problems, list):
        raise ValueError(
            "Source JSON has no top-level 'problems' array. Upstream structure "
            "may have changed."
        )

    statements: list[dict[str, str]] = []
    for i, entry in enumerate(problems):
        if not isinstance(entry, dict) or "latex" not in entry:
            raise ValueError(
                f"Problem entry #{i} is missing a 'latex' field. Upstream "
                "structure may have changed."
            )
        latex = entry["latex"]
        if not isinstance(latex, str) or not latex.strip():
            raise ValueError(
                f"Problem entry #{i} has an empty or non-string 'latex' field."
            )
        statements.append(
            {
                "source_id": str(entry.get("id", f"prob-{i + 1:03d}")),
                "latex": latex,
            }
        )

    if len(statements) != len(PROBLEM_METADATA):
        raise ValueError(
            f"Expected exactly {len(PROBLEM_METADATA)} problems in the source, "
            f"got {len(statements)}. Upstream may have changed; update "
            "PROBLEM_METADATA."
        )
    return statements


def write_problem_markdown(
    path: pathlib.Path,
    meta: dict[str, object],
    statement_tex: str,
    *,
    source_blob_url: str,
) -> None:
    """Write a single problem .md file with a short header + raw LaTeX."""
    md = (
        f"# Problem {meta['id']}: {meta['short_title']}\n\n"
        f"- **Area:** {meta['area']}\n"
        f"- **Source:** [problems.json]({source_blob_url}) "
        f"(upstream id `{meta['source_id']}`)\n"
        f"- **Slug:** `{meta['slug']}`\n\n"
        f"## Statement (verbatim LaTeX from upstream)\n\n"
        f"```latex\n"
        f"{statement_tex.rstrip()}\n"
        f"```\n"
    )
    path.write_text(md, encoding="utf-8")


def write_index_json(
    path: pathlib.Path,
    entries: list[dict[str, object]],
    *,
    fetch_date: str,
    source_sha256: str,
) -> None:
    payload = {
        "source": {
            "landing_page": LANDING_URL,
            "github_repo_url": GITHUB_REPO_URL,
            "github_blob_url": GITHUB_BLOB_URL,
            "raw_json_url": RAW_JSON_URL,
            "fetch_date": fetch_date,
            "source_sha256": source_sha256,
        },
        "problems": entries,
    }
    path.write_text(
        json.dumps(payload, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def write_readme(path: pathlib.Path, fetch_date: str) -> None:
    """Rewrite the shared 1stproof/README.md to cover both batches."""
    readme = f"""# 1stProof Benchmark — local cache

This directory mirrors the problem statements from the
[First Proof Project](https://1stproof.org/) so that downstream triage and
`/lean` probes can operate from local files instead of re-fetching the upstream
sources on every run.

This is a reference cache, **not** a gallery entry — no `proofs/`,
`src/data/proofs/`, or `research/registry.json` changes are made by the pullers.

## Batches

| Batch | Landing page | Upstream source | Puller |
|-------|--------------|-----------------|--------|
| first-batch | <https://1stproof.org/first-batch.html> | `1stproof/batch-1` `First_Proof.tex` | `scripts/research/pull-1stproof-first-batch.py` |
| second-batch | <{LANDING_URL}> | `1stproof/batch-2` `{_SOURCE_REL}` | `scripts/research/pull-1stproof-second-batch.py` |

The two batches use different upstream formats: batch-1 ships one `.tex` with all
ten problems in a single `enumerate` block; batch-2 ships a `problems.json`
whose entries each carry a verbatim LaTeX fragment. The pullers therefore live
in separate files (see issue: Approach B / fork) but share the same idempotency
and cache-layout conventions.

The fetch date in each `index.json` is auto-updated by its puller only when the
upstream source content actually changes (detected via SHA-256). A no-op re-run
leaves the date as-is so the directories are fully idempotent.
Most recent refresh of this README: {fetch_date}.

## Layout

```
research/references/1stproof/
  README.md                       <- this file
  first-batch/
    first_proof.tex               <- cached upstream LaTeX (verbatim)
    index.json
    problems/01-<slug>.md ... 10-<slug>.md
  second-batch/
    problems.json                 <- cached upstream JSON (verbatim)
    index.json
    problems/01-<slug>.md ... 10-<slug>.md
```

Each problem markdown file contains:
- short title and area
- a link back to the upstream source
- the verbatim LaTeX statement (no transcription / rewording)

## How to refresh

```bash
./scripts/research/pull-1stproof-first-batch.py    # batch-1
./scripts/research/pull-1stproof-second-batch.py   # batch-2
```

The scripts are safe to re-run. If the upstream source has not changed, the
output is byte-identical to the previous run. Pin to a local copy with
`--source path/to/source` for reproducibility.

## Scope

This cache covers **only** problem-statement retrieval and storage. Triage,
`/lean` probe orchestration, and comparison against the official solutions are
tracked separately.
"""
    path.write_text(readme, encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Pull 1stProof second-batch problem statements into "
            "research/references/1stproof/second-batch/."
        )
    )
    parser.add_argument(
        "--source",
        help="Path to a local copy of problems.json (default: fetch from GitHub raw).",
        default=None,
    )
    parser.add_argument(
        "--out-root",
        help="Repo root to write under (default: auto-detected from this script's location).",
        default=None,
    )
    args = parser.parse_args(argv)

    if args.out_root is not None:
        repo_root = pathlib.Path(args.out_root).resolve()
    else:
        # scripts/research/pull-1stproof-second-batch.py -> repo root is two levels up.
        repo_root = pathlib.Path(__file__).resolve().parents[2]

    out_dir = repo_root / "research" / "references" / "1stproof"
    batch_dir = out_dir / "second-batch"
    problems_dir = batch_dir / "problems"
    problems_dir.mkdir(parents=True, exist_ok=True)

    raw_json = fetch_json(args.source)
    source_sha256 = hashlib.sha256(raw_json.encode("utf-8")).hexdigest()

    cached_json_path = batch_dir / "problems.json"
    prev_sha = None
    if cached_json_path.exists():
        prev_sha = hashlib.sha256(cached_json_path.read_bytes()).hexdigest()

    # Only bump fetch_date when content actually changed.
    today = _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%d")
    if prev_sha != source_sha256 or not (batch_dir / "index.json").exists():
        fetch_date = today
    else:
        try:
            prev_index = json.loads(
                (batch_dir / "index.json").read_text(encoding="utf-8")
            )
            fetch_date = prev_index.get("source", {}).get("fetch_date", today)
        except Exception:
            fetch_date = today

    statements = extract_problem_statements(raw_json)

    cached_json_path.write_text(raw_json, encoding="utf-8")

    entries: list[dict[str, object]] = []
    for meta, statement in zip(PROBLEM_METADATA, statements):
        # Sanity-check the hand-maintained table is still aligned with upstream.
        if meta["source_id"] != statement["source_id"]:
            raise ValueError(
                f"Metadata/source id mismatch at position {meta['id']}: "
                f"table says {meta['source_id']!r}, source says "
                f"{statement['source_id']!r}. Update PROBLEM_METADATA."
            )
        filename = f"{meta['id']:02d}-{meta['slug']}.md"
        path = problems_dir / filename
        write_problem_markdown(
            path,
            meta,
            statement["latex"],
            source_blob_url=GITHUB_BLOB_URL,
        )
        entries.append(
            {
                "id": meta["id"],
                "source_id": meta["source_id"],
                "slug": meta["slug"],
                "area": meta["area"],
                "short_title": meta["short_title"],
                "statement_path": f"second-batch/problems/{filename}",
            }
        )

    write_index_json(
        batch_dir / "index.json",
        entries,
        fetch_date=fetch_date,
        source_sha256=source_sha256,
    )
    write_readme(out_dir / "README.md", fetch_date)

    print(
        f"Wrote {len(entries)} problem statements to {batch_dir.relative_to(repo_root)}",
        file=sys.stdout,
    )
    print(f"  source sha256: {source_sha256}", file=sys.stdout)
    print(f"  fetch_date:    {fetch_date}", file=sys.stdout)
    if prev_sha is not None and prev_sha != source_sha256:
        print("  upstream content CHANGED since last run", file=sys.stdout)
    elif prev_sha == source_sha256:
        print("  upstream content unchanged (idempotent re-run)", file=sys.stdout)
    return 0


if __name__ == "__main__":
    sys.exit(main())
