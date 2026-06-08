#!/usr/bin/env python3
"""Pull 1stProof first-batch problem statements from GitHub LaTeX source.

The 1stProof benchmark (https://1stproof.org/first-batch.html) publishes 10
research-level math problems. Statements live in a single LaTeX source file
on GitHub (1stproof/batch-1, file First_Proof.tex), inside an `enumerate`
block in `\\section{The questions}`. Each `\\item` is one problem.

Usage:
    pull-1stproof-first-batch.py                  Pull from the canonical URL
    pull-1stproof-first-batch.py --source PATH    Use a local .tex file
    pull-1stproof-first-batch.py --help           Show this help

Output (relative to repo root):
    research/references/1stproof/
      README.md
      first-batch/
        first_proof.tex                # cached upstream LaTeX
        index.json                     # {problems: [{id, slug, area, ...}]}
        problems/
          01-<slug>.md
          ...
          10-<slug>.md

The script is idempotent: re-running with the same source produces identical
output (modulo the `fetch_date` field in `index.json`, which is bumped only
when the cached source file content changes).
"""

from __future__ import annotations

import argparse
import datetime as _dt
import hashlib
import json
import pathlib
import re
import sys
import urllib.request

# Canonical sources.
RAW_TEX_URL = "https://raw.githubusercontent.com/1stproof/batch-1/main/First_Proof.tex"
GITHUB_BLOB_URL = "https://github.com/1stproof/batch-1/blob/main/First_Proof.tex"
ARXIV_ABS_URL = "https://arxiv.org/abs/2602.05192"
ARXIV_ID = "2602.05192"
LANDING_URL = "https://1stproof.org/first-batch.html"

# One-line area + slug per problem, in the order the authors used in the paper.
# These are determined by reading the LaTeX once and recording the topic stated
# on the landing page next to the matching mathematical content. They are NOT
# extracted from the LaTeX automatically (the source carries no per-item area
# tags), so this table is the single hand-maintained mapping. If the upstream
# source ever reorders or renumbers the problems, this table must be updated.
PROBLEM_METADATA: list[dict[str, str]] = [
    {
        "id": 1,
        "slug": "phi43-shift-equivalence",
        "area": "stochastic analysis",
        "short_title": "Equivalence of shifted Phi^4_3 measures on T^3",
    },
    {
        "id": 2,
        "slug": "rankin-selberg-nonvanishing",
        "area": "representation theory",
        "short_title": "Nonvanishing local Rankin-Selberg integral on GL_{n+1}",
    },
    {
        "id": 3,
        "slug": "interpolation-asep-markov-chain",
        "area": "algebraic combinatorics",
        "short_title": "Markov chain for interpolation ASEP / Macdonald ratio",
    },
    {
        "id": 4,
        "slug": "polynomial-convolution-phi-bound",
        "area": "spectral graph theory",
        "short_title": "Boxplus convolution and Phi_n bound for real-rooted polynomials",
    },
    {
        "id": 5,
        "slug": "n-infty-slice-filtration",
        "area": "algebraic topology",
        "short_title": "O-slice filtration and geometric fixed-point connectivity",
    },
    {
        "id": 6,
        "slug": "epsilon-light-laplacian-subset",
        "area": "spectral graph theory",
        "short_title": "Existence of epsilon-light vertex subsets of size c*epsilon*|V|",
    },
    {
        "id": 7,
        "slug": "uniform-lattice-rational-acyclic-cover",
        "area": "lattices in Lie groups",
        "short_title": "Uniform lattice with 2-torsion as pi_1 of Q-acyclic-cover manifold",
    },
    {
        "id": 8,
        "slug": "polyhedral-lagrangian-smoothing",
        "area": "symplectic geometry",
        "short_title": "Lagrangian smoothing of 4-valent polyhedral Lagrangian surfaces",
    },
    {
        "id": 9,
        "slug": "generic-3x4-determinant-tensor-relations",
        "area": "tensor analysis",
        "short_title": "Algebraic relations among 3x3x3x3 det-tensors of generic 3x4 matrices",
    },
    {
        "id": 10,
        "slug": "cp-rkhs-pcg-mode-subproblem",
        "area": "numerical linear algebra",
        "short_title": "Preconditioned CG for RKHS-constrained CP-decomposition mode subproblem",
    },
]


def fetch_tex(source: str | None) -> str:
    """Return LaTeX source text. If source is None, fetch from RAW_TEX_URL."""
    if source is None:
        with urllib.request.urlopen(RAW_TEX_URL, timeout=30) as resp:
            data = resp.read()
        text = data.decode("utf-8")
    else:
        text = pathlib.Path(source).read_text(encoding="utf-8")
    return text


# Regex anchors. We do NOT try to "parse" arbitrary LaTeX; we rely on the very
# specific structure used by First_Proof.tex:
#
#   \section{The questions}\label{sec:problems}
#
#   \begin{enumerate}
#   \item ... problem 1 ...
#   \item ... problem 2 ...
#   ...
#   \item ... problem 10 ...
#   \end{enumerate}
#
# If the upstream file diverges from this structure the script will fail loudly
# (raise) rather than silently produce garbage.
SECTION_RE = re.compile(
    r"\\section\{The questions\}\s*\\label\{sec:problems\}(?P<rest>.*?)\\section\{",
    re.DOTALL,
)
ENUMERATE_RE = re.compile(
    r"\\begin\{enumerate\}(?P<body>.*?)\\end\{enumerate\}",
    re.DOTALL,
)


_BEGIN_RE = re.compile(r"\\begin\{([a-zA-Z*]+)\}")
_END_RE = re.compile(r"\\end\{([a-zA-Z*]+)\}")
_ITEM_RE = re.compile(r"(?m)^\s*\\item\b")


def _split_top_level_items(body: str) -> list[str]:
    """Split body on `\\item` only when nesting depth is 0.

    A `\\item` inside a nested `\\begin{itemize}...\\end{itemize}` (or any other
    nested environment) belongs to that inner list, not to the outer
    `enumerate`. We track depth by walking the string and finding the next
    `\\begin{...}`, `\\end{...}`, or top-level `\\item` boundary at each step.
    """
    # Build a sorted list of (position, kind, span_end) events.
    events: list[tuple[int, str, int]] = []
    for m in _BEGIN_RE.finditer(body):
        events.append((m.start(), "begin", m.end()))
    for m in _END_RE.finditer(body):
        events.append((m.start(), "end", m.end()))
    for m in _ITEM_RE.finditer(body):
        events.append((m.start(), "item", m.end()))
    events.sort(key=lambda e: e[0])

    items: list[str] = []
    depth = 0
    current_start: int | None = None
    for pos, kind, end in events:
        if kind == "begin":
            depth += 1
        elif kind == "end":
            depth -= 1
        elif kind == "item":
            if depth == 0:
                # Close previous item (if any) at this position.
                if current_start is not None:
                    items.append(body[current_start:pos].strip())
                current_start = end  # start of new item body, after `\item`
    # Close the trailing item: from current_start to end of body.
    if current_start is not None:
        items.append(body[current_start:].strip())
    return items


def extract_problem_statements(tex: str) -> list[str]:
    """Return the list of 10 raw-LaTeX problem statements.

    Raises ValueError if the source doesn't have the expected structure.
    """
    section_match = SECTION_RE.search(tex)
    if section_match is None:
        raise ValueError(
            "Could not locate '\\section{The questions}\\label{sec:problems}' "
            "section in the source. Upstream LaTeX structure may have changed."
        )
    enum_match = ENUMERATE_RE.search(section_match.group("rest"))
    if enum_match is None:
        raise ValueError(
            "Found 'The questions' section but no \\begin{enumerate}...\\end{enumerate} "
            "block inside it. Upstream LaTeX structure may have changed."
        )
    body = enum_match.group("body")
    items = _split_top_level_items(body)
    items = [it for it in items if it]
    if len(items) != 10:
        raise ValueError(
            f"Expected exactly 10 top-level \\item entries inside the enumerate "
            f"block, got {len(items)}. Upstream LaTeX structure may have changed."
        )
    return items


def write_problem_markdown(
    path: pathlib.Path,
    meta: dict[str, str],
    statement_tex: str,
    *,
    arxiv_id: str,
    source_blob_url: str,
) -> None:
    """Write a single problem .md file with YAML-like frontmatter + raw LaTeX."""
    md = (
        f"# Problem {meta['id']}: {meta['short_title']}\n\n"
        f"- **Area:** {meta['area']}\n"
        f"- **Source:** [First_Proof.tex]({source_blob_url}) "
        f"(arXiv [{arxiv_id}](https://arxiv.org/abs/{arxiv_id}))\n"
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
            "arxiv_id": ARXIV_ID,
            "arxiv_abs_url": ARXIV_ABS_URL,
            "github_blob_url": GITHUB_BLOB_URL,
            "raw_tex_url": RAW_TEX_URL,
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
    readme = f"""# 1stProof Benchmark — local cache

This directory mirrors the **first-batch** problem statements from the
[First Proof Project](https://1stproof.org/) so that downstream triage and
`/lean` probes can operate from local files instead of re-fetching the upstream
LaTeX on every run.

This is a reference cache, **not** a gallery entry — no `proofs/`,
`src/data/proofs/`, or `research/registry.json` changes are made by the puller.

## Provenance

| Field | Value |
|-------|-------|
| Landing page | <{LANDING_URL}> |
| arXiv id | [{ARXIV_ID}]({ARXIV_ABS_URL}) |
| LaTeX source | <{GITHUB_BLOB_URL}> |
| Raw LaTeX | <{RAW_TEX_URL}> |
| Last fetch (UTC date) | {fetch_date} |

The fetch date above is auto-updated by the puller only when the upstream
LaTeX content actually changes (detected via SHA-256). A no-op re-run leaves
the date as-is so the directory is fully idempotent.

## Layout

```
research/references/1stproof/
  README.md                       <- this file
  first-batch/
    first_proof.tex               <- cached upstream LaTeX (verbatim)
    index.json                    <- {{problems: [...]}}
    problems/
      01-<slug>.md ... 10-<slug>.md
```

Each problem markdown file contains:
- short title and area
- a link back to the upstream source
- the verbatim LaTeX statement (no transcription / rewording)

## How to refresh

```bash
./scripts/research/pull-1stproof-first-batch.py
```

The script is safe to re-run. If the upstream LaTeX has not changed, the
output is byte-identical to the previous run.

To pin to a specific local copy of the `.tex` (e.g. for reproducibility):

```bash
./scripts/research/pull-1stproof-first-batch.py --source path/to/First_Proof.tex
```

## Scope

This cache covers **only** problem-statement retrieval and storage. Triage,
`/lean` probe orchestration, the June 2026 second-batch window, and any
trial writeups are tracked separately in the parent issue
(see the issue referenced in the PR that introduced this directory).
"""
    path.write_text(readme, encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Pull 1stProof first-batch problem statements into research/references/1stproof/."
    )
    parser.add_argument(
        "--source",
        help="Path to a local copy of First_Proof.tex (default: fetch from GitHub raw).",
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
        # scripts/research/pull-1stproof-first-batch.py -> repo root is two levels up.
        repo_root = pathlib.Path(__file__).resolve().parents[2]

    out_dir = repo_root / "research" / "references" / "1stproof"
    first_batch_dir = out_dir / "first-batch"
    problems_dir = first_batch_dir / "problems"
    problems_dir.mkdir(parents=True, exist_ok=True)

    tex = fetch_tex(args.source)
    source_sha256 = hashlib.sha256(tex.encode("utf-8")).hexdigest()

    cached_tex_path = first_batch_dir / "first_proof.tex"
    prev_sha = None
    if cached_tex_path.exists():
        prev_sha = hashlib.sha256(
            cached_tex_path.read_bytes()
        ).hexdigest()

    # Only bump fetch_date when content actually changed.
    today = _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%d")
    if prev_sha != source_sha256 or not (first_batch_dir / "index.json").exists():
        fetch_date = today
    else:
        # Reuse previous date from index.json if present.
        try:
            prev_index = json.loads(
                (first_batch_dir / "index.json").read_text(encoding="utf-8")
            )
            fetch_date = prev_index.get("source", {}).get("fetch_date", today)
        except Exception:
            fetch_date = today

    statements = extract_problem_statements(tex)
    if len(statements) != len(PROBLEM_METADATA):
        raise ValueError(
            f"Mismatch between extracted statements ({len(statements)}) and "
            f"hand-maintained metadata table ({len(PROBLEM_METADATA)})."
        )

    cached_tex_path.write_text(tex, encoding="utf-8")

    entries: list[dict[str, object]] = []
    for meta, statement in zip(PROBLEM_METADATA, statements):
        filename = f"{meta['id']:02d}-{meta['slug']}.md"
        path = problems_dir / filename
        write_problem_markdown(
            path,
            meta,
            statement,
            arxiv_id=ARXIV_ID,
            source_blob_url=GITHUB_BLOB_URL,
        )
        entries.append(
            {
                "id": meta["id"],
                "slug": meta["slug"],
                "area": meta["area"],
                "short_title": meta["short_title"],
                "statement_path": f"first-batch/problems/{filename}",
            }
        )

    write_index_json(
        first_batch_dir / "index.json",
        entries,
        fetch_date=fetch_date,
        source_sha256=source_sha256,
    )
    write_readme(out_dir / "README.md", fetch_date)

    print(
        f"Wrote {len(entries)} problem statements to {first_batch_dir.relative_to(repo_root)}",
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
