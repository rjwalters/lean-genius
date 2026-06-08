# 1stProof Benchmark — local cache

This directory mirrors the **first-batch** problem statements from the
[First Proof Project](https://1stproof.org/) so that downstream triage and
`/lean` probes can operate from local files instead of re-fetching the upstream
LaTeX on every run.

This is a reference cache, **not** a gallery entry — no `proofs/`,
`src/data/proofs/`, or `research/registry.json` changes are made by the puller.

## Provenance

| Field | Value |
|-------|-------|
| Landing page | <https://1stproof.org/first-batch.html> |
| arXiv id | [2602.05192](https://arxiv.org/abs/2602.05192) |
| LaTeX source | <https://github.com/1stproof/batch-1/blob/main/First_Proof.tex> |
| Raw LaTeX | <https://raw.githubusercontent.com/1stproof/batch-1/main/First_Proof.tex> |
| Last fetch (UTC date) | 2026-06-08 |

The fetch date above is auto-updated by the puller only when the upstream
LaTeX content actually changes (detected via SHA-256). A no-op re-run leaves
the date as-is so the directory is fully idempotent.

## Layout

```
research/references/1stproof/
  README.md                       <- this file
  first-batch/
    first_proof.tex               <- cached upstream LaTeX (verbatim)
    index.json                    <- {problems: [...]}
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
