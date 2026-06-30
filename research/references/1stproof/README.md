# 1stProof Benchmark — local cache

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
| second-batch | <https://1stproof.org/second-batch.html> | `1stproof/batch-2` `batch-2-raw-outputs/Batch2Problems/problems.json` | `scripts/research/pull-1stproof-second-batch.py` |

The two batches use different upstream formats: batch-1 ships one `.tex` with all
ten problems in a single `enumerate` block; batch-2 ships a `problems.json`
whose entries each carry a verbatim LaTeX fragment. The pullers therefore live
in separate files (see issue: Approach B / fork) but share the same idempotency
and cache-layout conventions.

The fetch date in each `index.json` is auto-updated by its puller only when the
upstream source content actually changes (detected via SHA-256). A no-op re-run
leaves the date as-is so the directories are fully idempotent.
Most recent refresh of this README: 2026-06-17.

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
