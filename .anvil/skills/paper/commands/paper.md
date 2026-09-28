---
name: paper
description: Portfolio orchestrator for paper threads. Discovers all paper threads under cwd, reports state-machine position per thread, and recommends the next command.
---

# paper — Portfolio orchestrator

**Role**: portfolio orchestrator (read-only; reports state, does not mutate).
**Reads**: all `<thread>.*/` directories under the current working directory.
**Writes**: nothing on disk. Returns a status report.

## Purpose

A single command that an operator (or orchestrating agent) runs to see the state of every paper thread in the portfolio and a recommended next command per thread.

## Inputs

- **CWD**: the portfolio directory containing paper threads.
- **Discovery rule**: a thread is detected by the presence of any `<slug>.{N}/` directory (with `_progress.json`) OR a `<slug>.0.litsearch/` directory (a litsearch-only thread is in state `EMPTY` but is worth surfacing). The slug is the directory name up to the first `.<digit>`. A bare `<slug>/` directory without any versioned siblings is treated as a brief-only thread in state `EMPTY`.

## Procedure

1. Enumerate all directories under cwd matching the pattern `<slug>` or `<slug>.{N}` or `<slug>.{N}.<critic>` (where `<critic>` ∈ {`review`, `audit`, `litsearch`, `critic`, ...}).
2. Group by slug. For each slug, identify:
   - The latest `N` for which `<slug>.{N}/` exists.
   - Whether `<slug>.0.litsearch/` exists (pre-draft).
   - Which sibling critic dirs exist at the latest `N` (`.review/`, `.audit/`, `.litsearch/`, ...).
   - The verdict (advance/block, total /44, critical flags) from `<slug>.{N}.review/verdict.md` if present.
   - The audit flags from `<slug>.{N}.audit/flags.md` if present.
   - The iteration count and `max_iterations` from `<slug>.{N}/_progress.json` (or from `<slug>/.anvil.json` if the per-thread override is set).
3. Compute the state-machine position per thread using the table in `SKILL.md`.
4. Recommend the next command per thread:

   | State | Recommended next command |
   |---|---|
   | `EMPTY` (no litsearch, no version dirs) | `paper-litsearch <thread>` (optional) or `paper-draft <thread>` |
   | `EMPTY` (has `.0.litsearch/` only) | `paper-draft <thread>` |
   | `DRAFTED` | `paper-review <thread>` |
   | `REVIEWED` (advance=false, under iteration cap) | `paper-revise <thread>` |
   | `REVIEWED` (advance=false, AT iteration cap) | `BLOCKED — human review required` |
   | `REVIEWED` (advance=true, no audit yet) | `paper-audit <thread>` |
   | `READY` (advance=true, no figures generated) | `paper-figures <thread>` (then `paper-audit`) |
   | `READY` (advance=true, figures present, no `<thread>.{N}.vision/` sibling at this `N`) | `paper-vision <thread>` (then `paper-audit`) — surface rendered-figure defects before the audit pass so a vision critical flag factors into the same revision as any audit flag |
   | `READY` (advance=true, figures present, `<thread>.{N}.vision/` sibling exists) | `paper-audit <thread>` |
   | `AUDITED` (no critical flags in audit, no figures) | (terminal) |
   | `AUDITED` (no critical flags in audit, figures present, `<thread>.{N}.vision/` sibling exists) | (terminal) |
   | `AUDITED` (no critical flags in audit, figures present, no `<thread>.{N}.vision/` sibling at this `N`) | (terminal — but recommend `paper-vision <thread>`: figures reached terminal without visual review; non-blocking operator note, does not reopen the state machine) |
   | `AUDITED` (critical flags in audit) | `paper-revise <thread>` (audit findings drive a new revision) |

5. Detect anomalies and surface them:
   - A `<slug>.{N}/_progress.json` with any phase in state `in_progress` AND the version dir is older than 10 minutes — likely a crashed phase; recommend resuming.
   - A critic sibling dir (`<slug>.{N}.<critic>/`) without a matching `<slug>.{N}/` — orphan; report. **Exception:** `<slug>.0.litsearch/` is allowed without a matching `<slug>.0/`.
   - A gap in version numbers (e.g., `<slug>.1/` and `<slug>.3/` with no `<slug>.2/`) — report.
   - An audit with unresolved critical flags on a thread the reviewer marked `advance: true` — report as `READY-WITH-AUDIT-FLAGS`, recommend `paper-revise`.
   - A `READY` or `AUDITED` thread with figures generated at the latest `N` (i.e. `<slug>.{N}/figures/` contains at least one rendered file besides the `src/` subdirectory) but no `<slug>.{N}.vision/` sibling at that `N` — report as `NEVER-VISION-CHECKED`, recommend `paper-vision`. This is **informational and non-blocking** (it does not change the reported state and does not reopen the state machine); it exists because `paper-vision` is operator-recommended-but-optional and its rendered-artifact defects (label cropping, axis legibility, mathtext artifacts) are otherwise never surfaced. A thread with **no figures** at the latest `N` never triggers this note (byte-identical routing to a text-only paper).

## Output format

Print a markdown table to stdout:

```
| Thread          | Latest | State    | Score | Iter | Flags | Next                     |
|-----------------|--------|----------|-------|------|-------|--------------------------|
| q3-method       | .2     | REVIEWED | 30/44 | 2/4  | 0     | paper-revise q3-method     |
| acme-bench-2026 | .3     | AUDITED  | 38/44 | 3/4  | 0     | (terminal)               |
| arxiv-survey    | -      | EMPTY    | -     | 0/4  | -     | paper-litsearch arxiv-survey |
```

Follow the table with an `## Anomalies` section if any were detected, and an `## Operator notes` section with any threads requiring human review (iteration cap reached, critical flag unresolved across multiple revisions, etc.).

## Notes

- This command does **not** write to disk. It is safe to run repeatedly.
- The portfolio orchestrator is the recommended user-facing entry point. The six lifecycle commands (`paper-litsearch`, `paper-draft`, `paper-review`, `paper-revise`, `paper-audit`, `paper-figures`) can be invoked directly by an orchestrating agent or by a human operator running them in sequence.
- The `Flags` column counts unresolved critical flags across both `.review/` and `.audit/` siblings at the latest `N`.
