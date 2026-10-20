# `_progress.json` read-merge-write snippet

Canonical convention for every command that touches a `_progress.json` file.
This is the single source of truth referenced by SKILL.md and command files
across all anvil skills.

## Schema

Every `_progress.json` carries this minimum shape:

```json
{
  "version": 1,
  "thread": "<slug>",
  "phases": {
    "<phase>": {
      "state": "pending|in_progress|done|failed",
      "started":   "<ISO-8601 UTC>",
      "completed": "<ISO-8601 UTC>"
    }
  },
  "metadata": {
    "iteration": <N>,
    "max_iterations": <N>,
    "score_history": [
      { "iteration": 1, "total": 28, "threshold": 32, "rubric_id": "anvil-memo-v1" },
      { "iteration": 2, "total": 30, "threshold": 32, "rubric_id": "anvil-memo-v1" }
    ]
  },
  "termination_reason": "THRESHOLD_MET | CRITICAL_FLAG | STALLED | MAX_ITERATIONS"
}
```

`metadata.score_history` and the top-level `termination_reason` are
**optional** and added by #27 for stable-score termination. See
"Convergence fields" below.

Critic sibling directories (`<thread>.{N}.<tag>/`) carry an additional
top-level field naming the version they critique:

```json
{ "version": 1, "thread": "<slug>", "for_version": <N>, "phases": { ... } }
```

Skill-specific extensions are allowed (e.g., `project: <slug>` for the
report skill; `metadata.audit_summary` for paper-audit's rich nested
metadata; `metadata.revision_mode` + `metadata.revise_force_reason` for
the memo skill's operator-initiated polish-pass audit trail — see
`anvil/skills/memo/commands/memo-revise.md` §"CLI flags" — where
`revision_mode` is `"normal"` (or absent) on the default revise path and
`"polish"` when invoked with `--polish "<reason>"`, and
`revise_force_reason` is `null` (or absent) by default and the verbatim
operator reason string under `--polish`; both fields are audit-trail
only, not scored, not gating, and not state-machine inputs;
`metadata.figure_policy` for the memo skill's migration-time figure-intent
recording — see `anvil/skills/memo/commands/memo-migrate.md`
§"figure_policy classification" — where `"by-design"` records an
operator-intentional figure-less thread (sourced from a
`% anvil:zero-figures-by-design` LaTeX comment in the legacy source),
`"pending"` records the absence of figures with no marker (signals
reviewer the absence may be unintended), and the field is omitted
entirely when figures are present and no policy decision is needed). The
merge rule preserves any extension fields the caller does not touch.

## Phase states

| State | Meaning |
|---|---|
| `pending` | Phase has not started (or was reset after a crash). |
| `in_progress` | Phase is currently running. |
| `done` | Phase completed successfully. The `completed` field is set. |
| `failed` | Phase ran but did not produce valid output. Caller decides whether to retry from `pending` or escalate. |

## Convergence fields (added by #27)

Two optional fields participate in the secondary "stable-score termination"
stop condition. Both are additive and the shallow-merge rule (see
"Read-merge-write recipe" below) preserves them: a command that does not
own these fields will read them, leave them untouched, and write them back.

### `metadata.score_history`

An array of per-iteration scorecard summaries, appended one entry per
review iteration:

```json
"score_history": [
  { "iteration": 1, "total": 28, "threshold": 32, "rubric_id": "anvil-memo-v1" },
  { "iteration": 2, "total": 30, "threshold": 32, "rubric_id": "anvil-memo-v1" },
  { "iteration": 3, "total": null, "threshold": 35, "rubric_id": "anvil-memo-v2" }
]
```

- `iteration`: 1-indexed iteration number, matching `metadata.iteration`
  at the time the entry was appended.
- `total`: the per-version aggregated total from
  `anvil.lib.critics.aggregate`. Use `null` (NOT `0`) when no scorecard
  was produced — e.g., a critical-flag short-circuit fired before the
  reviewer wrote a scorecard.
- `threshold`: the advance threshold at that iteration. Captured per-row
  so a mid-loop threshold override remains auditable.
- `rubric_id`: the stable rubric identifier the reviewer scored against
  (e.g., `"anvil-memo-v1"`, `"anvil-memo-v2"`). Added per issue #346 so
  a thread that spans a rubric migration records which rubric scored
  which iteration — the example above shows a `/40 → /44` migration
  between iterations 2 and 3 (threshold bumped from 32/40 to 35/44 and
  `rubric_id` from `anvil-memo-v1` to `anvil-memo-v2`).

The array is the input to `anvil.lib.convergence.check_stable` and
`anvil.lib.convergence.decide_termination`. The orchestrator extracts the
`total` column in iteration order and passes it as the `history` argument.

The reviser/orchestrator command is responsible for appending the row for
the iteration it just finished. Other commands MUST NOT mutate
`score_history`; they read it as input only.

**Backwards compatibility on `rubric_id`** — required for new entries
(post-issue #346) and absent-tolerated for legacy entries (pre-issue
#346). Readers MUST tolerate a row missing `rubric_id` by treating it
as `"unknown/legacy"` (a downstream consumer aggregating across a
thread that spans the migration knows the row is pre-stamping and was
scored against whatever rubric the skill shipped at the time). The
`check_stable` precedent — it tolerates `None` entries in `history`
without short-circuiting — is the same backwards-compat shape.

### `termination_reason` (top-level)

A top-level field set by the review/revise command **only** when it has
just decided to terminate the convergence loop. Absent (or `null`) on
intermediate iterations. Values:

| Value | Meaning |
|---|---|
| `NO_GO` | A thesis-failure critical flag (type `"no_go"`) is set — terminal verdict `NO-GO` (issue #559). The reviser refuses to proceed; operator override required to resurrect. Highest priority: NO-GO short-circuits every other terminator including `CRITICAL_FLAG` and `THRESHOLD_MET`. |
| `THRESHOLD_MET` | `total >= threshold`, no critical flag — `ADVANCE`. |
| `CRITICAL_FLAG` | A critical flag is set — `BLOCK`. (NOT a `no_go`-typed flag; those route through `NO_GO` above.) |
| `STALLED` | The last `lookback` totals are within `± window` and below threshold — secondary stop condition. Verdict = `STALLED`. |
| `MAX_ITERATIONS` | Iteration cap exhausted without convergence. Verdict stays `REVISE`; the termination reason distinguishes "ran out of budget" from "demonstrated plateau". |

The resolution order is documented in `rubric.md`'s "Convergence logic"
and implemented in `anvil.lib.convergence.decide_termination`. The two
sources MUST agree; the Python implementation is the source of truth for
programmatic use, the snippet for LLM-side authoring.

### `metadata.kill_rationale` (#559)

A one-paragraph operator-readable rationale set **only** when
`termination_reason == "NO_GO"`. The verbatim contents of the triggering
`no_go` critical flag's `justification` field. Authored once at NO-GO
emission time (by `memo-review` step 7); preserved on every subsequent
shallow merge. Other commands MUST NOT mutate it. Absent (or `null`) on
every non-NO-GO termination and on every pre-#559 thread.

### `metadata.no_go_overridden` + `metadata.no_go_override_reason` (#559)

Operator-override audit-trail fields set **only** by the operator-
override path of `memo-revise --override-no-go "<reason>"`. When set on
a version dir's `_progress.json`:

- `metadata.no_go_overridden: true` — the operator explicitly bypassed
  the NO-GO refusal at memo-revise step 4. Downstream readers (orchestrator,
  share script) MAY surface this to distinguish a resurrected thread from
  a fresh one.
- `metadata.no_go_override_reason: "<verbatim>"` — the verbatim
  operator-supplied rationale for the override. Treated identically to
  `metadata.revise_force_reason` from the `--polish` precedent: no
  trimming, no normalization, no truncation beyond what JSON encoding
  requires.

Both fields are absent on every non-override path. The NO-GO override is
**per-version** (audit-trail-only); a thread that resurrects and then
re-earns a `no_go` flag on the resurrected version is in NO-GO again.

### Why this is additive

Both fields are optional and absent in pre-#27 `_progress.json` files. The
shallow-merge rule (every command preserves top-level + `metadata` fields
it does not own) means existing commands that have not been migrated to
write these fields continue to function unchanged. The only command that
needs to know about them is the review/revise command (which appends to
`score_history`) and the orchestrator's stop-condition check (which reads
both).

## Validation discipline

**Validation is by file existence**, not by flag. The presence of `memo.md`
(or `deck.md`, `spec.tex`, `report.md`, etc.) is the source of truth for
"did this phase produce output". `_progress.json` is a resume hint that
helps a crashed command re-enter the right phase. A `phases.draft.state ==
done` without the artifact file present means the JSON is stale; the
command should treat the phase as crashed and re-run.

## Read-merge-write recipe (pseudocode)

```
def write_phase(path, phase, fields):
    if exists(path):
        progress = json.loads(read(path))
    else:
        progress = {"version": 1, "thread": <slug>, "phases": {}, "metadata": {}}

    # Update only this phase; preserve all other phases and top-level fields.
    progress["phases"][phase] = {
        **progress["phases"].get(phase, {}),
        **fields,  # e.g., {"state": "done", "completed": <ISO>}
    }

    write_atomic(path, json.dumps(progress, indent=2))
```

**Merge rule (shallow)**: the command updates one phase, preserves all
others, and preserves any top-level fields it does not own (`metadata`,
`for_version`, `project`, `termination_reason`, skill-specific
extensions). The merge is shallow: do not attempt deep recursive merges
of `metadata` sub-objects unless the specific snippet says otherwise.

Specifically:

- `termination_reason` (top-level, added by #27) is preserved on every
  shallow merge. Only the review/revise command that decided termination
  writes this field. Other commands MUST NOT clear it.
- `metadata.score_history` (added by #27) is preserved on every shallow
  merge. Only the review/revise command that just finished an iteration
  appends to it. Other commands MUST NOT mutate it.

**Atomicity**: write to a temp file in the same directory, then `rename()`
over the target. This avoids corrupting `_progress.json` if the process
is killed mid-write.

## Crash recovery contract

Two shapes apply, distinguished by whether the dir under recovery is a
**version dir** (one canonical artifact file — `memo.md`, `deck.md`,
`spec.tex`, `report.md`, …) or a **critic sibling dir** (six-ish files
with no single canonical one — `verdict.md` + `scoring.md` +
`comments.md` + `_summary.md` + `_meta.json` + `_progress.json` for the
memo-review shape, with audit / narrative / market shapes carrying
different manifests).

### Version dir — single-canonical-output check

If a command finds `phases.<phase>.state == in_progress` and the expected
output file is missing or empty, the command MUST:

1. Treat the phase as crashed.
2. Delete any partial output (e.g., an empty or truncated `memo.md`).
3. Re-enter the phase from `pending` (or directly re-write `in_progress`
   with a fresh `started` timestamp).

If `phases.<phase>.state == done` AND the expected output file is present
and parses, the command is a no-op (idempotent).

### Critic sidecar dir — atomic rename (issue #350)

Critic sibling dirs (`.review/`, `.audit/`, `.narrative/`, `.market/`,
…) write N files with no single canonical "main" file: the studio
canary surfaced 13 partials produced by mid-cycle interrupts in which
some files made it to disk and others did not. The single-canonical-
output check above is **insufficient** at this boundary — a sidecar
with `verdict.md` only, or `_review.json` only, would be silently
discoverable by `anvil/lib/critics.py:discover_critics`.

The canonical recovery shape at the sidecar boundary is **staged-then-
rename**: a critic writes its files into a leading-dot staging dir
`.<slug>.{N}.<tag>.tmp/` (a sibling of the intended final
`<slug>.{N}.<tag>/`), then on clean exit verifies a per-critic
required-files manifest and atomically renames the staging dir to its
final name. The final-named dir only ever exists in **complete** form;
discovery checks "dir exists" and that remains sufficient. The staging
shape is invisible to `discover_critics` (the leading-dot prefix is
rejected by `critics.py:122-129`'s discovery glob, and the staging-name
"tag" segment also carries a dot so the inner tag check rejects it as
well — belt-and-suspenders rejection).

The reference implementation ships at `anvil/lib/sidecar.py`:

```python
from anvil.lib.sidecar import (
    staged_sidecar,
    cleanup_one_staging,
    cleanup_stale_staging,
)

# Per-critic entry-step sweep — called by each command's "Discover
# state" step BEFORE opening the staged_sidecar context. Parallel-safe:
# targets ONLY the staging dir corresponding to this critic's
# final_dir (issue #376).
cleanup_one_staging(Path("<thread>.{N}.review"))

with staged_sidecar(
    final_dir=Path("<thread>.{N}.review"),
    required_files=["verdict.md", "scoring.md", "comments.md",
                    "_summary.md", "_meta.json", "_progress.json"],
) as staging:
    (staging / "verdict.md").write_text(...)
    # ... write all required files into staging, not into final_dir ...
# On clean __exit__: required-files manifest verified, dir renamed.
# On exception or missing required: staging dir left in place for GC.

# Operator-facing portfolio-wide sweep — maintenance use only, NOT
# safe to call from a per-critic entry step in a parallel fan-out
# workflow (see issue #376).
cleanup_stale_staging(portfolio_dir)
```

On entry, every command that operates on a thread SHOULD first call
`cleanup_one_staging(<final_dir>)` — passing the SAME `final_dir` it is
about to hand to `staged_sidecar` — to sweep a `.<final_dir>.tmp/` left
behind by a prior crashed run of THIS SAME critic on THIS SAME version.
The per-critic sweep is **parallel-safe**: when N critics fan out
concurrently under the same portfolio root (the canonical anvil:deck
workflow — 4 critics × N decks — and the increasingly canonical memo
workflow — perspective + hyperlinks + citations + image-accessibility),
each one's entry-step sweep is bounded to its own staging path. The
operator-facing `cleanup_stale_staging(portfolio_dir)` sweeps ALL
`.<slug>.*.tmp/` shapes under `portfolio_dir` — including in-flight
staging dirs from sibling critics — and MUST NOT be called from a
per-critic entry step in any parallel fan-out workflow (issue #376).
Restart-on-detection is the v0 contract — resume-from-staging is
deferred (critics are cheap; a restart preserves more invariants).

Resume-state recovery for a partially-staged sidecar is unnecessary:
the staging dir is silently swept and the command re-enters its phase
as if no prior attempt had run. The `_progress.json` for a sidecar
lives **inside** the sidecar dir, so a sidecar that never renamed has
no `_progress.json` visible to discovery anyway.

The per-file atomic-write recipe (`tmp + os.replace` for `_progress.json`
and other individual JSON files — see "Read-merge-write recipe" above)
remains correct at the **file** boundary and ships alongside the
directory-level shape; the two are complementary, not alternatives.

## Initial-write template (version dir)

A new version directory writes its `_progress.json` for the first time
like this (replace `<phase>` with `draft`, `figures`, etc.):

```json
{
  "version": 1,
  "thread": "<slug>",
  "phases": {
    "<phase>": {
      "state": "in_progress",
      "started": "<ISO-8601 UTC>"
    }
  },
  "metadata": {
    "iteration": <N>,
    "max_iterations": <inherited from <thread>/.anvil.json or 4>
  }
}
```

On successful completion:

```json
{
  "version": 1,
  "thread": "<slug>",
  "phases": {
    "<phase>": {
      "state": "done",
      "started":   "<ISO-8601 UTC>",
      "completed": "<ISO-8601 UTC>"
    }
  },
  "metadata": { ... preserved ... }
}
```

## Initial-write template (critic sibling)

A critic sibling adds the `for_version` field naming the version it
critiques:

```json
{
  "version": 1,
  "thread": "<slug>",
  "for_version": <N>,
  "phases": {
    "<phase>": {
      "state": "done",
      "started":   "<ISO-8601 UTC>",
      "completed": "<ISO-8601 UTC>"
    }
  }
}
```

Note that the phase name in a critic sibling SHOULD match the critic's
own tag (e.g., `review` for `.review/`, `audit` for `.audit/`, `s101` for
`.s101/`). Some early skill implementations used `review` as a generic
phase name across siblings — that is a known inconsistency tracked
separately; new critics should use their own tag.

## See also

- `timestamp.md` — canonical ISO-8601 UTC format.
- `version_layout.md` — directory naming rules.
- `critics.md` — `_meta.json` discovery and aggregation.
- `scorecard_kind.md` — the `human-verdict` vs `machine-summary` discriminator.
