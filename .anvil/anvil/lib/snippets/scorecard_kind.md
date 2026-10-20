# `scorecard_kind` discriminator

The load-bearing primitive that lets `anvil/lib/` describe the critic
landscape without forcing every skill to converge on identical files.

## The problem

Across the six v0 skills (memo, paper, slides, deck, report, ip-uspto),
critic siblings emit different files:

- **memo, paper, slides, report reviewers** emit `verdict.md` +
  `scoring.md` + `comments.md`. These are narrative documents a human
  reads end-to-end to understand the critique.
- **ip-uspto critics + deck specialists** emit `_summary.md` +
  `findings.md` (plus `_meta.json`). These are partial scorecards an
  aggregator merges programmatically; each critic owns only some
  rubric dimensions and leaves the rest `null`.
- **deck-review** emits BOTH layered together — the union of the two
  patterns above.
- **paper-audit, slides-audit, report-audit** add task-specific files
  (citation logs, compile logs, claim tables) alongside one of the
  above scorecard shapes.

The lib does NOT force a single shape. It introduces a discriminator
field in `_meta.json` so consumers can detect what shape to expect
without inspecting filenames.

## The discriminator

Every critic sibling's `_meta.json` MUST include:

```json
{
  "critic": "<tag>",
  "role": "<skill>-<tag>.md",
  "started":  "<ISO-8601 UTC>",
  "finished": "<ISO-8601 UTC>",
  "model": "<model-id>",
  "schema_version": 1,
  "scorecard_kind": "human-verdict" | "machine-summary",
  "rubric_id": "<rubric-identifier>",
  "rubric_total": <int>,
  "advance_threshold": <int>
}
```

### Rubric version stamping fields (`rubric_id`, `rubric_total`, `advance_threshold`)

These three fields are required for new reviews (post-issue #346) and
absent-tolerated for legacy reviews (pre-issue #346). They record the
rubric that the critic scored against, so a downstream consumer can
compare scores apples-to-apples across rubric migrations without
re-reading the skill's current `rubric.md`.

- `rubric_id` (`str`) — stable rubric identifier, e.g.
  `"anvil-memo-v2"`, `"anvil-ip-uspto-v2"`. Naming convention:
  `anvil-<skill>-v<N>`; the version is bumped on breaking shape
  changes (e.g., `/40 → /44` or `/40 → /45`). Pre-existing literals
  for advisory / overlay / vision rubrics: `anvil-pub-neurips-v1`,
  `anvil-figure-content-v1`, `anvil-vision-v1`,
  `anvil-report-vision-v1`, `anvil-ip-uspto-vision-v1`. All eight v0
  artifact-class skills ship `-v2` for their main gate rubric
  post-#357: `anvil-memo-v2`, `anvil-proposal-v2`, `anvil-pub-v2`,
  `anvil-slides-v2`, `anvil-deck-v2`, `anvil-report-v2`,
  `anvil-installation-v2`, `anvil-ip-uspto-v2`. The deck skill bumped
  to `anvil-deck-v3` post-#550 (the /44 → /49 migration adding dim 10
  *Business-model & unit-economics credibility*); the legacy
  `anvil-deck-v2` literal remains a recognized stamp on prior-iteration
  reviews per the per-review version stamping contract.
- `rubric_total` (`int`) — the rubric's declared `total` (the point
  pool the per-dimension weights sum to). The v0 observed values are
  `40` (legacy), `44` (seven post-#357 skills), `45` (ip-uspto
  post-#357, preserving flat-weight design), and `49` (deck post-#550).
- `advance_threshold` (`int`) — the rubric's declared advance
  threshold (the minimum aggregated total that yields `ADVANCE` when
  no critical flag is set). Observed values: `32` and `35` for the
  legacy /40 skills; `35` for the internal-tier /44 skills (memo,
  proposal, paper, slides, installation); `39` for the customer-facing
  /44 skills (report; deck pre-#550); `39` for the /45 ip-uspto skill;
  `43` for the customer-facing /49 deck skill post-#550.

**Backwards compatibility**: a critic sibling produced before these
fields landed MAY omit any or all of them. Readers MUST tolerate the
absence — treat missing `rubric_id` as `"unknown/legacy"` and the
review's reported `total` as advisory only. The verdict aggregator
(`anvil.lib.critics.compute_verdict`) does NOT consume these fields;
they are downstream-consumer audit-trail metadata, not gating inputs.

**Why per-review stamping**: a thread that spans a rubric migration
(e.g., `/40 → /44`) records different `rubric_id` values across its
review siblings; without per-review stamping, an aggregator looking
back at the thread's history cannot tell which iteration was scored
against which rubric and may compare `/40` scores against `/44`
thresholds. See `rubric.md` §"Per-review version stamping" for the
full contract.

**Arithmetic validation consumer (issue #392)**: the `rubric_total` /
`advance_threshold` stamps are consumed by
`anvil/lib/scorecard_check.py`, which validates the *emitted* scorecard
against the *stamped* rubric — per-dimension weights must sum to the
effective pool (`rubric_total` plus any artifact-type overlay
`weight_adjustments`), each score must be a non-negative integer ≤ its
weight, the declared total must equal Σ per-dimension scores, and
`advance: true` requires total ≥ `advance_threshold` with zero critical
flags. A sidecar missing the stamps yields an info-level
`pool_unstamped` finding (the internal checks still run). Write-time
consumers (memo-review step 7b, the pilot) hard-fail on findings; read
time, findings downgrade the sidecar's verdict to advisory — the
sidecar itself is never mutated.

The `scorecard_kind` field takes one of two values:

### `human-verdict`

The critic's output is meant to be read end-to-end by a human (or by
the reviser as a narrative). Files emitted:

```
<thread>.{N}.<tag>/
  verdict.md       Top-level decision + total /N (where N is the rubric's declared `total`) + critical flags
  scoring.md       Per-dimension scorecard with justifications (markdown table)
  comments.md      Line-keyed or location-keyed feedback grouped by severity
  _meta.json       { ..., "scorecard_kind": "human-verdict" }
  _progress.json
```

Used by: memo-review, paper-review, slides-review, report-review,
paper-audit, slides-audit, report-audit.

The reviser consumes these by reading the markdown narratives; no
programmatic aggregation is required because each critic produces a
complete (all-9-dimensions) scorecard.

### `machine-summary`

The critic's output is meant to be aggregated programmatically. Each
critic owns only a subset of rubric dimensions; un-owned dimensions
appear as `null`. Files emitted:

```
<thread>.{N}.<tag>/
  _summary.md      Partial 9-dim scorecard (owned dims scored; others null) + critical-flag bool
  findings.md      Itemized findings (severity, location, rationale, suggested fix)
  _meta.json       { ..., "scorecard_kind": "machine-summary" }
  _progress.json
```

Used by: ip-uspto-review, ip-uspto-101, ip-uspto-112, ip-uspto-claims,
ip-uspto-prior-art, ip-uspto-audit, ip-uspto-pre-flight, deck-narrative,
deck-market, deck-design.

The reviser aggregates these by per-dimension mean of non-null scores,
and ORs all critical-flag booleans.

## Aggregation rules

```
def aggregate_scores(critic_dirs):
    per_dim_scores = {dim: [] for dim in 1..8}
    critical_flag = False

    for critic_dir in critic_dirs:
        meta = load_json(critic_dir/"_meta.json")
        kind = meta.get("scorecard_kind", "human-verdict")  # default backward-compatible

        if kind == "human-verdict":
            # Read scoring.md or verdict.md; extract per-dim scores from markdown table.
            scores = parse_scoring_markdown(critic_dir/"scoring.md")
            flag   = parse_verdict_flag(critic_dir/"verdict.md")
        elif kind == "machine-summary":
            # Read _summary.md; extract per-dim partial scorecard.
            scores = parse_summary_markdown(critic_dir/"_summary.md")  # nulls for unowned dims
            flag   = parse_summary_flag(critic_dir/"_summary.md")
        else:
            raise ValueError(f"unknown scorecard_kind: {kind}")

        for dim, score in scores.items():
            if score is not None:
                per_dim_scores[dim].append(score)
        critical_flag = critical_flag or flag

    # Mean of non-null scores per dimension.
    final = {dim: mean(per_dim_scores[dim]) if per_dim_scores[dim] else None
             for dim in 1..8}
    return final, critical_flag
```

LLM-side: an agent doing aggregation reads each critic sibling's
`_meta.json` to detect the kind, then parses the appropriate file shape.

## Backward compatibility

A critic that does NOT ship `_meta.json` (or ships one without
`scorecard_kind`) is treated as `human-verdict` for backward
compatibility. This keeps memo/paper/slides/report reviewers working
without any required changes — their existing `verdict.md` +
`scoring.md` + `comments.md` is already the `human-verdict` shape.

The minimum change required to formally declare a critic's kind is:
add a `_meta.json` with at least:

```json
{ "critic": "<tag>", "scorecard_kind": "machine-summary" }
```

(The other `_meta.json` fields are recommended but not required for
discrimination.)

## Aggregator critics (both kinds)

Some critics (deck-review, future cross-critic synthesizers) emit BOTH
file shapes — `verdict.md` + `scoring.md` + `comments.md` AND
`_summary.md` + `findings.md`. These are aggregator critics: their job
is to assemble a complete picture from the work of other specialists
while also producing a human-readable narrative.

For an aggregator critic, the `_meta.json` SHOULD record either kind
(typically `human-verdict`, since the aggregated `verdict.md` is the
primary deliverable). The presence of both shapes is the signal to
downstream consumers; the discriminator carries the primary intent.

## Audit / fact-check critics

Audit critics (paper-audit, slides-audit, report-audit, ip-uspto-audit)
may add task-specific files alongside whichever scorecard kind they
ship:

- paper-audit: `citation-audit.md`, `numerical-audit.md`, `compile-log.txt`
- slides-audit: `claims.md`
- report-audit: `findings.md`, `evidence.md`
- ip-uspto-audit: `findings.md` (machine-summary kind)

These additive files do NOT affect the discriminator; they are
documented in the respective audit command file.

## See also

- `critics.md` — discovery glob + aggregation invocation.
- `progress.md` — `_progress.json` schema (sits next to `_meta.json`).
- `rubric.md` — the per-skill weighted-dimension shape that scorecards conform to (/40 and /44 are the v0 observed shapes) + the per-review `rubric_id` version-stamping convention these fields surface.
