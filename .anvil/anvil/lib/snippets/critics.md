# Critic discovery and aggregation

Anvil's "N parallel critics, one reviser" pattern is implemented entirely
through filesystem conventions plus the `scorecard_kind` discriminator.
There is no shared runtime; each skill's reviser performs discovery and
aggregation using the rules here.

## Discovery

Given a thread and a version `N`, critic siblings are the directories
matching the glob:

```
<thread>.{N}.*/
```

minus the bare versioned directory `<thread>.{N}/`. The glob captures
every sibling of every kind (review, audit, narrative, market, design,
s101, s112, preflight, ...) regardless of which skill defined the tag.

### Skill-side default critic set

Each skill defines a default set of critics that MUST run before a
version can leave `REVIEWED`. The reviser refuses to advance if any
configured critic is missing or unfinished.

| Skill | Default critic set | Optional siblings |
|---|---|---|
| memo | `review` | `audit`, `critic` (consumer-added) |
| paper | `review`, `audit` | `litsearch` (pre-draft or re-run) |
| slides | `review`, `audit` (mandatory) | `outline` (pre-draft), `rehearse`, `handout` (terminal) |
| deck | `review`, `narrative`, `market`, `design` | `audit` |
| report | `review`, `audit` (both mandatory) | `promote` (terminal) |
| ip-uspto | `review`, `s101`, `s112`, `claims`, `priorart` | `preflight` (mid-loop), `audit` (post-READY) |

Operators can subset the default set per-thread by writing
`{ "critics": ["..."] }` to `<thread>/.anvil.json`.

## Per-critic discovery

For each discovered sibling at `<thread>.{N}.<tag>/`, the reviser:

1. Loads `_meta.json` if present — extract `scorecard_kind` (default
   `human-verdict` if missing).
2. Verifies `_progress.json` records the relevant phase as `done`.
   If `in_progress` or `failed`, treat as missing for aggregation
   purposes (and warn the operator that a critic crashed).
3. Loads the appropriate scorecard files per the discriminator (see
   `scorecard_kind.md` for the file map).
4. If the sibling ships a canonical `_review.json`, the loader checks
   the payload's `kind` field. When `kind == "tool_evidence"` (audit-
   class critics; see `audit.md`), every entry in `findings[]` MUST
   include a non-empty `tool_calls` array. The schema validator at
   `anvil/lib/review_schema.py::Review._validate_kind_required_fields`
   enforces this contract — a `tool_evidence` review with a
   `tool_calls`-less finding is rejected at parse time. When
   `kind == "judgment"` (review-class critics), no `tool_calls` are
   required.

## Aggregation

The reviser produces a single composite scorecard from all critic
outputs:

```
def aggregate(thread, N, skill_config):
    siblings = glob(f"{thread}.{N}.*/") - {f"{thread}.{N}"}
    required = set(skill_config["critics"])
    found    = {parse_tag(s) for s in siblings}

    missing = required - found
    if missing:
        return ERROR(f"missing required critics: {missing}")

    per_dim = {dim: [] for dim in 1..8}
    critical_flag = False

    for sibling in siblings:
        meta = load_json(sibling/"_meta.json")  # or {} if not present
        kind = meta.get("scorecard_kind", "human-verdict")

        scores, flag = read_scorecard(sibling, kind)
        for dim, score in scores.items():
            if score is not None:
                per_dim[dim].append(score)
        critical_flag = critical_flag or flag

    composite = {dim: round(mean(per_dim[dim])) if per_dim[dim] else None
                 for dim in 1..8}
    total = sum(v for v in composite.values() if v is not None)
    return composite, total, critical_flag
```

### Aggregation rule details

1. **Per-dimension mean of non-null scores.** A dimension is null if NO
   critic owned it (rare; usually the general reviewer covers all
   dimensions). Otherwise the mean of non-null contributions.
2. **Integer rounding.** Final composite per-dimension scores round to
   the nearest integer (the rubric is integer-valued).
3. **Critical-flag OR.** Any critic with `critical_flag: true` (in its
   verdict.md or _summary.md frontmatter) sets the composite flag.
4. **Threshold comparison happens after aggregation.** The reviser
   checks `total >= skill_threshold AND NOT critical_flag` to decide
   if the thread advances.

## Parallelism

Critics are independent. Two parallel critics on the same `<thread>.{N}/`
read the same input and write to disjoint output paths
(`<thread>.{N}.review/` vs `<thread>.{N}.audit/`). There is no shared
mutable state.

**v0 implementations should default to serial execution** (for
debuggability). The sibling-directory convention permits parallel
spawn, and the orchestrator MAY parallelize when an operator opts in;
nothing in the file layout breaks.

## Adding a new critic

To add a new critic to an existing skill:

1. Create a new command file: `commands/<skill>-<tag>.md`.
2. Have it write to `<thread>.{N}.<tag>/` with the appropriate
   `scorecard_kind` per the discriminator.
3. Append the new tag to the skill's default critic set (in the
   skill's SKILL.md, the `Default critic set` row of the table above).
4. **Pick the `kind` of the critic.** This sets the value of `kind`
   on the sibling's `_review.json` payload:
   - **`kind: judgment`** (default) — the critic scores from the text
     alone. No external tool calls are required to back its findings.
     Review-class critics (`<skill>-review` and most specialists like
     `deck-narrative`, `deck-market`, `ip-uspto-s101`) are
     `judgment`-kind.
   - **`kind: tool_evidence`** — the critic backs its findings with
     external tool calls (citation resolution, build verification,
     numeric consistency). Every `Finding` MUST set a non-empty
     `tool_calls` array recording each tool invocation as a
     `ToolCall`. The schema validator at
     `anvil/lib/review_schema.py::Review._validate_kind_required_fields`
     enforces this. Audit-class critics (`<skill>-audit`,
     `ip-uspto-priorart` once it's tool-augmented) are
     `tool_evidence`-kind. See `audit.md` for the full contract.
5. No reviser changes required — the glob discovery picks it up.

## Examples by skill

### memo (human-verdict only)

```
acme-seed.1/                  # the artifact
acme-seed.1.review/           # human-verdict
  verdict.md
  scoring.md
  comments.md
  _meta.json   { "scorecard_kind": "human-verdict" }
  _progress.json
```

The reviser reads `scoring.md`'s markdown table to extract all 8
dimension scores; no aggregation across critics (single critic).

### ip-uspto (machine-summary, multiple specialists)

```
acme-widget.2/
acme-widget.2.review/         # machine-summary (owns dims 6, 7, 8)
acme-widget.2.s101/           # machine-summary (owns dim 4)
acme-widget.2.s112/           # machine-summary (owns dims 2, 3)
acme-widget.2.claims/         # machine-summary (owns dim 1)
acme-widget.2.priorart/       # machine-summary (owns dim 5)
```

The reviser aggregates per-dimension means across the 5 specialists,
each contributing scores only for their owned dimensions. Critical
flags from any specialist (especially s101, s112) short-circuit the
advance.

### deck (mixed: aggregator + specialists)

```
acme-seed.1/
acme-seed.1.review/           # AGGREGATOR — emits both kinds; primary kind: human-verdict
  verdict.md                  # synthesized narrative
  scoring.md                  # complete 9-dim table (mean of specialists + own observations)
  comments.md
  _summary.md                 # machine-summary shape (for machine consumers)
  findings.md
  _meta.json   { "scorecard_kind": "human-verdict" }   # primary intent
acme-seed.1.narrative/        # SPECIALIST — machine-summary (owns dims 1, 7, 9)
acme-seed.1.market/           # SPECIALIST — machine-summary (owns dims 3, 4)
acme-seed.1.design/           # SPECIALIST — machine-summary (owns dim 8)
```

Deck's aggregator critic (`deck-review`) emits both shapes layered:
the human-verdict narrative is the primary deliverable; the
machine-summary layer lets future cross-skill machinery aggregate it
alongside other machine-summary critics if needed.

### paper (human-verdict reviewer + human-verdict auditor with task-specific files)

```
q3-method.2/
q3-method.2.review/           # human-verdict
q3-method.2.audit/            # human-verdict + task-specific files
  verdict.md                  (synthesized: aggregates the per-claim audits)
  scoring.md                  (audit-specific scoring; treated as a critic vote in aggregation)
  citation-audit.md           # additive task-specific
  numerical-audit.md          # additive task-specific
  compile-log.txt             # additive task-specific
  flags.md                    # additive task-specific
  _meta.json   { "scorecard_kind": "human-verdict" }
```

Note: paper-audit currently emits `flags.md` rather than `verdict.md` +
`scoring.md`. This is an audit-critic convention; the aggregator
treats `flags.md` as critical-flag input and consults `_meta.json` to
determine the scorecard kind. The migration in the PR introducing
this lib adds the `_meta.json` annotation without changing the
existing files.

## Citation auditor — partial scorecard, no special aggregation

Skills that opt in to the citation-quality dimensions
(`citation_recall`, `citation_precision`; see `rubric.md`) typically
assign ownership of those two dimensions to a single critic — the
citation auditor (commonly `paper-audit`, `report-audit`, or
`ip-uspto-priorart`). The auditor populates `citation_recall` and
`citation_precision` in its own `Score` entries and leaves them
`None` on the general reviewer's scorecard.

This requires **no new aggregation behavior**. The existing partial-
scorecard rule (per-dimension mean of non-null contributions across
critics, see "Aggregation" above) handles it: the auditor's
non-null values flow through, the reviewer's `None` values are
ignored, and the aggregated composite reflects the auditor's verdict
on citation quality alone.

The lib's `cite.py` produces `refs.bib`; the auditor reads
`refs.bib` plus the artifact body to compute recall and precision.
Neither the resolver nor the aggregator needs to know about the
citation dimensions specifically — they are ordinary opt-in
dimension names per the existing convention.

## Deterministic-checks family — consistency sweep alongside render-gate / marp-lint

Some critics are cheap mechanical greps rather than full LLM
judgments. They run *before* the expensive content review, surface as
typed `Review(kind=tool_evidence)` payloads so the existing aggregator
consumes them without any schema change, and (by convention) emit
findings at `severity="minor"` so a false positive can be declined
without forcing a `Verdict.BLOCK`.

The family currently has three members:

- **`anvil/lib/render_gate.py`** — page-fit, overfull-box, compile-
  success, and placeholder-scan gates over a compiled PDF + log
  (`Kind.TOOL_EVIDENCE`; `CriticalFlag` on fail because a missing PDF
  IS a blocker).
- **`anvil/lib/marp_lint.py`** — slide-source overflow /
  layout linter over the markdown before Marp render.
- **`anvil/lib/revise_consistency.py`** — stale-token sweep for the
  `*-revise` lifecycle. Compares old- and new-source priced-number
  tokens (money, percent, ranges), then flags companions (figure
  scripts, speaker-notes, CSVs) that still reference a token the new
  source has fully dropped. Wired into `deck-revise` step 9.5;
  available to every other `*-revise` command on adoption.

All three share: deterministic regex/tool greps (no LLM), `to_review`
that emits `Kind.TOOL_EVIDENCE` with a single null-scored dim so the
aggregator stays untouched, and a `passed()` predicate the skill
wiring uses to decide whether to write the sidecar file (no noise on
clean runs).

## Orchestrator output-file guard collisions

Some anvil skills emit a critic sibling file named `findings.md`, and every
skill's `human-verdict` reviewer emits `verdict.md` + `scoring.md` +
`comments.md`. These are **required manifest outputs** — they are named in
each skill's `## Output layout` section and passed to
`anvil/lib/sidecar.py::staged_sidecar(final_dir=..., required_files=[...])`,
so the atomic rename fails (and the review never lands) if any of them is not
written. `findings.md` in particular is the hard-required review-manifest file
for `paper`, `deck`, `slides`, `ip-uspto`, and `ip-uspto-provisional` (see
`scorecard_kind.md`; note these skills split across both
`scorecard_kind` values — see the paragraph below for which kind each emits
`findings.md` under).

**The collision.** Some agent-orchestrator harnesses pattern-match subagent
output *by filename* — a "return findings as text, do not write a report file"
policy intercepts writes to files named `findings.md` / `report.md` / (by the
same reasoning) `verdict.md` / `scoring.md` / `comments.md`. Under such a
harness, the required critic write is silently blocked, `staged_sidecar` never
sees a complete manifest, and the atomic rename never fires — the review dir
never appears even though the reviewer "ran." This is an **external harness
misclassifying anvil's contractually-required output**, not an anvil defect:
these are structured sidecar-manifest files, not incidental "report files."

**These files are NOT renameable to dodge the guard.** Three concrete
arguments make renaming the wrong fix:

1. **A rename breaks a literal filename read in the parsing code.**
   `anvil/lib/critics.py`'s ip-uspto legacy adapter reads `findings.md` by
   its exact name — `(critic_dir / "findings.md").read_text()` (line 487),
   gated by the `LEGACY_IP_USPTO_FILES = ("_summary.md", "findings.md",
   "_meta.json")` existence check (line 77). Renaming the file silently
   drops those critics out of aggregation.

2. **The cross-skill blast radius is large.** `findings.md` is referenced by
   name in ~46 command manifests and ~30 tests across the tree (grep
   `findings.md` under `anvil/skills/*/commands/` and `tests/`). A rename is
   not a one-file edit; it is a coordinated migration touching every skill
   that emits or asserts on the file.

3. **A rename does not even solve the problem.** Renaming *only*
   `findings.md` to `_findings.md` would still leave `verdict.md` /
   `scoring.md` / `comments.md` exposed to the identical class of guard under
   a differently worded pattern (a "verdict"-shaped filename is just as
   plausible a match for a "no report/verdict files" heuristic). The same
   guard would catch those files anyway, so the only durable fix is on the
   orchestrator side, not the filename.

(For completeness on the naming convention: `findings.md` carries no
leading underscore because, by the anvil-wide filename convention, the
underscore prefix marks "operator/agent-managed metadata, not artifact
content" — see `anvil/skills/memo/SKILL.md:106`. Note this is a filename
convention, *not* the `scorecard_kind` discriminator: `scorecard_kind.md`
discriminates on the `_meta.json` `scorecard_kind` field
(`human-verdict` vs `machine-summary`), and `findings.md` is actually
emitted under **both** kinds depending on skill — `human-verdict` for
`paper-review` (see `anvil/skills/paper/commands/paper-review.md` lines 45, 232),
`machine-summary` for the ip-uspto and deck specialists per
`scorecard_kind.md` §`machine-summary`. That skill-dependent duality is
exactly why a blanket rename would be wrong, and it is independent of the
three arguments above.)

**Recommended operator action.** A consumer running an anvil skill's
`*-review` / `*-audit` / specialist critic commands under an
agent-orchestrator harness with output-file interception should **whitelist
writes into the critic sibling directories**:

- Broadest: allow all writes under `<thread>.{N}.review/`,
  `<thread>.{N}.audit/`, and `<thread>.{N}.<critic>/` (and their leading-dot
  `.<...>.tmp/` staging siblings — the atomic-rename staging shape).
- Narrowest: allow the specific filenames named in each skill's
  `## Output layout` / `required_files=[...]` manifest (e.g. `verdict.md`,
  `scoring.md`, `comments.md`, `findings.md`, `_review.json`, `_summary.md`,
  `_meta.json`, `_progress.json` for `paper-review`).

If the guard cannot be relaxed, a Bash-heredoc write (or any non-intercepted
file-write path) into the staging directory is a valid manual fallback — the
requirement is only that the bytes land at the manifest path before
`staged_sidecar` verifies and renames.

Whitelisting (not renaming) is the framework's position because it fixes the
actual failure mode — an external harness blocking anvil's documented,
required output — without touching the atomicity primitive, the parsing code,
or the identical `findings.md` / `verdict.md` convention the other skills
share.

## See also

- `scorecard_kind.md` — the discriminator and per-kind file maps.
- `version_layout.md` — sibling directory naming rules.
- `state_machine.md` — when critics run in the lifecycle.
- `progress.md` — `_progress.json` schema for the sibling directory.
- `cite.md` — citation primitive on-disk convention.
- `audit.md` — the `.review/` (judgment) vs `.audit/` (tool-evidence)
  distinction and the per-finding `tool_calls` contract.
