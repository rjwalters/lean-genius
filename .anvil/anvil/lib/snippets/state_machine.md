# State machine and extension-point pattern

Every anvil skill walks a state machine from `EMPTY` to a terminal state.
The shape is shared; the specific states differ per skill. This snippet
documents the canonical base machine, the standard extension points, and
how skills hook into them without forking.

## Base state machine

```
EMPTY → DRAFTED → REVIEWED → REVISED → … → READY
                          ↘ NO-GO (terminal — issue #559; operator override required)
                                          ↘ AUDITED (optional, auditor sibling)
```

| State | Evidence (on-disk) |
|---|---|
| `EMPTY` | No `<thread>.{N}/` directories exist. |
| `DRAFTED` | Latest `<thread>.{N}/` has the artifact file + `_progress.json.draft == done`; no sibling review at the same `N`. |
| `REVIEWED` | `<thread>.{N}.review/verdict.md` (or `_summary.md`) exists for the latest `N`. |
| `REVISED` | A `<thread>.{N+1}/` exists after a prior `<thread>.{N}.review/`. |
| `READY` | Latest review records `advance: true` AND no unresolved critical flag. |
| `NO-GO` | Latest `<thread>.{N}.review/verdict.md` records `**Verdict**: NO-GO` AND no `<thread>.{N+1}/` exists. Terminal sink — the evaluator concluded the *thesis itself* fails (issue #559). Operator override required to resurrect: `memo-revise <thread> --override-no-go "<rationale>"` writes `<thread>.{N+1}/` with `metadata.no_go_overridden = true`. |
| `AUDITED` | `<thread>.{N}.audit/` exists alongside a `READY` version (when supported). |

`READY` is terminal for skills that ship without a mandatory audit phase
(memo, deck). `AUDITED` is terminal for skills where audit is mandatory
(paper, slides, report, ip-uspto). Some skills add further terminal states
past `AUDITED` (report → `CUSTOMER-READY`; ip-uspto → `FINALIZED`); see
Extension Points below. `NO-GO` is the thesis-failure terminal sink
shared across skills that opt in (memo is the first canary; other
skills are deferred until a second canary instance). NO-GO is
distinct from `BLOCKED` (iteration-cap exhaustion — recoverable via
per-document cap override) and from `STALLED` (score plateau —
recoverable via operator escalation): it represents an evaluator-
declared structural failure of the thesis that no further revision
against the existing evidence can fix.

### Review vs audit: the principled split

The `REVIEWED → REVISED → ... → READY` portion of the loop operates on
**subjective LLM judgment** — rubric dimensions a strong reader scores
from the text alone (structure, clarity, argument coherence). Review-
sibling `_review.json` payloads carry `kind: judgment`.

The `READY → AUDITED` transition is reserved for **tool-evidence
verification** — citation resolution, numeric consistency, build
cleanliness, prior-art coverage, regulatory checks. Audit-sibling
`_review.json` payloads carry `kind: tool_evidence`, and every finding
records the tool call that produced its evidence. The expensive
tool-call budget is intentionally deferred to the post-`READY` phase so
it only runs against a draft that has already converged on subjective
quality.

Audit critical flags (fabricated citation, build failure, numerical
inconsistency) short-circuit `READY → AUDITED` regardless of the
aggregated score. See `audit.md` for the full distinction, the
load-bearing `tool_calls` contract, and the per-skill audit-vs-review
mapping table.

## Convergence and iteration cap

Each loop iteration is one revise pass. The default iteration cap is
`max_iterations: 4`. The reviser refuses to write `<thread>.{N+1}/` when
`N + 1 > max_iterations`, so `<thread>.{max_iterations}/`
(`<thread>.4/` at the default) is the worst-case terminal version dir —
there is no `<thread>.5/` under a default cap. Exceeding the cap marks
the thread `BLOCKED` and requires human review.

The cap is configurable per-thread by writing
`{ "max_iterations": <N> }` to `<thread>/.anvil.json` in the thread root.

### Highest-priority terminal verdict: `NO-GO` (#559)

In addition to the primary terminators (`THRESHOLD_MET`, `CRITICAL_FLAG`,
`MAX_ITERATIONS`), the convergence loop can halt with `verdict: NO-GO`
when a critical flag of type `"no_go"` is present in the aggregated
review. NO-GO is a **thesis-level** verdict — the evaluator has concluded
that the idea itself fails, not that the prose has a defect. It
short-circuits the revise loop (the loop's job is no longer "raise the
score") and requires an explicit operator override to resurrect.

`NO-GO` is the **highest-priority** terminator — it is resolved BEFORE
`CRITICAL_FLAG`, `THRESHOLD_MET`, `MAX_ITERATIONS`, and `STALLED`. A
`no_go`-typed critical flag is a stronger signal than a generic critical
flag (which forces `advance: false` and routes to revise on the
expectation that a re-revision against the same evidence can fix the
defect); the `no_go` flag declares that no re-revision against the
existing evidence can fix the underlying issue.

The `no_go` flag is emitted by the skill's review command via the
"N parallel critics, one reviser" aggregation pathway. Typical trigger
conditions (memo-skill v0 — other skills opt in per their own canary
signals):

- A red-team critic's `redteam_survives` finding on a **load-bearing**
  objection at iteration `max_iterations - 1` or later (i.e., the
  iteration budget is about to be exhausted against an unrebutted
  structural objection — issue #573 composition).
- A `Strongman: NOT_ADDRESSED (load-bearing)` finding at iteration
  `max_iterations - 1` or later.
- A `Summary-detail consistency: CONTRADICTED` finding on the memo's
  thesis claim at iteration `max_iterations - 1` or later.

Lower-tier flags (typos, dim 9 bloat, unverified cites) NEVER promote
to `no_go`. The bar is "an evaluator has identified a defect that
re-revision against the existing evidence cannot fix."

The terminal verdict (when one fires) is recorded in the top-level
`termination_reason` field as `"NO_GO"`; the verbatim flag
`justification` is preserved in `metadata.kill_rationale` per
`progress.md` §"`metadata.kill_rationale`". A first-class `verdict.md`
artifact carries the same kill rationale in operator-facing markdown
shape — see the skill's own command spec (e.g., `memo-review.md` step 10)
for the canonical NO-GO `verdict.md` format.

**Operator override semantics.** NO-GO is a **recommendation, not a
hard lock**. The override path (e.g., `memo-revise <thread>
--override-no-go "<reason>"`) is intentionally friction-ful: it
requires a verbatim non-empty rationale. The override is **per-version**:
a thread that resurrects from NO-GO and then re-earns a `no_go` flag on
the resurrected version is in NO-GO again.

### Secondary terminal verdict: `STALLED` (#27)

In addition to the primary terminators (`THRESHOLD_MET`, `CRITICAL_FLAG`,
`MAX_ITERATIONS`), the convergence loop can halt with `verdict: STALLED`
when the last `lookback` aggregated totals are all within `± window` of
each other AND the latest total is below the threshold AND no critical
flag is set. Defaults: `window=1`, `lookback=2` (two consecutive rounds
within ±1).

`STALLED` does NOT produce a `READY` transition. The thread is still
below threshold; the verdict says "the score has stopped moving" rather
than "the work has converged". The orchestrator (or human) reads
`termination_reason: "STALLED"` and decides whether to escalate, swap
critics, or accept the below-threshold result.

`STALLED` is the **lowest-priority** terminator — `CRITICAL_FLAG`,
`THRESHOLD_MET`, and `MAX_ITERATIONS` all resolve first. The full
resolution order is in `rubric.md`'s "Convergence logic" section and
implemented in `anvil.lib.convergence.decide_termination`.

The score history that drives the stable check is recorded in
`metadata.score_history` in `_progress.json` (see `progress.md`). The
terminal verdict (when one fires) is recorded in the top-level
`termination_reason` field.

## Critical-flag short-circuit

Any critical flag set by any sibling critic short-circuits regardless of
score. A `READY` transition requires:

1. `total_score >= threshold` (32 for memo/paper/slides, 35 for deck/report/ip-uspto).
2. `no unresolved critical flag` from any sibling critic.

Both conditions must hold. Either falsy condition keeps the thread in
the convergence loop (or `BLOCKED` if the cap is exceeded).

## Extension points

Skills extend the base machine in three well-defined ways. Use these
patterns rather than inventing parallel structures.

### 1. Pre-draft phases

Add a state before `DRAFTED` for setup work the drafter consumes. The
sibling lives at `<thread>.0.<tag>/`. Examples:

| Skill | Pre-draft state | Sibling |
|---|---|---|
| slides | `OUTLINED` | `<thread>.0.outline/` |
| paper | (no named state — litsearch is informational) | `<thread>.0.litsearch/` |
| deck | `BRIEF_DONE` | `<thread>/BRIEF.md` (not a sibling — lives in thread root) |
| ip-uspto | `INTAKE_DONE` → `INVENTORSHIP_DONE` | `<thread>/BRIEF.md` + `<thread>/inventorship.md` |

The state-derivation predicate (see `thread_state.md`) checks for the
expected pre-draft evidence; if present and no `<thread>.1/` exists yet,
report the pre-draft state.

### 2. Mid-loop phases

Add a state inside the convergence loop. Used when a check must run
before each review iteration. Example:

| Skill | Mid-loop state | When |
|---|---|---|
| ip-uspto | `PRE_FLIGHT_PASSED` | After revise, before next review |

The orchestrator's "next command" recommendation includes the mid-loop
phase as a prerequisite for the next iteration.

### 3. Post-AUDITED terminal phases

Add a state after `AUDITED` for human-acknowledgment gates or assembly
of submission packages. Example:

| Skill | Terminal state | Trigger |
|---|---|---|
| report | `CUSTOMER-READY` | `report-promote` writes `<thread>.{N}.promote/receipt.md` |
| ip-uspto | `FINALIZED` | `ip-uspto-finalize` writes `<thread>.final/_manifest.json` |
| slides | `REHEARSED → HANDOUT_GENERATED` | rehearse sibling, then handout export |

The post-AUDITED transition typically requires explicit human
acknowledgment (a "kill-switch" gate before delivering customer-facing
material). The state-derivation predicate checks for the relevant
sibling's existence.

## Runtime hook (deferred)

The two-stage `AUDITED → CUSTOMER-READY` pattern (and ip-uspto's
`AUDITED → FINALIZED`) is currently implemented inline in each skill.
A first-class "post-audit human-ack gate" runtime hook is deferred until
a third skill needs the pattern — at that point the canonical hook
shape will be added here and the existing skills migrated. Until then,
new skills wanting a post-AUDITED terminal MUST follow the inline
pattern documented in the existing skills (write a critic-shaped
sibling at `<thread>.{N}.<tag>/` containing a `receipt.md` or
`_manifest.json` keyed to the version's content hash).

## State-transition table (composite, across skills)

```
EMPTY
  └→ (skill-specific pre-draft phases, optional)
       └→ DRAFTED
            └→ REVIEWED  ⇄  REVISED (loop until convergence)
                 ↘
                  └→ READY
                  │    └→ AUDITED (optional or mandatory per skill)
                  │         └→ (skill-specific terminal, optional: CUSTOMER-READY, FINALIZED, HANDOUT_GENERATED, ...)
                  └→ NO-GO (issue #559 — thesis-failure terminal; opt-in per skill; operator override required)
       └→ BLOCKED (if iteration cap exceeded)
```

## See also

- `thread_state.md` — derive state from on-disk evidence (the runtime
  side of this table).
- `version_layout.md` — directory naming for sibling phases.
- `progress.md` — `_progress.json` records phase state for each step.
- `critics.md` — how the review/revise loop discovers and aggregates
  critic outputs.
- `audit.md` — the principled `.review/` (judgment) vs `.audit/`
  (tool-evidence) distinction; load-bearing fields and per-skill mapping.
