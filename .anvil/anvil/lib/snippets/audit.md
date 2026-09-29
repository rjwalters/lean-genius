# Audit phase: tool-evidence verification

This snippet codifies the principled distinction between the `.review/`
and `.audit/` sibling critic directories. Both produce per-critic
`_review.json` payloads that the aggregator merges into a single
composite scorecard. They differ in **how findings are produced**:

- **`.review/` siblings carry `kind: judgment`.** Rubric dimensions a
  strong reader can score from the text alone — structure, clarity,
  prose quality, argument coherence, strategic framing. No external
  tool calls; no out-of-band verification.
- **`.audit/` siblings carry `kind: tool_evidence`.** Dimensions that
  require *external* verification — citation resolution (does the
  cited source actually say this?), numeric consistency (does the math
  check?), prior-art coverage (was this patent or paper missed?),
  compile/build cleanliness, regulatory/compliance assertions. Each
  audit finding cites the tool call that produced the evidence via
  the `tool_calls` array on the finding.

This is the CRITIC (Gou et al., arXiv 2305.11738) tool-augmented
self-correction line, applied to Anvil's review/revise loop: subjective
quality and verifiable correctness are kept on separate critics so the
expensive tool-call budget runs only after the artifact has converged
on subjective quality.

## When audit runs

Audit is post-`READY` for most skills (the artifact has already met the
subjective rubric threshold; we only burn tool calls on a near-final
draft). For some skills audit is **mandatory** — `AUDITED`, not
`READY`, is the terminal state. Where audit is optional, the orchestrator
may skip it for rough-internal artifacts.

See `state_machine.md` for the canonical sequence
`REVIEWED → REVISED → ... → READY → AUDITED`.

## Load-bearing fields

The schema validator at `anvil/lib/review_schema.py::Review.
_validate_kind_required_fields` (lines 369–382) enforces the contract:

- When a critic's `_review.json` has `kind == "tool_evidence"`, every
  entry in `findings[]` MUST include a non-empty `tool_calls` array.
- The validator rejects (`ValidationError`) any `tool_evidence` review
  whose findings omit `tool_calls`.
- `kind == "tool_evidence"` with `findings == []` is valid (a clean
  audit pass with no findings to report).

Each `ToolCall` records the tool invocation (tool name, args, optional
result summary) so a downstream consumer can audit the auditor: every
factual claim in an audit finding traces back to a specific tool call.

## Perishable vs durable verifications

`kind: tool_evidence` conflates two materially different things:

- **Durable** — BOM arithmetic, link budgets, internal consistency, a
  subtotal that sums, a reference numeral that matches. Verified once,
  true forever unless the *document* changes.
- **Perishable** — a live URL, an HTTP status, a version pin, the SHA
  of a served artifact, a "verified live on `<date>`" claim, a price
  quote with an expiry. Verified once, true until the *world* moves.

A perishable claim's `VERIFIED` verdict has an implicit expiry. Before
issue #863 the framework did not record it, so the two read identically
on disk and every downstream consumer — the next auditor, the reviser,
the operator deciding to send — inherited a verification whose freshness
was unknowable without redoing the probe.

This bites hardest exactly where the framework is strongest:
audit-mandatory, customer-facing skills (`proposal`, `report`, the `ip-*`
family) whose artifacts are *held* between the audit and the moment
someone external reads them. The longer an artifact sits `READY` /
`AUDITED` waiting on a human decision, the more its perishable claims
decay.

### The probe record

An auditor records each perishable verification as a `Probe`
(`anvil/lib/review_schema.py`). Four required fields — the minimum a
later pass needs to re-run the check without re-deriving *what* to
check:

| Field | Meaning |
|---|---|
| `target` | What was probed, as a stable re-addressable identifier (URL, DOI, SKU, host:port). This is the identity key across passes — keep it byte-stable. |
| `method` | How. Free-form tag; no enforced vocabulary. Observed values: `http_status`, `sha256`, `version_string`, `content_match`, `quote_validity`. |
| `observed` | What it returned then, verbatim enough to diff against a re-probe (`200`, `sha256:ab12…`, `working draft v8`). |
| `checked_at` | ISO-8601 UTC timestamp (see `timestamp.md`). Validated as parseable. |

Optional: `claim` (the artifact claim that depends on it — so a staleness
report can name what would become *false*, not just which URL went cold),
`evidence_span`, `recheck_command` (the literal one-liner, when the probe
is shell-reproducible), `max_age_days` (per-probe freshness budget, for a
claim with a known expiry such as a 30-day vendor quote).

**The existence of a `Probe` row IS the perishability marker.** There is
no `durable: true` counterpart — durable verifications are simply the
ones with no probe. This keeps the marker additive: a critic that records
nothing is byte-identical to a pre-#863 critic.

### Where probes live

Two carriers, because the shipped audit commands have not all migrated to
`_review.json` (see "Migration status" below):

- **Schema-era critic** — populate `Review.probes[]` in `_review.json`.
- **Prose-era critic** (every shipped auditor today) — write a standalone
  `probes.json` next to `findings.md`:

```json
{
  "schema_version": "1",
  "version_dir": "gossamer-lan.2",
  "critic_id": "proposal-audit",
  "probes": [
    {
      "target": "https://example.org/papers/widget-draft.pdf",
      "method": "sha256",
      "observed": "sha256:9f2c…",
      "checked_at": "2026-08-01T14:03:00Z",
      "claim": "§3 cites this paper as 'working draft v8'",
      "recheck_command": "curl -sL <url> | shasum -a 256"
    }
  ]
}
```

Both are validated by the same `Probe` model and unioned by the reader,
so the perishability contract does not wait on the per-skill
`_review.json` migration.

An **empty** `probes` list is meaningful and is NOT the same as an absent
record: it is the auditor stating "I looked; nothing in this artifact is
perishable." An absent record is unknown freshness.

### Surfacing staleness

`anvil/lib/probe_freshness.py` turns the recorded probes into a bounded
re-probe checklist. A revise or audit pass over a version runs:

```
python -m anvil.lib.probe_freshness <thread>/<thread>.{N}
```

(prefix `uv run --project .anvil` in an installed consumer repo). It
walks every critic sibling across **every** version under the thread
root, keeps the newest probe per `target`, and classifies:

- **`FRESH`** — probed within its freshness budget, against the version
  under review.
- **`STALE`** — the newest probe of this target is older than its budget
  (`Probe.max_age_days`, else the caller's default of 14 days).
- **`NOT-REPROBED`** — the target was verified against an *earlier*
  version and no pass since has re-probed it. The claim was carried
  forward on the strength of an older pass.

`STALE` + `NOT-REPROBED` is the checklist: it turns "re-verify everything
or trust it" into a bounded set. Resolving one of these is the same
discipline as issue #749's "findings are leads, not evidence", extended
across *time* rather than across siblings — re-run the probe, do not
carry the earlier verdict forward on faith.

**Backward compatibility.** An audit sibling with no probe record at all
is reported under `unknown_freshness` — tolerated by design, never a
defect, never an error, and never conflated with "nothing perishable".
Every pre-#863 sibling lands there. Unknown is honest; silence dressed as
`VERIFIED` was the bug.

**Advisory only.** Like the `evidence_drift` check (issue #857), probe
freshness never mutates on-disk state, never affects scoring, `advance`,
or critical flags, and its CLI always exits `0`. A stale probe is not a
scored defect — it is a verification that has expired and that the next
pass must re-run before the artifact ships. Unlike the `pending_marker`
gate (#841/#842), it is never wired through `convergence.py`'s
`CriticalFlag` machinery.

## Aggregation

The aggregator (see `critics.md` and `anvil/lib/critics.py::aggregate`)
merges judgment-kind and tool-evidence-kind reviews into one composite
scorecard using the standard per-dimension mean-of-non-null rule. `kind`
is a per-review attribute; the aggregate scorecard does not carry a
single `kind` — its `critic_ids` list records which reviews
contributed, and a consumer interested in provenance can re-load
individual reviews to inspect their `kind`.

The threshold comparison happens once, against the aggregated total.
The audit's contribution to the total flows through the standard
mean-of-non-null rule.

## Critical-flag semantics

Audit-phase critical flags are the most consequential the framework
emits. Typical examples:

- **Fabricated citation** — `\cite{key}` resolves to a paper that does
  not say what the surrounding sentence claims it says.
- **Build failure** — `pdflatex` / `marp` / equivalent fails to produce
  a clean rendered artifact.
- **Numerical inconsistency** — text says 87.3%, table says 87.1%.
- **Compliance / regulatory failure** — required disclaimer missing,
  inventor list mismatched against `inventorship.md`, prior art omitted.

Audit critical flags short-circuit `READY → AUDITED` regardless of the
aggregated score. A 38/40 with one audit critical flag does NOT
advance. This is identical to the review-phase short-circuit rule;
audit just owns a different class of defects.

The composite scorecard surfaces critical flags via the standard
logical-OR rule (any critic, any kind, with `critical_flags` non-empty
forces `Verdict.BLOCK`).

## Skill-by-skill audit-vs-review mapping

The v0 skills split as follows:

| Skill | Has audit command? | Audit mandatory? | Notes |
|---|---|---|---|
| memo | no | n/a | Audit is documented in `critics.md` as an optional consumer-added sibling; the framework ships no `memo-audit` command. |
| paper | yes (`paper-audit`) | mandatory | Citation resolution, claim-support spot-check, numerical audit, LaTeX compile verification. `READY` is not terminal — `AUDITED` is. |
| report | yes (`report-audit`) | mandatory | Customer-facing; ≥39/44 threshold + audit. Subsequently promoted to `CUSTOMER-READY` via `report-promote`. |
| deck | yes (`deck-audit`) | optional | Audit is recommended for fundraising decks (fabricated traction / market-math claims) but not required to reach `READY`. |
| slides | yes (`slides-audit`) | mandatory | Density / timing / asset checks; combined with the rehearse + handout terminal phases. |
| ip-uspto | yes (`ip-uspto-audit`) | mandatory (post-convergence) | Inventor name consistency, reference-numeral coherence, prior-art-admission checks. Runs only when a version is `READY_FOR_AUDIT`. |

Five audit commands ship in v0 (paper, report, deck, slides, ip-uspto);
memo's audit slot is reserved for consumer extension.

## Migration status (v0)

The five shipped audit commands currently emit their existing prose
artifacts (`flags.md`, `citation-audit.md`, `_summary.md`, etc.) plus a
`_meta.json` with `scorecard_kind`. They do **not** yet write
`_review.json` with `kind: tool_evidence`. The legacy adapter in
`anvil/lib/critics.py` bridges the gap so this snippet's contract
applies to new audit critics today; per-skill migration of the five
shipped commands lands as five separate follow-up issues (one per
skill).

When a shipped skill migrates, the change is mechanical:

1. In the skill's `<skill>-audit.md`, replace the prose-only output spec
   with a `_review.json` write spec using `kind: tool_evidence`.
2. Populate each finding's `tool_calls` array with the tool invocations
   that produced its evidence (`grep`, `pdflatex`, `WebFetch`, etc.).
3. Keep the legacy prose siblings as optional human-readable artifacts
   if useful; the reviser ignores them once `_review.json` is present.

## Filename tolerance

The five shipped audit commands (`paper`, `report`, `deck`, `slides`, `ip-uspto`)
and the proposal auditor all write their per-claim findings file as
`findings.md` by default. Some execution contexts — notably subagent
harnesses that block specific filenames (see issue #135 for anvil's
documented subagent-delegation workaround) — can prevent a writer from
producing `findings.md` literally.

For the **proposal skill only** (per issue #240, canary-surfaced
2026-06-02), the consumer reviser (`proposal-revise.md` step 6) accepts
a small whitelist of documented aliases in priority order:

1. `findings.md` (canonical — always wins when present)
2. `claim-log.md` (documented alias)
3. `audit-findings.md` (documented alias)

The writer-side convention is documented in
`anvil/skills/proposal/commands/proposal-audit.md` §"Alias contract":
writers SHOULD use `findings.md`; if blocked, MAY use one of the two
aliases and prepend a one-line header note in the file body explaining
the rename. The reviser does not parse the header note — it is
human-readable bookkeeping for the next agent.

**Scope is intentionally local to the proposal skill.** The other four
shipped audit-bearing skills (`paper`, `report`, `deck`, `slides`,
`ip-uspto`) keep strict `findings.md` behavior. Per the "wait for the
second consumer before generalizing" rule (CLAUDE.md §"Skill-local
first, lib promotion later"), the alias-tolerance pattern is **not**
yet promoted to a framework-wide helper. If a second skill's canary
reports the same subagent-harness block, the pattern can be lifted to
`anvil/lib/` as a helper like `find_findings_file(critic_dir: Path) ->
Path | None` and consumed by all revisers. Until then, the per-skill
duplication is acceptable.

## Adding a new audit critic

To add a tool-augmented critic to a skill:

1. Create `commands/<skill>-<tag>.md` (typically `<skill>-audit.md`).
2. Have it write `<thread>.{N}.<tag>/_review.json` with:
   - `kind: "tool_evidence"`.
   - One `Finding` per defect, each carrying a `tool_calls: [...]`
     array recording the tool invocations that produced the evidence.
   - Critical-flag-worthy defects surfaced via `critical_flags[]` at
     the top level (or `Score.critical = true` for dim-scoped flags).
3. Append the tag to the skill's default critic set in `critics.md` if
   the audit is mandatory.
4. Record every **perishable** verification as a `Probe` — in
   `Review.probes[]`, or in a sibling `probes.json` if the critic still
   emits the prose shape. See "Perishable vs durable verifications".

No reviser changes are required. The glob discovery picks up the
sibling; the schema validator enforces `tool_calls` on every finding;
the aggregator merges via the standard rule.

## See also

- `state_machine.md` — `REVIEWED → REVISED → ... → READY → AUDITED`
  in context; this snippet supplies the principled rule for what runs
  in each phase.
- `critics.md` — sibling discovery, aggregation, "Adding a new critic".
- `rubric.md` — "Judgment dimensions vs tool-evidence dimensions"
  subsection maps dim ownership to critic kind with worked examples.
- `scorecard_kind.md` — on-disk file-shape discriminator
  (`human-verdict` vs `machine-summary`). Orthogonal to `kind` on the
  `_review.json` payload: a `tool_evidence` audit may use either
  scorecard kind.
- `anvil/lib/review_schema.py::Review._validate_kind_required_fields`
  — the validator that enforces this contract.
- `anvil/lib/probe_freshness.py` — the perishable-claim freshness
  advisory (issue #863) and its `probes.json` reader.
- `anvil/lib/evidence_drift.py` — the sibling advisory for the *other*
  half of the same problem: `BRIEF.md` / `refs/**` changing under a
  frozen version (issue #857). Probe freshness covers claims that rot
  because the outside world moved; evidence drift covers claims that
  rot because the thread's own evidence base moved.

## Sources

- CRITIC: Gou et al., "Tool-augmented LLMs for self-correction"
  (arXiv 2305.11738).
