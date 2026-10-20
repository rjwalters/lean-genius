# Pending-measurement placeholder convention

This snippet codifies a first-class convention for drafting an artifact
whose load-bearing number does not yet exist — a training run still
running, a benchmark queued, a vendor quote not returned. Without a
supported convention, correct behavior depends on ad-hoc per-thread
prompt discipline hand-written into `BRIEF.md`, and critics have no way
to distinguish "this number is missing because it's genuinely pending"
from "this number is missing because the drafter was sloppy" — or,
worse, from a drafter who fabricates a plausible-looking number rather
than admit the gap. This snippet promotes the framework-level
`anvil/lib/pending_marker.py` primitive so any skill can adopt the
convention without reinventing it.

## The marker syntax

A drafter marks a genuinely-outstanding value with a bracketed
placeholder naming its source:

```
The model reaches [PENDING benchmark-run-2024-11] accuracy on the
held-out set.

Component cost is [PENDING: vendor-quote-acme] per unit at the quoted
minimum order quantity.
```

**Well-formed shape**: `[PENDING <source>]` or `[PENDING: <source>]` —
the literal, **case-sensitive** keyword `PENDING` immediately after the
opening bracket, a colon and/or whitespace separator, then a non-empty
`<source>` label naming *what* is pending (a benchmark run id, a
vendor name, "Q3 earnings call", a training-run identifier), then the
closing bracket.

The uppercase keyword is deliberate — it mirrors the `TODO`/`FIXME`
code-comment convention so a genuine marker is visually and
mechanically unambiguous. It also means ordinary prose that happens to
use the word "pending" (*"results are pending"*, *"a decision is
PENDING review"*) is never mistaken for a marker: the detector matches
only the bracketed, uppercase, source-bearing shape.

**A source-less marker (`[PENDING]`, `[PENDING ]`) is malformed and is
NOT detected as a marker at all** — it degrades to an unexplained
bracket for both a human reader and the detector. Always name the
source; a marker without one defeats the purpose (a reader — or
critic — has no way to know what's being waited on, or when it will
resolve).

## No-fabrication discipline

This convention exists for the same reason `perspective.md`'s
no-fabrication rule exists (see that snippet's "No-fabrication rule"):
an LLM drafter under pressure to produce a complete-looking artifact
will otherwise either (a) silently invent a plausible number to fill
the gap, or (b) leave vague hand-wavy language ("results are
promising") that reads as evasive rather than honest. **Neither is
acceptable.** The pending marker is the third option: name the gap
explicitly, name what's needed to close it, and let the deterministic
gate (below) keep the artifact from shipping with the gap still open.

A drafter facing a genuinely-unresolved number MUST use a well-formed
pending marker rather than fabricate a value or hand-wave around the
gap. This rule is as load-bearing as `perspective.md`'s citation
discipline — the difference between "honest about what's not done yet"
and "fabricated to look done" is exactly the failure mode this
convention closes.

## Not a defect — but not silently ignored either

A well-formed pending marker gets three, deliberately different,
treatments from a consuming skill's critics:

1. **No dimension score penalty.** A reviewer scoring the artifact
   against its rubric MUST NOT deduct points on any dimension *because*
   a well-formed marker is present (e.g. an evidence-sufficiency or
   reproducibility dimension should not mark down for "missing data"
   when the data is honestly declared as pending). The marker is a
   disclosure, not a defect.
2. **Never a blocking `Verdict.BLOCK`.** The marker surfaces as a
   specially-resolved `pending_dependency`-typed `CriticalFlag` (an
   *additive* flag type — see below), which is **visible** in the
   aggregate but is filtered out of the ordinary blocking-critical-flag
   trigger (`convergence.blocking_critical_flags`). It does NOT tank the
   review/audit verdict the way a fabricated-citation flag does. This is
   the load-bearing distinction: routing a pending marker through the
   ordinary `Verdict.BLOCK` path would tell the reviser (per a skill's
   "critical flags MUST be addressed" prose) to *resolve* it in prose —
   i.e. to invent the still-outstanding number, the exact fabrication
   this convention exists to prevent.
3. **Gates `READY`/`AUDITED` — separately.** An artifact with any
   unresolved pending marker cannot reach a terminal state. This is
   enforced by a **separate terminal-state check** the consuming skill
   runs before promoting to `READY`/`AUDITED`
   (`convergence.has_pending_dependency_flag(aggregate.critical_flags)`,
   or a deterministic re-run of the CLI + its exit code), decoupled from
   the score/verdict path. Resolving a marker means replacing its
   bracketed text with the real value — at that point the next detector
   pass finds nothing and the gate clears.

Combining these rules matters: double-penalizing (a low dimension score
**and** a blocked verdict) punishes the honest disclosure the
convention exists to encourage, which pushes drafters right back toward
fabrication or hand-waving. The outstanding-dependency surface alone
communicates "not done yet"; the dimension scores reflect the
argument's soundness *assuming* the pending value resolves as
described.

## The distinct, specially-resolved flag type

`pending_dependency` is an **additive** `CriticalFlag.type` value (no
schema-version bump), modeled on the `no_go` precedent
(`anvil/lib/convergence.py`) — but with the *opposite* posture. Where a
`no_go` flag is a *stronger* terminator than a generic critical flag
(short-circuiting to `Verdict.NO_GO`), a `pending_dependency` flag is a
*weaker* signal: it never forces `Verdict.BLOCK` and never deducts a
dimension score. It carries its own priority tier in
`compute_verdict`/`decide_termination`:

- `convergence.blocking_critical_flags(flags)` — the blocking subset,
  with `pending_dependency` filtered out. `critics.py` computes
  `any_critical` from this subset, so a pending-only review yields a
  score-driven verdict (`ADVANCE`/`REVISE`), never `BLOCK`.
- `convergence.has_pending_dependency_flag(flags)` — the terminal-state
  query. The consuming skill calls this before promoting to
  `READY`/`AUDITED`.

## The deterministic gate

Unlike a nuanced judgment call (e.g. "does this citation actually
support this claim?"), whether a well-formed marker is still present in
the body is a binary, mechanical fact — there's no ambiguity to
adjudicate. `anvil/lib/pending_marker.py` is therefore a
**judgment-free deterministic gate**: it emits the `pending_dependency`
flag (and per-marker `nit` findings) mechanically when any active
marker remains, rather than relying on an LLM reviewer to notice the
marker text and decide, on its own initiative, to write a flag. This is
the direct fix for the "ad-hoc per-thread prompt discipline" problem
the convention exists to close — the gate does not depend on anyone
remembering to check.

**Suppression.** A marker on a line carrying (or directly below) a
`<!-- anvil-lint-disable: pending_marker -->` directive is recorded as
a non-gating note and excluded from `outstanding_sources` — the same
suppression convention every other deterministic-checks-family module
honors. Use it only for a documentation passage that must show a
live-looking marker outside a code fence.

See the `anvil/lib/pending_marker.py` module docstring for the full
detection/masking/severity contract, and `anvil/lib/numeric_consistency.py`
for the sibling deterministic-checks-family precedent this module
follows (masking, sidecar shape, suppression convention).

## Sidecar shape

`anvil/lib/pending_marker.py::write_review_dir` writes
`<thread>.{N}.pending/_review.json` via the standard staged-sidecar
atomicity primitive (`anvil/lib/sidecar.py`). The `.pending` tag is a
single path segment, so `anvil/lib/critics.py::discover_critics` picks
it up automatically — no aggregator change is needed to wire a new
consumer skill in. Because the check is deterministic and cheaply
re-runnable, a later pass freely overwrites an earlier pass's sidecar
for the same version dir — the same deterministic-regeneration
carve-out `numeric_consistency.py` documents for its own sidecar.

## Optional `BRIEF.md` frontmatter: `pending_sources`

A thread MAY declare the pending sources it expects to resolve over its
lifetime in `<thread>/BRIEF.md` YAML frontmatter — a list of bare
source labels, or `{source, expected_by}` mappings:

```yaml
---
pending_sources:
  - benchmark-run-2024-11
  - source: vendor-quote-acme
    expected_by: 2026-08-15
---
```

Parsing/validation lives in `anvil/lib/project_brief.py`
(`resolve_pending_sources`, modeled on the `spec_ref`/`code_ref`
companion-input validators in that same file — NOT a bespoke parser in
`pending_marker.py`). It is **purely a reporting aid** — declaring a
source here has NO effect on gating: an undeclared marker still gates
the terminal state, and a declared-but-never-written source is not
itself a defect. What it enables is a critic reporting, e.g., *"3 of 5
declared pending sources resolved; 2 outstanding: vendor-quote-acme,
benchmark-run-2024-11"* — visibility into which of the anticipated gaps
are still open, without requiring the reviewer to scroll the whole body
looking for brackets.

## Adopting the convention in a skill

To wire this convention into a skill's review/audit lifecycle:

1. In the skill's `<skill>-review` command, invoke
   `python -m anvil.lib.pending_marker <thread>.{N}/ --write-review`
   (or the `check_pending_markers` / `write_review_dir` Python API
   directly). This is an unconditional step — no per-thread opt-in
   needed, mirroring `numeric_consistency`'s always-on posture. The
   emitted `pending_dependency` flag is safe to write unconditionally:
   it is specially resolved and never forces `Verdict.BLOCK` (see "The
   distinct, specially-resolved flag type" above).
2. Fold `result.outstanding_sources` / `result.resolved_sources` into
   the reviewer's `verdict.md`/`findings.md` as an explicit "Outstanding
   dependencies" note — this is the human-legible half of the
   acceptance criteria; the deterministic flag alone is not enough for
   an operator to know *what* is still pending.
3. **Gate the terminal state separately.** Before promoting the thread
   to `READY`/`AUDITED`, query
   `convergence.has_pending_dependency_flag(aggregate.critical_flags)`
   (or re-run the CLI and check its exit code / `pass` field) and hold
   the terminal transition while any active marker remains. Do NOT wire
   the pending marker into the ordinary blocking-verdict path.
4. Document the category in the skill's `rubric.md` as an **outstanding
   dependency, NOT a critical flag** (mirror `paper/rubric.md`'s
   "Outstanding dependencies (not critical flags)" section), and add a
   scoring-guidance note that a well-formed marker does not incur a
   dimension penalty — the rule an LLM reviewer is most likely to get
   wrong by default (the instinct to mark down for "missing data" is
   strong).
5. **Add the reviser carve-out.** In the skill's `<skill>-revise`
   command, explicitly instruct the reviser to NEVER fabricate a value
   to clear a `pending_dependency` flag — carry the marker forward
   verbatim until the real value lands (mirror `paper/commands/paper-revise.md`'s
   "NEVER fabricate a value to clear a `pending_dependency` flag" note).
   This is the load-bearing prose fix: without it, a reviser following
   the generic "critical flags MUST be addressed" instruction would
   invent the number.
6. Optionally, re-run the check at the skill's terminal-gate/audit
   phase too (defense in depth — useful when an operator runs the
   audit phase before the review loop reaches `READY`, which several
   skills' audit commands explicitly permit).

No framework changes are required beyond these skill-local wiring
steps — the discovery glob in `critics.md` picks up the new
`.pending/` sidecar automatically, and the `pending_dependency` flag
type is already resolved by the shared `convergence.py`/`critics.py`
verdict path.

## See also

- `anvil/lib/pending_marker.py` — the detector/emitter module this
  snippet documents.
- `anvil/lib/numeric_consistency.py` — the sibling deterministic-checks
  primitive whose masking/sidecar/CLI shape this module mirrors.
- `perspective.md` — the no-fabrication framing this snippet's
  discipline section is adapted from.
- `critics.md` — sidecar discovery, aggregation, and the critical-flag
  short-circuit mechanism this convention routes through.
- `rubric.md` — the general "Dimension scoring guidance" contract a
  consuming skill's own `rubric.md` extends with the pending-marker
  critical-flag entry.
