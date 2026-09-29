# Rubric scoring shape and convergence logic

Every anvil skill ships a `rubric.md` with weighted dimensions whose
sum is the rubric's declared `total`. The shipped skills use
**/44 (9 dimensions, dim 9 *Rhetorical economy*)** or **/45 (9
dimensions, the two ip skills)**; legacy /40 (8-dimension) reviews
remain valid on disk and the lib is total-agnostic. This
snippet documents the SHAPE only — every skill picks its own dimension
names, weights, threshold, and total. The lib does not impose a
canonical dimension list (every observed skill has a different one)
and does not impose a canonical total (skills migrate from /40 to /44
independently; see "Per-review version stamping" below).

## Shape requirements

A skill rubric MUST:

1. Declare a **`total`** (positive integer point pool — `40` and `44`
   are the v0 shapes; the lib accepts any positive integer).
2. Define **8 or 9 dimensions** (the v0 observed counts) — long-term
   the rubric.py schema accepts ≥1 dimension and the skill's
   `rubric.md` is the source of truth for the count.
3. Assign each dimension an integer **weight** (in points).
4. Have weights that **sum to the declared `total`**.
5. Declare an **advance threshold** (integer, in points out of
   `total`).
6. Declare a **critical-flag** list (one-paragraph definitions of
   "any of these blocks regardless of total").

A skill rubric MAY:

- Document a calibration guide ("a score of N means ...") per
  dimension.
- Override critical-flag definitions per consumer
  (`rubric.overrides.md`).
- Document which critic owns which dimension (for skills with multiple
  specialists; see `critics.md`).

### Threshold-to-total anchor (suggested)

For skills picking a new threshold, the observed v0 pattern anchors
near `threshold ≈ round(total × 0.82)` — that yields `≥33/40` and
`≥36/44` as natural anchors and matches the canary's "high quality"
advance bar. The actual shipped thresholds (`≥35/44`, `≥39/44`,
`≥39/45`) sit close to this anchor; the skill's declared `threshold`
is the source of truth at runtime — the anchor is guidance only.

## Observed thresholds across v0 skills

| Skill | Total | Threshold | Dimensions | Critical-flag count |
|---|---|---|---|---|
| memo | /44 | ≥35/44 | 9 | 4 examples + open-ended |
| proposal | /44 | ≥35/44 | 9 | 4 hard rules + open-ended |
| paper | /44 | ≥35/44 | 9 | 5 examples + open-ended |
| slides | /44 | ≥35/44 | 9 | 3 hard rules (audit / density / time) + open-ended |
| deck | /44 | ≥39/44 | 9 | 4 hard rules (fabricated traction / fabricated team / market-math / absent ask) |
| report | /44 | ≥39/44 | 9 | 4 hard rules + open-ended |
| installation | /44 | ≥35/44 | 9 | 3 hard rules + open-ended |
| ip-uspto | /45 | ≥39/45 | 9 | §101 + §112 hard rules (each short-circuits) + open-ended |

Two patterns recur: (a) customer-facing or legal-facing artifacts use
the higher threshold band (`≥39`); internal or rough-draft-friendly
artifacts use the lower band (`≥35`); (b) skills have migrated `/40 →
/44` by adding **dim 9 *Rhetorical economy*** at weight 4 as
countervailing bloat-pressure (memo, proposal, paper, slides, deck,
report, installation), or — for `ip-uspto` — by adding a skill-
appropriate **dim 9 *Claim-spec correspondence*** at weight 5 to
preserve the flat-weight design (`/45`, every dim weight 5). The /44
skills choose a new threshold near the 0.82 anchor (memo/proposal/
paper/slides/installation at ≥35/44; deck/report at ≥39/44, the
customer-facing tier). The /45 ip-uspto threshold (≥39/45 ≈ 0.87) is
proportionally bumped from its prior ≥35/40 customer-facing tier.

## Dim 9 — teaching-oriented length is not padding

Dim 9 *Rhetorical economy* (weight 4, the /44 skills' shared bloat-
pressure dimension) exists to catch a document that could say the same
thing in fewer words — repeated hedging, restated conclusions,
throat-clearing, decorative elaboration. It does **not** exist to
penalize a document for being long because it is teaching something. A
passage that walks a reader from an ordinary-language statement of an
idea to a precise technical one — per the plain-language-first framework
in `anvil/lib/snippets/plain_language.md` (issue #1042/#1043) — is doing
the artifact's job, not padding it.

**The distinction a dim 9 critic applies:**

- **Padding (deduct):** the same claim restated in different words
  without adding information; a caveat repeated at every point of use
  after it was already labeled and ledgered (see `anvil/skills/memo/
  rubric.md` §"Redundant hedging" for the shipped worked example of this
  specific sub-pattern); decorative elaboration that could be deleted
  with no loss of meaning; hedging disproportionate to genuine
  uncertainty.
- **Teaching (do not deduct):** an ordinary-language explanation that
  precedes a technical term's first load-bearing use; a concrete example
  that makes an abstract claim legible; a plain restatement that survives
  alongside a newly introduced label (`plain_language.md` point 4); a
  worked example illustrating a claim a terser draft would have left as
  an assertion.

A useful test: **would deleting this passage remove information the
reader needs, or only remove words?** If deleting it removes
information — even if that information is "here is what this term
means in plain language" — it is teaching, not padding, and dim 9 should
not deduct for it. If deleting it changes nothing the reader could not
already infer from the surrounding text, it is padding, and dim 9
should deduct.

This calibration is a clarification of existing dim 9 scoring, not a new
sub-dimension or a change to the weight — a skill's `rubric.md` dim 9 row
already reads "does every paragraph carry weight the argument needs?"
(or equivalent per-skill wording); this section states explicitly that
"weight the argument needs" includes weight the *explanation* needs.

## Per-review version stamping

A rubric the skill ships today (`anvil-memo-v2`, `anvil-pub-v1`, …) is
NOT necessarily the rubric a historical review was scored against —
threads outlive rubric migrations, and a thread spanning a /40 → /44
bump records BOTH rubrics across its iterations. The framework records
the rubric a review was scored against as **per-review metadata** so
downstream consumers can compare scores apples-to-apples without
re-reading the skill's current `rubric.md`:

1. **`_meta.json.rubric_id`** + **`_meta.json.rubric_total`** +
   **`_meta.json.advance_threshold`** — the rubric the critic scored
   against. See `scorecard_kind.md` §"The discriminator".
2. **`_progress.json.metadata.score_history[].rubric_id`** — per-row
   stamp on the score-history so a thread that spans a migration
   records which rubric scored which iteration. See `progress.md`
   §"Convergence fields" → `score_history`.
3. **`_summary.md.rubric`** block — sibling to `lint` / `render_gate` /
   `summary_detail_consistency`, carrying the rubric `id`, `total`,
   `advance_threshold`, and `dimensions` count so an aggregator does
   not need to walk back to the skill's `rubric.md` file (which may
   have changed between v3 and v5). When the prior review sibling
   recorded a different `rubric_id`, the block also carries
   `prior_rubric_id` and (for legacy reviews missing `rubric_id`)
   `prior_rubric_inferred: "/40-legacy"`.

Reader contract (backwards-compat): a critic sibling produced before
this stamping landed MAY lack any of these fields. Readers MUST tolerate
the absence (treat missing `rubric_id` as `"unknown/legacy"` and the
review's `total` as advisory). See `convergence.check_stable` for the
precedent — it tolerates `None` entries in `score_history` without
short-circuiting.

`rubric_id` naming convention (informal, not enforced by the lib):
`anvil-<skill>-v<N>` for the generic gate rubric, bumped to `-v2` on a
breaking shape change (e.g., `/40 → /44` or `/40 → /45`). Pre-existing
literals in the codebase for advisory / overlay / vision rubrics:
`anvil-pub-neurips-v1`, `anvil-figure-content-v1`, `anvil-vision-v1`,
`anvil-report-vision-v1`, `anvil-ip-uspto-vision-v1`. All eight v0
artifact-class skills ship `-v2` for their main gate rubric post-#357:
`anvil-memo-v2`, `anvil-proposal-v2`, `anvil-pub-v2`, `anvil-slides-v2`,
`anvil-deck-v2`, `anvil-report-v2`, `anvil-installation-v2`,
`anvil-ip-uspto-v2`. The first seven ship `/44`; `ip-uspto` ships `/45`
to preserve its flat-weight design.

## Convergence logic

A version `<thread>.{N}/` advances out of the convergence loop when:

```
advance = (composite_total >= threshold) AND (no critical flag)
```

Both conditions must hold. Either falsy condition triggers another
revise iteration (within the `max_iterations` cap).

The composite total is computed by the reviser per the aggregation
rules in `critics.md` (per-dimension mean of non-null contributions
across all critic siblings, summed).

### Termination resolution order

The full termination decision considers **four** terminators, evaluated
in the following order — the first match wins:

| # | Condition | Verdict | `termination_reason` |
|---|---|---|---|
| 1 | Any critical flag set | `BLOCK` | `CRITICAL_FLAG` |
| 2 | `composite_total >= threshold` | `ADVANCE` | `THRESHOLD_MET` |
| 3 | `iteration >= max_iterations` | `REVISE` | `MAX_ITERATIONS` |
| 4 | Stable: last `lookback` totals within `± window` | `STALLED` | `STALLED` |

If none of the above match, the loop continues and the next revise pass
runs.

### Secondary stop condition: stable-score termination (#27)

Near the threshold the loop can oscillate (e.g., scores 31 → 32 → 31)
without converging, burning the iteration budget on a plateaued thread.
The **secondary** stop condition halts the loop when the score has
stopped changing meaningfully:

- Compare the last `lookback` aggregated totals (default `lookback=2`,
  i.e., the two most recent iterations).
- If all of them are within `± window` of each other (default
  `window=1`), AND the latest total is below threshold, AND no critical
  flag is set, halt with `verdict: STALLED` and
  `termination_reason: "STALLED"`.

The orchestrator (or human) then decides whether to escalate, swap
critics, or accept the below-threshold result.

The `STALLED` verdict is **distinct from** `MAX_ITERATIONS`:

- `STALLED` means "the loop demonstrably plateaued" — the score is no
  longer moving.
- `MAX_ITERATIONS` means "the loop ran out of budget" — the score might
  still have been climbing, but we hit the cap. The verdict stays
  `REVISE` (work did not converge); the `termination_reason` field is
  the signal that distinguishes the two.

The input to the stable check is `metadata.score_history` from
`_progress.json` (see `progress.md`). Defaults for `window` and
`lookback` match the rationale in #27. Skills may override per-thread in
`<thread>/.anvil.json`, alongside `max_iterations`.

The Python implementation is `anvil.lib.convergence.decide_termination`,
which is the source of truth for programmatic use. This snippet is the
source of truth for LLM-side authoring. The two MUST agree.

## Judgment dimensions vs tool-evidence dimensions

Rubric dimensions split along the CRITIC tool-vs-judgment line (see
`audit.md`). A **judgment dimension** is scored from the text alone by a
strong reader; a **tool-evidence dimension** requires an external
verification step (citation resolution, build check, numeric audit,
prior-art search). The split governs *which critic scores the dimension*,
not the dimension definition itself — the same dimension name can be
scored by a `kind: judgment` review critic and (re-)scored by a
`kind: tool_evidence` audit critic at the audit phase. The aggregator
merges contributions via the standard mean-of-non-null rule; it is
indifferent to which critic kind produced the score.

The same dimension can therefore appear on both a review and an audit
critic when the artifact warrants it. For example, a `methodology`
dimension on a `paper-review` (judgment-kind) might score how clearly the
method is *described*, while the same dimension on a `paper-audit`
(tool_evidence-kind) re-scores the same dim against a tool-verified
check that the cited datasets/code actually exist and behave as
described.

### Worked example: `anvil:paper`

| Dimension | Typically scored by | Kind | Why |
|---|---|---|---|
| `clarity` | `paper-review` | `judgment` | A reader can assess prose quality from the text alone. |
| `argument_coherence` | `paper-review` | `judgment` | Argument flow is a subjective-quality check. |
| `methodology` | `paper-review` + (optionally) `paper-audit` | `judgment` + `tool_evidence` | The reviewer scores method *clarity*; the auditor re-scores method *verifiability* (does the cited dataset exist, does the code compile). |
| `citation_recall` | `paper-audit` | `tool_evidence` | Requires resolving every `\cite{}` against `refs.bib` plus an external lookup of the cited source. |
| `citation_precision` | `paper-audit` | `tool_evidence` | Requires reading the cited source to verify claim support — a tool call (or human-in-the-loop on author-supplied PDFs in `<thread>/refs/`). |
| `build_cleanliness` | `paper-audit` | `tool_evidence` | Runs `pdflatex` / `bibtex` and inspects exit codes plus the compile log. |

### Worked example: `anvil:ip-uspto`

| Dimension | Typically scored by | Kind | Why |
|---|---|---|---|
| `claim_breadth` | `ip-uspto-claims` | `judgment` | A patent attorney scores claim scope vs prior art from the spec alone. |
| `s101_eligibility` | `ip-uspto-s101` | `judgment` | Statutory-subject-matter analysis from the spec; doctrinal, not tool-augmented. |
| `s112_enablement` | `ip-uspto-s112` | `judgment` | Written-description analysis from the spec; doctrinal. |
| `prior_art_coverage` | `ip-uspto-priorart` (judgment today, `tool_evidence` once tool-augmented) | `judgment` → `tool_evidence` | When the prior-art critic searches an external corpus, it becomes a tool-evidence critic; today it ships judgment-only. |
| `inventor_consistency` | `ip-uspto-audit` | `tool_evidence` | Cross-checks `spec.tex` front matter against `inventorship.md` and `BRIEF.md` — a grep/diff tool call per inventor. |
| `reference_numeral_coherence` | `ip-uspto-audit` | `tool_evidence` | Greps every `\ref{}` against the figure source files. |

The takeaway: judgment dimensions tend to live on review-class critics
(`<skill>-review` and doctrinal specialists); tool-evidence dimensions
tend to live on audit-class critics. The same rubric dim can appear on
both classes when the artifact warrants belt-and-suspenders verification.

## Critical-flag semantics

Critical flags are NOT a sub-score deduction. They are a binary
short-circuit:

- **Critical flag set** → block regardless of total. Even a 38/40 (or
  42/44) with one critical flag does not advance.
- **Critical flag NOT set** → fall back to the score-vs-threshold
  check.

This matches the intuition that some defects cannot be averaged away:
a deck with fabricated traction does not become more truthful by being
well-designed; a paper with a citation error does not become more
correct by being well-written.

## Dimension scoring guidance (applies to all skills)

1. **Justify every score — with quoted evidence.** Each per-dim score
   in `scoring.md` carries 1–3 sentences of justification citing
   specific evidence from the artifact (section heading, slide number,
   excerpt, exhibit reference). A score without justification is not a
   useful signal for the reviser. Beyond that (issue #464, the
   draftwell "no score without quoted-evidence critique" discipline):

   - **Quoted-evidence sub-rule.** Each dimension's justification MUST
     embed at least one **verbatim quote from the reviewed body**,
     wrapped in double quotes, followed by a location anchor:
     `("the quoted span" — §2.1)`. The anchor is a section heading,
     slide number, or line reference — human-facing navigation aid,
     not machine-validated. Use inline `"..."` spans, NOT markdown
     blockquotes — justifications live in single table cells
     (`# | Dimension | Weight | Score | Justification`) and
     blockquotes do not survive table cells. A quote that does not
     appear verbatim in the body is **fabricated evidence** — a major
     defect in the review itself, worse than no quote at all.
     **Elision with `...` / `…` is permitted** (issue #478): a quote
     may skip intervening text with an ellipsis, provided each elided
     fragment is itself verbatim from the body, long enough to count
     as evidence on its own (≥ the verifier's `MIN_QUOTE_CHARS`
     floor), in document order, and drawn from one nearby passage
     (within the verifier's `ELISION_WINDOW_CHARS` proximity window —
     do NOT stitch fragments from distant sections into one quote).
     Em/en dashes may be typed as `--` / `---`; the verifier folds
     dash variants symmetrically.
   - **Ceiling-by-absence contract.** A dim scored at **full weight**
     MAY substitute the marker phrase `no instance of <X> found` for a
     quote — absence of defects has no quotable span (e.g., dim 9 at
     4/4 with "no instance of multi-paragraph hedging found"). Below
     ceiling, the quote requirement stands: a deduction always has a
     quotable offending passage.
   - **Deterministic verifier.** `anvil/lib/evidence_check.py`
     (`python -m anvil.lib.evidence_check <version_dir>
     [--scoring <path>]`) mechanically checks that each justification
     contains at least one quoted span that actually appears in the
     body. Missing quote → minor advisory finding; quoted span absent
     from the body → major `fabricated_evidence` finding. Anchors are
     not validated (judgment-free scope). Reviewer commands SHOULD run
     it as a write-time self-check before their scoring sidecar lands;
     it is also runnable post-hoc over legacy review dirs (advisory
     only — never mutates, never gates).
   - **Coordination with voice grounding (issue #461).** This rule
     targets the *reviewed body*; `voice_grounding.md` §"Reviewer
     contract" requires voice deductions to quote the *corpus*
     (exemplar ground truth). The two are complementary, not in
     conflict: a voice deduction under both contracts quotes BOTH the
     offending body passage (this rule) and the corpus exemplar it
     falls short of (voice grounding).

2. **Be calibrated, not encouraging.** The rubric exists to surface
   problems early. A reviewer who scores generously to spare the
   drafter's feelings wastes a revision iteration.

3. **Integer scores only.** No half-points. If you cannot decide
   between 4 and 5, that is a 4 with a justification that explains
   what would push it to 5 on the next iteration.

4. **Critical flags are not bonus points.** A flag is "this would
   stop a sophisticated reader cold". Set them when warranted; do
   not set them for stylistic concerns or polish issues (those live
   in comments at severity `minor` or `nit`).

## Rubric–perspective interaction (opportunistic, not punitive)

A perspective sibling (see `perspective.md`) is **optional input** the
drafter MAY consume to ground claims in external substrate. When
present, it raises the **ceiling** on dimensions that depend on external
substrate; it does **not** lower the floor when absent. The interaction
is **opportunistic**, not punitive — a load-bearing distinction that
makes perspective safe to introduce without breaking the convergence
behaviour of legacy threads that have no perspective sibling.

### The rule

For any rubric dimension a per-skill rubric extension names as
**substrate-sensitive** (typically the dimensions that score "external
evidence quality" — market sizing, related-work positioning, competitive
differentiation, cost sourceability, evidence quality):

- **When `<thread>.0.perspective/` (or the latest
  `<thread>.{N}.perspective/`) is present AND the artifact's
  load-bearing claims cite candidates from `candidates.md` (by anchor
  id or by the candidate's source pointer):** the cited claims are
  treated as **substrate-backed**, and the dimension MAY score higher
  than it would without the perspective citation. The reviewer treats
  a perspective candidate's structured `Source:` field as an
  inline-footnote-equivalent hook for the surrounding claim. Scores at
  the top of the dimension's calibrated range (4/5 or full weight)
  become defensibly reachable on this evidence.
- **When the perspective sibling is absent OR present-but-not-cited:**
  the dimension scores against the legacy baseline. **No new
  deduction** is taken for the absence — the scoring rule is identical
  to the pre-perspective behaviour. A thread that has never run
  `<skill>-perspective` is unaffected by this interaction.
- **When the perspective sibling's `notes.md` "Identified gaps"
  explicitly names a substrate area as un-covered AND the artifact
  makes a load-bearing claim about that area without sourcing it:**
  the standing per-instance deduction the dimension already enforces
  (see the skill's existing citation-hook / refs / sourceability sub-
  rules) is the natural escalation path. **No new** deduction is
  introduced by this interaction — the perspective sibling sharpens
  the *existing* deduction by surfacing that the drafter was told the
  substrate was missing and made the claim anyway.

### Opportunistic, not punitive (the architect's core contract)

The rule is **opportunistic**: perspective can move a score **UP**,
never **DOWN**. Two equivalent statements:

1. A claim with a perspective-cited candidate scores at least as well
   as the same claim without one (and typically scores higher,
   substrate-backed-claim being the higher-credibility mode).
2. Removing a perspective citation from an otherwise-identical artifact
   does not raise its score — only lowers or holds it.

The framework enforces this property through the **no-new-deduction**
clause: per-skill rubric extensions that adopt this interaction MUST
NOT introduce a new deduction keyed on perspective absence. They MAY
introduce a new positive-evidence rule (cited candidate → substrate-
backed) and MAY sharpen an existing deduction (un-cited claim against
a known-gap → the existing deduction is applied to a more clearly-
established miss).

This contract is the reason perspective is safe to ship incrementally:
a skill that adds a `<skill>-perspective` command and updates its
rubric does NOT break review continuity for legacy threads in the same
consumer repository.

### Per-skill rubric extension shape

A per-skill rubric that adopts the perspective interaction adds a
subsection (typically `§"Perspective substrate (dim N)"`, sibling to
existing per-dim sub-rules like `§"Citation hooks (dim N)"` and
`§"Refs back-check (dim N)"`) that:

1. Names the substrate-sensitive dimension(s) and what kind of claim
   the dimension scores (market-size claim, related-work claim,
   competitive claim, sourceability claim, …).
2. Anchors to this snippet by reference (so the cross-skill contract
   stays visible).
3. States the opportunistic-not-punitive rule explicitly for the
   skill's domain — typically: "with perspective: substrate-backed
   claims score higher; without perspective: unchanged baseline".
4. (Optionally) names the natural-escalation path for an existing
   deduction when a known-gap claim is made un-hooked.

The v0 adopters are `anvil:deck` (dims 3 + 4 + 10), `anvil:memo` (dim 3),
`anvil:proposal` (dim 6 with light dim 4 reference), and `anvil:paper`
(dim 4 — codifies the implicit litsearch rule). Other skills (`slides`,
`installation`, `ip-uspto`, `report`) do not currently consume
perspective and SHOULD NOT add rubric language until they ship a
`<skill>-perspective` command.

### Why this is load-bearing

Per the Epic #143 architect proposal: "Adding `{skill}-perspective`
commands without touching the rubric will produce minimal behavior
change — drafters will skip it." A drafter that sees no scoring upside
to running the substrate-gathering step will skip it under deadline
pressure. The rubric interaction closes that gap by making
perspective-cited claims **measurably better** at the rubric level
without making perspective-absent threads **measurably worse** — the
positive-incentive design the canary signal asks for.

## Citation-quality dimensions (optional, opt-in per skill)

Skills that produce sourced artifacts may name two of their dimensions
using the canonical citation-quality vocabulary:

- **`citation_recall`** — claims-with-citations / total-claims. How
  much of the artifact's load-bearing content is sourced.
- **`citation_precision`** — claims-supported-by-cited-source /
  claims-with-citations. How well the cited sources actually back the
  claims they're attached to.

Both are integer scores on the same /weight scale as any other
rubric dimension. The two-dim shape (rather than one combined
"citation hygiene" dimension) lets each axis move independently —
high recall with low precision is a different failure mode than the
inverse.

This is **opt-in**, not mandatory. Skills that don't produce sourced
artifacts (`anvil:deck`, `anvil:slides`) leave them out entirely.
Skills that do (`anvil:paper`, `anvil:report`, `anvil:memo`,
`anvil:ip-uspto`) may name two of their nine dimensions accordingly.
The lib does not enforce or detect this naming — it documents the
convention so the eventual citation auditor critic can populate
identifiable per-dimension scores per the existing partial-scorecard
rule (see `critics.md`).

### Per-consumer rubric migration

The skill's declared `total` envelope is preserved by **splitting** an
existing citation-related dimension rather than adding two new ones
outside that envelope. Worked examples (both shown for /40 skills; a
/44 skill follows the same pattern against its own envelope):

| Skill | Before | After |
|---|---|---|
| `anvil:paper` | dim 8 "Citation hygiene", weight 5 | `citation_recall` + `citation_precision`, weights 2 + 3 (or any split summing to 5) |
| `anvil:report` | dim 4 "Evidence trail / citation", weight 6 | `citation_recall` + `citation_precision`, weights 3 + 3 |

The migration is per-skill and **not in scope** for the lib PR. Each
consumer skill that opts in does so in its own follow-up PR (rubric.md
edit + the owning critic's command spec).

STORM (stanford-oval/storm) reports 84.83% / 85.18% on these dimensions
in its retrieval-grounded essay generation, useful as calibration
anchors when authoring a new rubric.

## Rubric override mechanism

Every skill ships `rubric.md` in its source-controlled root. Consumers
override via `.anvil/skills/<skill>/rubric.overrides.md` in their own
repo. The override file:

- **Adds** critical-flag examples specific to the consumer's domain.
- **May tune** dimension calibration guidance.
- **Cannot reduce** the base rubric — overrides are additive only.

The reviewer command loads both files (base + override) and applies
both during scoring.

## Advisory rubric overlays

Some skills (currently `anvil:paper`) ship **advisory rubric overlays**
in addition to the generic gate rubric. These are venue-pinned YAMLs
(e.g. `anvil/skills/paper/rubrics/neurips.yaml`) that produce
supplementary scoring for venue-specific signal — NeurIPS
reproducibility checklist, Nature's broad-significance bar, arXiv's
category-correctness norm — without breaking the framework-wide
gate-rubric invariant ("the skill's declared `total` means the same
thing across versions of that skill's reviewer").

Key properties of advisory rubrics:

- **They do NOT change the convergence gate.** The generic gate rubric
  (the skill's `rubric.md`, with its declared `total` and `threshold`)
  remains the sole driver of the `advance` decision. The venue overlay
  produces additional findings the reviser consumes; it does NOT
  contribute points to the gate-deciding total.
- **They relax the sum-to-total invariant.** A venue overlay may
  declare any sensible total (NeurIPS /16, Nature /15, arXiv /10).
  The gate-rubric sum-to-total rule applies only to the gate rubric
  (`advisory: false`).
- **Threshold is optional.** Advisory rubrics have no gate, so no
  threshold is required.

The on-disk shape is the same `Rubric` model in `anvil/lib/rubric.py`
(YAML-loaded) — the `advisory: true` flag is the discriminator. The
machine-readable JSON Schema lives at
`anvil/lib/rubric_schema.json`.

Reviewer commands that consume an advisory rubric write its scores
as a second `_review.json`-shaped file in the same `.review/` sibling
directory (canonical name: `_review.venue.json`). Both files use the
existing `Review` schema in `anvil/lib/review_schema.py`; the
reviser's existing N-critics-one-reviser aggregator treats the
venue file as one more critic input and the convergence gate is
computed from the generic file only (filtered by `rubric` id).

See `anvil/skills/paper/SKILL.md` and `anvil/skills/paper/rubric.md` for
the canonical example of an advisory overlay in use.

## See also

- `critics.md` — how multi-critic aggregation produces the composite
  per-dimension score and critical flag.
- `scorecard_kind.md` — how the reviser knows what file shape to read
  from each critic.
- `state_machine.md` — where the convergence check sits in the
  lifecycle.
- `audit.md` — the `.review/` (judgment) vs `.audit/` (tool-evidence)
  distinction with skill-by-skill mapping table.
- `perspective.md` — the pre-draft external-substrate sibling whose
  presence triggers the opportunistic rubric interaction documented
  in §"Rubric–perspective interaction" above.
