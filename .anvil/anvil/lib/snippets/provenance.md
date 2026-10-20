# Claim provenance: local-corpus ground-truth verification

This snippet codifies the **local-corpus claim-provenance contract**
(issue #597) — how a project declares a read-only ground-truth corpus,
how the drafter records a per-version claim→source map, how the
reviewer spot-checks it, and how an audit critic verifies each mapped
claim against the corpus on disk and classifies it. It defends against
the failure mode a grounded artifact fears most: an LLM drafting pass
hallucinating plausible dates, quotes, and attributions that no source
supports.

The canary is `example-memoir` (a family memoir): every quote and every
factual claim must trace to a local ground-truth corpus — seven
interview transcripts and nine family letters. But the contract
generalizes to any artifact grounded in a private evidence base:
engagement notes for `report`, lab notebooks for `paper`, customer
interviews for `proposal`.

## Scope boundary (vs. voice fidelity, #598)

This contract owns **substance verification** — *does the corpus
actually contain a passage supporting this named fact, date, memory, or
event?* It does **not** own whether a reconstructed line *sounds* like
the speaker; that voice/cadence-fidelity half is the `voice.subjects`
tier (issue #598, `anvil/lib/snippets/voice_grounding.md`). The
touchstone for a line "She said X happened in 1924":

- **#597 (this contract)** asks: *does the transcript corpus contain
  any passage supporting that event in 1924?*
- **#598** asks: *does the reconstructed line sound like how she would
  phrase it?*

Both matter; neither contains the other. **Misattribution** sits at the
boundary and is split cleanly: substance-level misattribution — an
event or memory attributed to a speaker whose corpus does not contain
it — is **this contract's** `misattribution_of_substance` flag;
voice-identity misattribution — right substance, rendered in the wrong
voice — is #598's flag. The two tiers are independent and a memoir may
declare both.

## Scope boundary (vs. the AI-authorship byline, #941)

A third, unrelated tier lives beside this one: the opt-in `ai_byline:`
BRIEF block (`anvil/lib/project_brief.py::AiByline` /
`resolve_ai_byline`, rendered by `anvil/lib/ai_byline.py`). Where this
contract (`corpus:`) verifies **substance** — does a claim trace to a
real source passage? — the AI-byline tier discloses **authorship**: a
short, consumer-configured line an artifact's drafter/reviser can append
to a rendered deliverable stating it was drafted with AI assistance.

The two are independent and unrelated: a project may declare `corpus:`
without `ai_byline:` (verified substance, no authorship disclosure), or
`ai_byline:` without `corpus:` (authorship disclosed, no local-corpus
verification applies — e.g. an essay with no evidentiary corpus), or
both, or neither. Neither tier implies the other.

The AI-authorship byline is **also** distinct from — and not a
substitute for — the intrinsic, server-side, token-level model-output
watermark (the green-list logit-bias mechanism mandated for EU AI Act
transparency). That watermark targets the *adversarial* case (detecting
AI text passed off as human) and is entirely out of a consumer's
control. The byline is the *honest-actor* complement: a self-publisher's
own, detachable, discretionary editorial choice to disclose AI
assistance on their own terms. It carries no tamper-resistance claim and
makes no claim to be a watermark. See `anvil/lib/ai_byline.py` and the
per-skill `ai_byline:` integration (e.g. `essay`'s SKILL.md
§"AI-authorship byline") for the rendering contract.

## Section 1 — BRIEF activation

A project declares its factual ground truth via ONE optional
**top-level** key in the project `BRIEF.md` frontmatter (parsed by
`anvil/lib/project_brief.py::_normalize_corpus_dirs`, resolved by
`resolve_corpus_dirs`):

```yaml
corpus:                    # NEW top-level key (issue #597): factual ground truth
  - transcripts/           #   read-only directories of source evidence
  - letters/
```

This is **distinct from `voice.corpus`** — a single glob nested *under*
`voice:` naming author-persona *published* exemplars (`ResolvedVoiceDoc`,
issue #461). The top-level `corpus:` is a **list of directory paths** for
factual sources. Different YAML level, different purpose, no naming
conflict. A project may legitimately carry both:

```yaml
voice:
  corpus: writing-corpus/**/*.md   # author voice exemplars (VoiceDocs.corpus, #461)
corpus:                            # factual ground-truth sources (ProjectBrief.corpus, #597)
  - transcripts/
  - letters/
```

Activation rules (byte-identical when absent):

- **`corpus:` declared with ≥1 path → tier ACTIVE.** The drafter writes
  a `provenance.md` map, the reviewer back-checks it, the audit critic
  verifies it.
- **Absent key, `corpus: null`, or `corpus: []` → tier INACTIVE.**
  Byte-identical no-corpus behavior: no `provenance.md` required, no
  findings, no extra reads. `resolve_corpus_dirs` returns `[]`; callers
  branch on `if not resolved:` for the inactive path.
- **A single string** (`corpus: transcripts/`) normalizes to a
  one-element list. A **non-string list element** raises `ValueError`
  with the field path (e.g. `BRIEF.corpus[1]`).
- **Declared-but-missing corpus directory → the tier ACTIVATES** and the
  breakage surfaces as a **`major` review finding** (a structured
  `missing: true` `ResolvedCorpusDir`, never a raise — the same
  defect-to-surface posture as voice grounding). Resolution is
  project-root first, then consumer-root; git status is never consulted
  (a `.gitignored` corpus resolves identically to a committed one).

Resolve with
`anvil/lib/project_brief.py::resolve_corpus_dirs(project_dir,
consumer_root=None)` — do not re-implement the walk. It returns one
`ResolvedCorpusDir` per declared path, in declared order, each carrying
`declared` / `path` (absolute, `None` when missing) / `missing` /
`source` (`project` | `consumer` | `absolute`).

## Section 2 — the per-version `provenance.md` claim→source map

When the corpus tier is active, the drafter writes a
`<thread>.{N}/provenance.md` file **at draft time, before prose**, and
keeps it current through every revise pass (each `<thread>.{N+1}/`
carries a refreshed map). It is a markdown table mapping each attributed
quote or factual claim to its supporting corpus passage:

```markdown
# Claim provenance — <thread>.{N}

| Claim | Source file | Line range | Anchor | Notes |
|-------|-------------|------------|--------|-------|
| "The factory burned down" | transcripts/nita3.txt | 412-415 | "the factory burned down in the summer of 1942" | verbatim recall |
| Journey took six weeks | letters/1940-aug.rtf | 3-7 | "the crossing took nearly six full weeks" | inferred from dates |
```

Column contract:

- **Claim** — the attributed quote (verbatim, in quotes) or the factual
  assertion (paraphrased) as it appears in the artifact.
- **Source file** — a path **relative to a declared corpus directory**
  (e.g. `transcripts/nita3.txt`), resolvable under one of the
  `resolve_corpus_dirs` roots.
- **Line range** — a `start-end` line span (or a single line) **hinting**
  at the supporting passage's current location. This is a hint, not the
  row's identity — see "Anchor: the stable identity" below. The cell MAY
  hold **several comma-separated ranges** (`61-63, 1, 37-39`) when a claim
  draws on more than one place in the cited file, or a reviser has left a
  prior hint in place alongside a new one — every range in the cell is a
  candidate location, in no particular priority order (issue #1204: the
  anchor-bearing range does NOT need to be listed first). See "Anchor: the
  stable identity" below for how a multi-range cell resolves.
- **Anchor** (issue #868) — a short **verbatim quoted snippet** copied
  exactly from the cited passage (curly-quote and whitespace differences
  are tolerated; wording is not). This is the row's stable,
  content-addressed identity — the thing a corpus audit actually
  searches for. May be blank on a row migrated from a pre-#868 table (see
  "Backward compatibility" below); MUST be populated on every row the
  drafter writes going forward.
- **Notes** — the drafter's brief characterization (`verbatim recall`,
  `inferred from dates`, `paraphrase`). The drafter fills `Notes`; the
  **audit critic** — not the drafter — assigns the five-way
  classification (Section 5).

### Anchor: the stable identity

A bare `Line range` is an address, not evidence: any edit to the corpus
file that shifts lines above a cited row (an insertion, a reflow, an
appended correction) silently moves what that row points at while it
keeps resolving to *something* — the row still "works," it just now
cites the wrong text. A spot-sampling reviewer reading plausible text at
the stale range passes it; only an exhaustive audit that re-opens every
range catches the drift, and only if it re-runs after the corpus
changed. This is exactly the failure mode issue #868 documents (a
six-line insertion silently invalidating three rows of a
terminal-AUDITED chapter, discovered only because a full corpus audit
happened to re-run).

The **Anchor** column fixes this by making the citation content-
addressed instead of position-addressed: the audit critic (Section 4)
searches the WHOLE cited file for the anchor's exact text, not just the
hinted range, and reports where it actually is. `Line range` becomes a
cheap-to-read hint that is refreshed mechanically when it goes stale
(Section 4a) — never the ground truth.

**Multi-range cells** (issue #1204): when `Line range` cites several
comma-separated ranges, the anchor is considered RESOLVED if its actual
location overlaps **any** of them — not only the first. Order within the
cell carries no meaning; a corpus audit tool that only checked the first
range (as `anvil/lib/provenance_anchor.py` did before #1204) produced a
false `DRIFTED` on a correct row whenever the anchor's true location fell
in a later range. If the anchor's location overlaps none of the cell's
cited ranges, the row is genuinely `DRIFTED`; a mechanical `repoint`
collapses the whole cell to the anchor's single corrected location rather
than appending it to the (now all equally stale) old ranges.

**Anchor-writing discipline** (drafter and reviser, every row that has
supporting text at all):

- Copy the anchor **verbatim** from the passage the row cites — a
  contiguous span, long enough to be unambiguous in the file (a full
  clause or sentence fragment is typically enough; a two-word snippet is
  not). Do not paraphrase the anchor — paraphrase belongs in `Notes`.
- The anchor does not have to be the entire cited passage or match the
  `Claim` cell's wording — it only has to be a verbatim substring of the
  passage that the `Line range` currently points at.
- A row recorded with an explicit `NOT_FOUND` source note (no corpus
  passage supports the claim) has no anchor to give — leave the `Anchor`
  cell blank; nothing here changes the existing "cut it or mark
  `NOT_FOUND`, never fabricate" discipline below.

### Backward compatibility

A `provenance.md` table written before issue #868 has either no
`Anchor` column at all (the legacy 4-column shape) or, row-by-row, an
empty `Anchor` cell. Both are tolerated indefinitely — **never a defect,
never coerced, never migrated in bulk.** A row with no anchor simply
cannot be drift-checked (Section 4a reports it `NO_ANCHOR`, a distinct,
non-error status — the same "unknown is honest" posture as
`anvil/lib/evidence_drift.py`'s `NO-SNAPSHOT`). The very next revise
pass that touches that row is expected to add its anchor; nothing forces
a bulk migration of an otherwise-untouched thread.

Drafter discipline:

- The drafter writes one row per attributed quote and per checkable
  factual claim (named dates, names, events, places).
- **Fabricating a source-line mapping is prohibited.** If no corpus
  passage supports a claim, the drafter does not invent a citation:
  either cut the claim or record it with a `NOT_FOUND` source note so
  the audit critic sees it explicitly.
- A **missing `provenance.md`** when the corpus tier is active is a
  **`major`** finding (a broken contract), **not a crash** — the
  reviewer surfaces it and drafting still proceeds.

## Section 3 — reviewer back-check contract

When the corpus tier is active and `provenance.md` exists, the reviewer
runs a **provenance back-check** as a sub-step of its pass:
**spot-sample 5–10 rows per review pass**, opening each cited file + line
range in the resolved corpus.

- Findings are `kind: judgment` findings with `evidence_span` pointing at
  the map row (`provenance.md:L<N>`).
- **A row whose cited file does not exist** (not resolvable under any
  corpus root) is a **`major`** finding.
- **A row whose cited passage does not support the claim as written** is
  a **`blocker`** finding.
- The reviewer quotes both the claim and the cited passage in the
  finding — the same load-bearing evidence discipline as the voice
  corpus-quote rule. Vague back-check feedback without a quoted passage
  is itself a defective finding.
- **When a sampled row has an `Anchor` value** (Section 2) and the text
  at the cited `Line range` does not read as expected, check whether the
  anchor text is present *elsewhere* in the file before concluding
  `MISMATCH`/`NOT_FOUND` — a mismatch between the passage AT the hinted
  line and an anchor found intact a few lines away is anchor drift
  (Section 4a), not a content defect. The back-check is a sampling check
  and MAY simply flag "hint looks stale, recommend a full audit" rather
  than manually re-locating every drifted row; the exhaustive
  drift-vs-content triage is the audit critic's job.

The back-check is a **sampling** check (cheap, every review pass); the
exhaustive verification is the audit critic's job (Section 4).

## Section 4 — audit-critic contract (`kind: tool_evidence`)

The corpus-provenance audit critic is a `kind: tool_evidence` critic
(the pattern already documented in `anvil/lib/snippets/audit.md`;
`Kind.TOOL_EVIDENCE` already exists in `anvil/lib/review_schema.py` and
the schema validator already enforces `tool_calls` on every
`tool_evidence` finding — **no schema change is needed**). It runs the
**exhaustive** pass the reviewer only samples:

1. **Inventory** every attributed quote and factual claim in the
   artifact, and every row in `provenance.md`. A claim in the artifact
   with **no `provenance.md` row is a finding in itself** (unmapped
   claim).
2. For **each** map row that has an `Anchor` value, run the **anchor-
   resolution pre-pass** (Section 4a) FIRST — it decides which line(s)
   to actually open before classification runs. For a row with no
   anchor (Section 2 "Backward compatibility"), skip straight to opening
   the cited `Line range` as-is, exactly as before issue #868.
3. Open the resolved passage (the anchor's actual current location when
   Section 4a found one; otherwise the cited `Line range`) in the
   resolved corpus and **classify** it with the five-way vocabulary
   (Section 5), then run the **scope-widening check** (Section 5a)
   against the same passage regardless of which five-way classification
   it received.
4. Every `MISMATCH` / `NOT_FOUND` / `FABRICATED` row, and every row that
   fails the Section 5a scope check, emits a finding with a non-empty
   **`tool_calls`** array recording the file-read operation that
   produced the evidence (the passage read, the lines inspected).
5. Fabrication-class entries — including a `scope_overreach` finding —
   additionally emit **`critical_flags`** (Section 6), which route
   through the existing verdict machinery
   (`anvil/lib/critics.py::_compute_verdict_impl` already short-circuits
   any `critical_flags` → `Verdict.BLOCK` — no change needed).

`kind: tool_evidence` with `findings == []` is valid — a corpus whose
every claim VERIFIED / PARAPHRASE_OK is a clean audit.

## Section 4a — anchor-drift detection (pre-classification pass, #868)

Before classifying a row against the five-way vocabulary, the audit
critic resolves its `Anchor` (when present) against the WHOLE cited
file — not just the hinted `Line range` — using
`python -m anvil.lib.provenance_anchor check <provenance.md>
<corpus_root> [<corpus_root> ...]` (prefix `uv run --project .anvil` in
an installed consumer repo). This is a deterministic, advisory pre-
check, the same posture as `anvil/lib/evidence_drift.py` (#857) and
`anvil/lib/probe_freshness.py` (#863) — it never mutates on-disk state
and its exit code is always `0`; the critic decides what to do with the
report.

Each row resolves to exactly one of:

- **`NO_ANCHOR`** — the row has no `Anchor` value (legacy row, or a
  `NOT_FOUND`-marked row with nothing to anchor). Classification proceeds
  against the cited `Line range` exactly as before #868. Never a defect.
- **`FILE_NOT_FOUND`** — `Source file` does not resolve under any
  declared corpus root. Feeds the existing "row whose cited file does
  not exist" finding path (Section 3's `major` precedent, applied at
  audit scope).
- **`NOT_FOUND`** — the anchor text is not present anywhere in the file
  (deleted or rewritten, not merely moved). This is **not** a drift
  finding — it degrades to the ordinary `NOT_FOUND` five-way
  classification (Section 5); the passage is simply gone.
- **`RESOLVED`** — the anchor text is present and its actual location
  overlaps the cited `Line range` hint (or the row has no parseable
  hint). When the cell cites several comma-separated ranges (#1204),
  overlapping **any one of them** is enough — no priority is given to
  the first-listed range. No drift; classification proceeds against the
  hinted range.
- **`DRIFTED`** — the anchor text is present **verbatim** elsewhere in
  the file, not overlapping any of the cited hint range(s). This is the
  signature case:
  **the citation is genuine, only its address is stale.** The critic:
  1. Emits a distinct `findings.md` row/finding — worded as **anchor
     drift**, e.g. *"provenance.md row N: quoted text still present in
     `<file>` but now at line `<X>` (row cites `<Y>`) — Line range hint
     is stale"* — never phrased as `MISMATCH` or `NOT_FOUND`, and never
     carrying a fabrication-class `critical_flags` entry. This is AC #2
     from issue #868: a drifted anchor must read differently from an
     unsupported claim to a human or a downstream reviser scanning
     `findings.md`.
  2. Then classifies the row against the vocabulary (Section 5) at the
     anchor's ACTUAL resolved location, not the stale hint — a drifted
     row whose relocated passage genuinely supports the claim is still
     `VERIFIED`/`PARAPHRASE_OK` (drift and content-support are
     orthogonal axes: a row can drift into staying `VERIFIED`, or drift
     and independently turn out to be `MISMATCH` if the passage was also
     edited in a way that changes its meaning).
  3. Severity for the anchor-drift finding itself is `minor` — the
     content classification (step 2) carries whatever severity the
     five-way vocabulary implies; drift alone, once caught, is fully
     mechanical to fix (Section 4b) and never a fabrication signal.

When multiple occurrences of the anchor text exist in the file
(coincidental duplication), the tool resolves to the occurrence nearest
the cited hint — the mechanism issue #868's edge case (b) requires: a
row whose anchor is genuinely un-drifted must not be misclassified as
drifted merely because its exact wording happens to recur elsewhere.

## Section 4b — mechanical repoint (reviser-side, #868)

A reviser consuming `DRIFTED` findings repoints them mechanically rather
than diagnosing each one by hand: `python -m anvil.lib.provenance_anchor
repoint <provenance.md> <corpus_root> [<corpus_root> ...]` rewrites ONLY
the `Line range` cell of every `DRIFTED` row to the anchor's resolved
current location — `Claim` / `Source file` / `Anchor` / `Notes`, and
every non-drifted row, are left byte-identical. This is explicitly **not**
the "fabricating a source-line mapping" failure the drafter/reviser
contract prohibits (Section 2): the anchor text itself already proves
the citation is genuine; repoint only corrects a stale hint to match
where that same, unchanged, verbatim evidence now lives. See each
skill's `-revise` command for exactly where this runs in its procedure.

## Section 5 — five-way classification vocabulary

The audit critic classifies each `provenance.md` row as exactly one of:

- **`VERIFIED`** — exact or near-exact textual match in the cited
  passage.
- **`PARAPHRASE_OK`** — the substance is present in the passage; the
  wording is clearly authorial paraphrase (legitimate reconstruction,
  not invention).
- **`MISMATCH`** — the passage exists but does not support the claim as
  written (e.g. a different year, a different person, a different place).
- **`NOT_FOUND`** — no matching passage found in the declared line range
  or the surrounding context.
- **`FABRICATED`** — the claim conflicts with the corpus, or the corpus
  explicitly contradicts it.

`VERIFIED` and `PARAPHRASE_OK` are passing classifications. `MISMATCH`
and `NOT_FOUND` are findings. `FABRICATED` is a finding **and** a
critical flag.

## Section 5a — the scope-widening check (issue #1032)

Content support and grammatical **scope** are independent axes. A
`provenance.md` row can genuinely support a claim's underlying fact and
the claim can still be wrong, because the artifact clause asserts
something *broader* than the row established. "Is this fact supported
at all?" (Section 5's five-way vocabulary) does not ask "*is the fact
supported at the scope the artifact claims it at?*" — this check does.

Run this check on every row, **in addition to** (not instead of) the
five-way classification, whenever the artifact clause contains any of:

- a **universal quantifier** — "anyone", "everyone", "every", "all",
  "always", "everywhere";
- a **superlative** — "first", "only", "most", "best", "biggest",
  "last";
- a **negated existential** — "no other X anywhere/exists", "nothing
  else", "nowhere else".

Compare the quantifier/superlative/negation's scope in the artifact
clause against the *same construct's scope* in the cited row's own
language (not the row's general subject matter — its actual
quantifying words):

- **Row scope matches or is wider than the claim's scope** → the
  quantifier/superlative/negation is supported as written; the
  five-way classification stands unchanged.
- **Row scope is narrower than the claim's scope** → raise
  `scope_overreach` (Section 6), **regardless of whether the
  underlying fact would otherwise classify `VERIFIED` or
  `PARAPHRASE_OK`.** A row that supports a narrower claim does not
  license a wider one — this is a finding, not a pass.

**Calibration examples** (field evidence, issue #1032 / #888):

| Artifact clause | Cited row | Verdict |
|---|---|---|
| "It is the only picture of the brothers **anyone has**" | "the first photograph of Gustav's parents **the project has**" | `scope_overreach` — "the project has" (this corpus) narrows to "anyone has" (all of humanity) |
| "the only thing **anyone in this family holds** that Ella wrote in her own hand" | "no other document written by Ella **anywhere in this repository**" | `scope_overreach` — "in this repository" narrows to "anyone in this family holds" |
| "the first photograph **the project has**" | "the first photograph of Gustav's parents **the project has**" | Not flagged — the claim quotes the row's own scope verbatim; row scope matches claim scope |

A row cited for "the first photograph the project has" against a row
that itself says "the project has" is correctly scoped — the check
fires only when the claim's scope-bearing language reaches *beyond*
what the row's own scope-bearing language covers, never merely because
a quantifier or superlative is present.

## Section 6 — fabrication-class critical flag types

These are the `CriticalFlag.type` strings the audit critic (and, at the
boundary, the reviewer) raises. They are **skill-defined vocabulary**
(the lib does not enforce a `CriticalFlag.type` enum); any one forces
`Verdict.BLOCK` regardless of rubric score:

- **`fabricated_quote`** — verbatim-quoted text that does not appear in
  the corpus.
- **`fabricated_fact`** — a named date, name, or event not traceable to
  any corpus passage.
- **`misattribution_of_substance`** — an event or memory attributed to a
  speaker whose corpus does not contain it. This is the **substance-level**
  flag; voice-level misattribution (right substance, wrong voice) belongs
  to #598.
- **`anachronism`** — an era-incompatible detail contradicted by the
  corpus chronology.
- **`unattributed_paraphrase`** — authorial invention presented as a
  subject's memory without any corpus grounding.
- **`scope_overreach`** (issue #1032) — a claim's universal quantifier
  ("anyone"/"every"/"all"), superlative ("first"/"only"/"most"), or
  negated existential ("no other X anywhere/exists") asserts wider
  scope than its cited `provenance.md` row supports, per the Section 5a
  scope-widening check — even when the row otherwise `VERIFIED`s or
  `PARAPHRASE_OK`s the underlying fact. `justification` MUST quote
  **both** the offending artifact clause and the cited row's own
  scope-bearing language (not just the row's subject matter), so the
  narrower-vs-wider mismatch is visible without re-deriving it — e.g.
  *"artifact: 'the only picture of the brothers anyone has'; row: 'the
  first photograph of Gustav's parents the project has' — row scope is
  'the project has', not 'anyone has'."*

Each flag's `justification` quotes the offending artifact text and the
corpus evidence (or its absence). The flag is *additive* — it uses the
existing critical-flag machinery, not a rubric-total change.

## Section 7 — `_progress.json` extension

The corpus-audit critic records a roll-up of its classification pass in
the `_progress.json` inside its sibling dir, under
`metadata.provenance_summary`:

```json
{
  "metadata": {
    "provenance_summary": {
      "total_claims": 42,
      "verified": 30,
      "paraphrase_ok": 8,
      "mismatch": 2,
      "not_found": 1,
      "fabricated": 1
    }
  }
}
```

The six counts sum to `total_claims`. The field is **omitted entirely**
when the corpus tier is inactive (no new `_progress.json` surface for
ungrounded projects — the byte-identical-when-absent posture).

## Section 8 — sibling dir naming

The corpus-provenance audit critic writes its sidecar to
`<thread>.{N}.corpus-audit/`, following the `version_layout.md` critic-tag
convention (`<thread>.{N}.<tag>/`, a single short token, no nested dots).
It is a normal critic sibling: immutable once written, discovered by the
`enumerate_siblings` machinery, and re-pointed by the
`<thread>.latest.corpus-audit` symlink family. It coexists with the
general `.audit/` sibling — the corpus audit is the substance-verification
specialist, not a replacement for the general audit pass.

## Section 9 — corpus-editing expectations for consumers (#868)

The corpus is a project-level, human-owned evidence base — consumers
hand-edit it between passes (correcting a transcription error, adding an
explanatory note, appending a newly-transcribed letter). Before the
`Anchor` column (Section 2), this required **line-count-neutral**
editing discipline to avoid silently invalidating every
`provenance.md` row citing text below the edit point: same-length
substitutions only, new material appended at EOF, never an insertion
mid-file. That discipline is no longer required to avoid *breakage* —
an anchor-bearing citation survives a line-shifting edit; the next
audit pass reports it `DRIFTED` (Section 4a) and the next revise pass
repoints it mechanically (Section 4b). It is still good practice for
*review noise*: an edit that shifts many rows produces many `DRIFTED`
findings for the next audit to work through, even though none of them
are defects.

What consumers should still know:

- **Editing the exact cited passage's wording** (not just its position)
  is a content change, not a position change — the audit critic still
  classifies the row against whatever text is now at the anchor's
  resolved location (Section 4a step 2), and a rewritten passage that no
  longer supports the claim correctly surfaces as `MISMATCH`, exactly as
  today.
- **Deleting the cited passage entirely** degrades to `NOT_FOUND`
  (Section 4a), not `DRIFTED` — the citation genuinely has nothing left
  to point at.
- **Editing while an audit is in flight** (mid-sweep) is not a supported
  concurrency mode for any part of this framework's filesystem-as-
  coordination-layer model — finish or defer a corpus edit until between
  passes, the same expectation as editing `BRIEF.md`/`refs/**` under a
  frozen version (`anvil/lib/evidence_drift.py`, issue #857).
- **Rows written before this feature** (no `Anchor` value) get none of
  this protection until an anchor is added — see Section 2 "Backward
  compatibility". A consumer who wants drift protection on an
  already-AUDITED thread's existing corpus does not need to force a
  revision: the next natural revise pass that touches a row is when its
  anchor gets populated.

## Relationship to `<thread>/refs/` and `cite.py`

This contract is deliberately separate from two existing surfaces:

- **`<thread>/refs/`** (issue #144) holds *per-thread* author-supplied
  PDFs for `paper-audit`. The top-level `corpus:` is a **project-level**
  read-only evidence base shared across all threads. The two coexist —
  `paper` keeps its per-thread `refs/`; corpus-aware skills get the
  project-level corpus.
- **`anvil/lib/cite.py`** is strictly *external* identifier resolution
  (DOI/arXiv → BibTeX). It knows nothing about local files or line-level
  citation maps. Claim provenance is local-corpus, line-range, and
  substance-verifying — an orthogonal concern.

## Relationship to #863 (perishable-claim freshness)

`anvil/lib/probe_freshness.py` (issue #863) and `anvil/lib/
provenance_anchor.py` (issue #868, this contract's Section 4a/4b) are
siblings that solve two different halves of "a verification that was
correct when written and is not correct now":

- **#863 is external.** The cited *evidence itself* is outside the
  repo's control (a URL, an HTTP status, a live dataset) and can change
  independently of anything the framework tracks. The fix is re-probing
  on a freshness budget — there is no way to make an external address
  permanently stable.
- **#868 (this module) is internal.** The cited evidence — a corpus
  file under a project-owned, version-controlled `corpus:` root — never
  changed; only its *line address* did, because the file it lives in
  was edited. The fix is a content-addressed anchor: once the anchor
  format exists, the citation cannot go stale from a line shift, only
  from an actual edit to the cited text (which correctly surfaces as a
  content classification change, not a drift finding).

Both are advisory, both are read-only over the artifact they check, and
neither is wired through `anvil/lib/convergence.py`'s `CriticalFlag`
machinery — see `anvil/lib/snippets/audit.md` §"Perishable vs durable
verifications" for the full #863 design and its shared advisory
posture.
