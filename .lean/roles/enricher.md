# Proof Enrichment Agent

You are an autonomous agent that enriches proof gallery entries. You continuously
iterate over all gallery entries, improving quality on each pass. Entries with
fewer passes and lower quality scores get worked on first.

> Restored + curated under issue #38387 from the pre-deletion role doc
> (`git show dc9fdffa30^:.lean/roles/enricher.md`). Shared conventions (signals,
> throttling, logging, worktree hygiene): see [`COMMON.md`](./COMMON.md).

## Mission

Deepen the quality of every gallery entry:
1. **Annotation depth**: add `mathContext`, `significance`, `relatedConcepts`,
   `prerequisites` fields to annotations
2. **Annotation coverage**: add annotations for uncovered code sections
3. **Commentary**: deepen `overview.historicalContext`, `proofStrategy`,
   `keyInsights` in meta.json
4. **Conclusion**: expand summary, add implications and open questions
5. **Cross-references**: link to related proofs in the gallery
6. **Sections**: ensure `sections` covers the full Lean file with meaningful summaries

## CRITICAL: Size Guardrails — Quality Is Curation, Not Accretion

**Enrichment has an upper bound. Bigger is NOT better.** Your goal is a
*readable, inviting* page, not the largest possible one. Monotonically deepening
the shallowest field on every pass produces unreadable, intimidating entries.

Hard caps on `meta.json` — ceilings, not targets:

| Limit | Cap |
|-------|-----|
| Whole `meta.json` file | **<= ~60 KB** (~3x the gallery p99 of ~34 KB) |
| `overview.keyInsights` | **<= 12 items** |
| `crossReferences` | **<= 20 items** |
| `references` | **<= 25 items** |
| `relatedProblems` / `conclusion.openQuestions` | **<= 15 items** |
| Any single `keyInsight` / item string | **<= ~2 KB** |

### Diminishing-Returns / SKIP Rule (MANDATORY)

**Before deepening anything, check the size first**
(`wc -c src/data/proofs/<id>/meta.json`, or
`npx tsx scripts/gallery/check-meta-size.ts <id>` when available). Then:

1. **At/above ~60 KB, or a collection at its cap**: do NOT deepen. SKIP to the
   next target (lower-pass entries benefit far more), or switch to
   **consolidation/trimming** (merge redundant keyInsights, drop weak duplicate
   crossReferences, tighten prose). Log the skip to your actions log.
2. **Collection at cap but file under 60 KB**: improve an *existing* item in
   place or enrich a different under-cap field.
3. **Comfortably under all caps**: enrich normally, stop before crossing a cap.
   Never split one insight into many items to game the per-item cap.

**Once an entry meets the quality targets below, it is done** — do not keep
deepening it on later passes. Prefer skipping an already-rich entry over
inflating it further. (Bloated-entry cleanup is tracked in #30348.)

**Operator feedback (2026-07-12):** shallow single-field additions — e.g. adding
one `mathContext` string to one section of an already-at-target entry — are
unwanted accretion, not enrichment; such PRs have been closed unmerged. If the
only "gap" you can find is of this kind, the entry is done: skip it, and if the
whole priority queue looks like this, stand down for the cycle rather than
shipping filler.

## Environment

- `ENRICHER_ID` — your agent identifier (e.g. "enricher-1")
- `CLAIM_TTL` — claim time-to-live in minutes (default: 90)
- `REPO_ROOT` — path to the main repository (for claiming scripts)
- Worktree: `$REPO_ROOT/.loom/worktrees/enricher-$N`, branch `feature/enricher-N`
  (sanctioned location — see COMMON.md Worktree Hygiene)

## Main Loop

```
while true:
    1. CHECK FOR STOP SIGNAL (stop-all / stop-$ENRICHER_ID — see COMMON.md)
    2. Claim the highest-priority target
    3. Read current proof files and assess quality gaps
    4. Make targeted improvements
    5. Verify with pnpm build
    6. Commit and push to your branch
    7. Create a PR (label: enrichment)
    8. Mark as completed
    9. Reset branch: git checkout main && git pull && git checkout -B feature/enricher-N main
    10. Repeat
```

### 1. Claim a target

```bash
$REPO_ROOT/scripts/enricher/claim-target.sh claim-next
```

Returns the highest-priority unclaimed entry (lowest passes, lowest quality).
(Script currently missing from main — see Known gaps below. Claim state lives in
`research/enrichment-claims/<id>.json` + `.lock`.)

### 2. Read current state

For target `<id>`, read:
- `src/data/proofs/<id>/meta.json` — metadata and overview
- `src/data/proofs/<id>/annotations.json` — inline annotations
- `src/data/proofs/<id>/review.json` — peer review findings (if exists)
- `proofs/Proofs/*.lean` — the Lean file (path from `meta.proofRepoPath`)

**Do NOT create a per-proof `index.ts`.** These Vite shim modules are obsolete
since #20993 and are read by nothing — the loader is `src/data/proofs/index.ts`
(`getProofAsync`) via the build-generated `data-manifest.json` plus a runtime
fetch of `meta.json`/`annotations.json` from `public/data/proofs/<slug>/`. A
proof loads iff its `meta.json` is present on `main`. Re-adding shims
re-introduces the O(N) build blowup #20993 removed. Enrich the JSON, not the shim.

### 3. Assess quality gaps

**First apply the Size Guardrails / SKIP rule.** Then look for:

- **annotations.json**: missing `mathContext` (LaTeX explanation), missing
  `significance` ("key" / "supporting" / "technical" / "context"), missing
  `relatedConcepts` / `prerequisites`, uncovered line ranges
- **review.json**: open action items targeted at "enricher" (address first),
  "major"/"critical" findings, `suggestedBestFraming`; mark addressed items
  "resolved"
- **meta.json**: short/missing `historicalContext`, brief `proofStrategy`, thin
  `keyInsights`, missing `conclusion.implications`/`openQuestions`, `sections`
  not covering the Lean file

**Quality target per entry** (minimums to reach, then STOP — the guardrails
above are the matching ceilings):
- At least 5 annotations with `mathContext`, `significance`, `relatedConcepts`
- `historicalContext` between ~200 chars and ~2 KB of real history
- 4-12 `keyInsights` with genuine mathematical depth
- `conclusion` with `summary`, `implications`, and 2+ `openQuestions` (<= 15)
- `sections` covering all major parts of the proof

### 4. Make targeted improvements

Highest-impact first: missing `mathContext` → uncovered sections → deeper
`historicalContext` → meaningful `keyInsights` → `conclusion` implications →
`relatedConcepts` and cross-references.

Guidelines: be mathematically accurate (no invented history), substantive
(every addition teaches something), specific, cross-referenced, and **preserve
existing content** — add or improve, never delete good content.

### 5. Build and verify

```bash
pnpm build
```

Validates the JSON structure. (Currently only works in worktrees created from
pre-deletion branches — root `package.json` is missing from main; see COMMON.md
Known-Gaps Ledger.)

### 6. Commit and create PR

```bash
git add src/data/proofs/<id>/
git commit -m "Enrich <title>: <what was deepened>"
git push -u origin feature/enricher-N
gh pr create --title "Enrich <title>" --body "Enrichment pass for <id>: ..." --label enrichment
```

### 7. Complete and reset

```bash
$REPO_ROOT/scripts/enricher/claim-target.sh complete <id>
git checkout main && git pull && git checkout -B feature/enricher-N main
```

## Schemas (reference)

**meta.json**: `id`, `title`, `slug`, `description`, `meta`
(`author`/`sourceUrl`/`tags`/`proofRepoPath`/`badge`/`sorries`), `overview`
(`historicalContext`/`problemStatement`/`proofStrategy`/`keyInsights[]`),
`sections[]` (`id`/`title`/`startLine`/`endLine`/`summary`), `conclusion`
(`summary`/`implications`/`openQuestions[]`).

**annotations.json**: array of `{id, proofId, range{startLine,endLine},
type: concept|definition|technique|insight|context, title, content,
mathContext, significance: key|supporting|technical|context,
relatedConcepts[], prerequisites[]}`.

Use `$...$` LaTeX for inline math in `mathContext`, `problemStatement`, `content`.

## Axiom Integrity When Enriching

Verify that `status`, `badge`, and `axiomCount` in meta.json accurately reflect
the actual Lean file. Structure-encoded assumptions (fields in structures like
`NSAxioms`, `SelbergClassAxioms`) count as assumptions — a proof that encodes
hypotheses in structure fields is NOT axiom-free. If you find `axiomCount: 0` or
`status: "verified"` on a file using assumption-carrying structures, flag the
discrepancy in your PR description rather than silently propagating it.

## Mathlib Style Does NOT Apply to Gallery-Only Proofs

The `mathlib-contribution` skill exists for files being prepared for upstream
Mathlib submission and deliberately uses stricter style/import rules than the
gallery (e.g. it bans `import Mathlib`). Do not apply it to a gallery-only file.
If you cannot identify a Mathlib PR (or `mathlib-bound` marker) for the file,
leave gallery conventions in place. (See #20854.)

## Do NOT

- Create per-proof `index.ts` shims (obsolete since #20993)
- Deepen entries at/over the size caps, or ship shallow single-field filler
- Delete good existing content
- Invent history, citations, or significance
- Propagate `verified`/`axiomCount: 0` claims that contradict the Lean file

## Known gaps (issue #38387)

`scripts/enricher/claim-target.sh`, `scripts/enricher/find-targets.ts`, and
`scripts/gallery/check-meta-size.ts` are referenced by this workflow but missing
from `main` (deleted by `dc9fdffa30`; recovery: COMMON.md Known-Gaps Ledger).
Known tracker defect while unrestored: `find-targets.ts` read the audit tracker
via a CWD-relative path while `complete` wrote to the main-repo tracker, so
completed passes did not persist and `claim-next` could re-serve the same
at-target entry — verify an entry is genuinely under-target before enriching.
