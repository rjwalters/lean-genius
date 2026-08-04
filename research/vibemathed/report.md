# VibeMathed discovery-feed exploration — report

Issue: #43622. Snapshot: `research/vibemathed/dataset-snapshot.json`, fetched
2026-08-03/04 from `GET https://vibemathed.com/api/dataset`
(`generated: 2026-08-04T05:14:59.644Z`, `count: 427`). Source:
[vibemathed.com](https://vibemathed.com/) ·
[github.com/mrconter1/vibemathed](https://github.com/mrconter1/vibemathed) ·
license **CC BY 4.0** (see `README.md` in this directory for attribution
mechanics).

**Scope note:** this is discovery/triage only. No `src/data/proofs/*/meta.json`
file has been modified as part of this issue. Every list below is framed as
candidates for a human or another agent (Mechanic/Researcher/Seeker) to
independently verify — not as conclusions.

Regenerate the numbers below at any time with:

```bash
curl -sS -o research/vibemathed/dataset-snapshot.json https://vibemathed.com/api/dataset
python3 research/vibemathed/join.py
```

## 1. Overlap size and mapping rate

Join key: VibeMathed's `problemNumber` field (for entries whose `slug`
starts with `erdos-`) against this repo's `src/data/proofs/erdos-<N>/meta.json`
**base** entries (the `-oq-*`/`-wip-*`/`-incomplete-*` variant slugs under
each `erdos-N` are sub-pages of the same problem, not separate join
targets). As the issue anticipated, this cannot be a straight slug join —
VibeMathed's slugs carry a descriptive suffix (e.g. their dataset would use
something like `erdos-131-non-dividing-sets` for problem 131) while ours are
bare `erdos-131` — so the join is numeric on `problemNumber`, not string
equality on `slug`.

| Metric | Value |
|---|---|
| VibeMathed dataset total entries | 427 |
| VibeMathed entries with `slug` starting `erdos-` **and** a numeric `problemNumber` | 136 (133 unique Erdős numbers — 3 numbers have two dataset entries) |
| VibeMathed entries mentioning Erdős in `posedBy` but with no numeric `problemNumber` (named slugs, e.g. `erdos-graham-unit-fraction-averages`, `erdos-lovasz-cover-number`) — **not** numerically joinable | 9 |
| This repo's `erdos-<N>` base gallery entries (distinct Erdős numbers covered) | 1195 |
| **Matched** (VibeMathed Erdős number has a gallery base entry) | **127 / 133 VibeMathed numbers (95.5%)** |
| VibeMathed Erdős numbers with **no** gallery counterpart | 6 (`1186`, `1188`, `1189`, `1190`, `1195`, `1197` — all in VibeMathed's high end, consistent with recent erdosproblems.com numbering our gallery hasn't ingested yet) |
| Gallery Erdős numbers **not** present in VibeMathed's Erdős-tagged set | 1068 / 1195 (89.4%) |

Two honest caveats on "mapping rate":
1. **Directionality matters.** From VibeMathed's side, our gallery already covers 95.5% of the Erdős problems they track — a strong signal our gallery is already the broader, denser Erdős corpus (1195 vs. 133 numbers). From our side, VibeMathed only overlaps 10.6% of our Erdős entries — expected, since VibeMathed's whole dataset (427 problems across all fields) is smaller than just our Erdős slice.
2. VibeMathed's dataset `count` field says 427 and 9 more entries credit "Erdős" in `posedBy` without a numeric `problemNumber` (their own dataset issue, not ours) — these 9 are listed but excluded from the numeric join; see `join-results.json` → `vmErdosPosedButUnnumbered`.

VibeMathed's `resolution` breakdown across the 136 Erdős-tagged entries:
`resolved` 78, `candidate` 35, `partial` 17, `variant` 4, `retracted` 2.
Their `verification` breakdown: `lean-verified` 82, `site-confirmed` 28,
`unreviewed` 21, `expert-verified` 3, `contested` 2.

## 2. VibeMathed `resolved` vs. our gallery still `open` — triage candidates

**Tier 1 (46 entries, highest confidence).** VibeMathed calls the problem
`resolved`, and our own `meta.erdosProblemStatus` field — the field this
repo already uses specifically to track whether the *underlying Erdős
problem* is open — still reads `open` (or is unset). This is the most direct
match for the issue's "our gallery still says open" checklist item.

**These are candidates for triage, not confirmed drift.** A gallery entry
showing `erdosProblemStatus: open` may be correct and VibeMathed premature
or wrong (`verification: unreviewed`/`site-confirmed` is not independently
vetted — see caveats in the original issue and Axiom Integrity Policy);
or the gallery field may be stale even though a *variant/OQ sub-page* of the
same problem was already closed elsewhere. Concretely: `erdos-1092` appears
below with `erdosProblemStatus: open`, but this repo's own history shows
`erdos-1092-oq-02` (a sub-question of the same problem) was already closed
as resolved in PR #43572 — the base entry's field was evidently never
updated to reflect that. That is exactly the kind of stale-field case this
list is meant to surface; each row needs its own check, not a blanket flip.

| Erdős # | Gallery slug | Gallery status | Gallery erdosProblemStatus | VM verification | VM solve date | Source |
|---|---|---|---|---|---|---|
| 38 | `erdos-38` | axiomatized | open | lean-verified | 2026-04-25 | https://www.erdosproblems.com/38 |
| 42 | `erdos-42` | axiomatized | open | lean-verified | 2026-04-27 | https://www.erdosproblems.com/42 |
| 43 | `erdos-43` | axiomatized | open | site-confirmed | 2026-04-27 | https://www.erdosproblems.com/43 |
| 90 | `erdos-90` | axiomatized | open | expert-verified | 2026-05 | https://arxiv.org/abs/2605.20695 |
| 119 | `erdos-119` | axiomatized | open | site-confirmed | 2026-07 | https://www.erdosproblems.com/119 |
| 123 | `erdos-123` | axiomatized | open | lean-verified | 2026-07 | https://www.erdosproblems.com/123 |
| 125 | `erdos-125` | verified | open | lean-verified | 2026-03-30 | https://www.erdosproblems.com/125 |
| 138 | `erdos-138` | axiomatized | open | lean-verified | 2026-05-21 | https://www.erdosproblems.com/138 |
| 202 | `erdos-202` | formalized | open | lean-verified | 2026-04-23 | https://www.erdosproblems.com/202 |
| 320 | `erdos-320` | axiomatized | open | site-confirmed | 2026-07 | https://www.erdosproblems.com/320 |
| 321 | `erdos-321` | axiomatized | (unset) | site-confirmed | 2026-07 | https://www.erdosproblems.com/321 |
| 330 | `erdos-330` | axiomatized | (unset) | lean-verified | 2026-04-24 | https://www.erdosproblems.com/330 |
| 351 | `erdos-351` | open | open | lean-verified | 2026-05-03 | https://www.erdosproblems.com/351 |
| 369 | `erdos-369` | axiomatized | open | lean-verified | 2026-03-26 | https://www.erdosproblems.com/369 |
| 380 | `erdos-380` | axiomatized | open | site-confirmed | 2026-03-31 | https://www.erdosproblems.com/380 |
| 457 | `erdos-457` | axiomatized | open | lean-verified | 2026-03-02 | https://www.erdosproblems.com/457 |
| 469 | `erdos-469` | verified | (unset) | lean-verified | 2026-07-21 | https://www.erdosproblems.com/469 |
| 539 | `erdos-539` | axiomatized | open | lean-verified | 2026-06-10 | https://www.erdosproblems.com/539 |
| 593 | `erdos-593` | axiomatized | open | unreviewed | 2026-06-23 | https://arxiv.org/abs/2606.24882 |
| 603 | `erdos-603` | axiomatized | open | site-confirmed | 2026-04-21 | https://www.erdosproblems.com/603 |
| 610 | `erdos-610` | axiomatized | open | lean-verified | 2026-04-21 | https://www.erdosproblems.com/610 |
| 619 | `erdos-619` | axiomatized | open | lean-verified | 2026-06-09 | https://www.erdosproblems.com/619 |
| 650 | `erdos-650` | axiomatized | open | lean-verified | 2026-03-07 | https://www.erdosproblems.com/650 |
| 690 | `erdos-690` | axiomatized | open | site-confirmed | 2026-05-08 | https://www.erdosproblems.com/690 |
| 694 | `erdos-694` | axiomatized | open | lean-verified | 2026-05-01 | https://www.erdosproblems.com/694 |
| 696 | `erdos-696` | axiomatized | open | lean-verified | 2026-06-05 | https://www.erdosproblems.com/696 |
| 741 | `erdos-741` | verified | open | lean-verified | 2026-04-16 | https://www.erdosproblems.com/741 |
| 750 | `erdos-750` | axiomatized | open | lean-verified | 2026-05-03 | https://www.erdosproblems.com/750 |
| 768 | `erdos-768` | axiomatized | open | unreviewed | 2026-06-23 | https://arxiv.org/abs/2606.24872 |
| 793 | `erdos-793` | axiomatized | open | site-confirmed | 2026-07 | https://www.erdosproblems.com/793 |
| 851 | `erdos-851` | axiomatized | open | site-confirmed | 2026-02-05 | https://www.erdosproblems.com/851 |
| 863 | `erdos-863` | verified | open | site-confirmed | 2026-04-22 | https://www.erdosproblems.com/863 |
| 865 | `erdos-865` | axiomatized | open | lean-verified | 2026-06-22 | https://www.erdosproblems.com/865 |
| 888 | `erdos-888` | axiomatized | open | site-confirmed | 2026-04-25 | https://www.erdosproblems.com/888 |
| 896 | `erdos-896` | axiomatized | open | site-confirmed | 2026-04-26 | https://www.erdosproblems.com/896 |
| 897 | `erdos-897` | axiomatized | open | lean-verified | 2025-12-26 | https://www.erdosproblems.com/897 |
| 948 | `erdos-948` | axiomatized | open | site-confirmed | 2026-06-21 | https://www.erdosproblems.com/948 |
| 997 | `erdos-997` | axiomatized | open | lean-verified | 2026-03-31 | https://www.erdosproblems.com/997 |
| 1014 | `erdos-1014` | axiomatized | open | lean-verified | 2026-04-23 | https://www.erdosproblems.com/1014 |
| 1039 | `erdos-1039` | axiomatized | open | lean-verified | 2026-05-17 | https://www.erdosproblems.com/1039 |
| 1051 | `erdos-1051` | axiomatized | open | lean-verified | 2026-01-29 | https://www.erdosproblems.com/1051 |
| 1061 | `erdos-1061` | axiomatized | open | unreviewed | 2026-06-24 | https://arxiv.org/abs/2606.25849 |
| 1089 | `erdos-1089` | axiomatized | open | site-confirmed | 2026-02-01 | https://www.erdosproblems.com/1089 |
| 1092 | `erdos-1092` | axiomatized | open | site-confirmed | 2026-04-28 | https://www.erdosproblems.com/1092 |
| 1138 | `erdos-1138` | axiomatized | open | lean-verified | 2026-04-25 | https://www.erdosproblems.com/1138 |
| 1148 | `erdos-1148` | axiomatized | open | lean-verified | 2026-03-16 | https://www.erdosproblems.com/1148 |

Full machine-readable rows (with `resultNote`, `solveType`, etc.) are in
`join-results.json` → `resolvedButGalleryOpen`.

**Suggested triage order**: prioritize the 25 rows with
`verification: lean-verified` (strongest external claim) whose gallery
`status` is `axiomatized` rather than `open`/`formalized` (i.e. we already
have *some* Lean formalization for the problem, which lowers the cost of
checking whether it now closes the open conjecture vs. bounding it).

**Tier 2 (27 entries, context only — do NOT read as drift).** VibeMathed
says `resolved`, and our gallery's `erdosProblemStatus` **already agrees**
(reads `solved`/`proved`/`disproved`/`partially-solved`), but our
formalization `status` is still `axiomatized`. Per this repo's Axiom
Integrity Policy, `axiomatized` is the expected status for many
legitimately-resolved entries (assumption-carrying proofs, undischarged
`native_decide`, or results we haven't independently re-verified against a
primary source) — this is not a status disagreement with VibeMathed at all,
just a note that our formalization of an already-agreed-resolved problem
still carries an assumption. Full list (erdos numbers) in
`join-results.json` → `resolvedGalleryAgreesButAxiomatized`:
`205, 258, 281, 283, 333, 347, 397, 401, 543, 659, 728, 729, 848, 858, 871,
960, 966, 986, 987, 990, 1026, 1091, 1141, 1153, 1196, 1202, 1217`.

## 3. VibeMathed `partial`/`candidate` with no gallery counterpart — Seeker candidates

Only **3** VibeMathed Erdős entries are both (a) `partial` or `candidate`
resolution and (b) have no matching `erdos-<N>` base entry in our gallery at
all (all three are recent, high-numbered erdosproblems.com entries our
gallery hasn't ingested yet):

| Erdős # | VM resolution | VM verification | Solve date | Source |
|---|---|---|---|---|
| 1186 | partial | unreviewed | 2026-07-13 | https://www.erdosproblems.com/1186 |
| 1188 | candidate | lean-verified | 2026-07-13 | https://www.erdosproblems.com/1188 |
| 1189 | partial | lean-verified | 2026-07-13 | https://www.erdosproblems.com/1189 |

These are reasonable Seeker research-queue candidates: recent, checkable
against a primary source (`erdosproblems.com`), and not yet represented in
our gallery at all. (Three more VibeMathed-only numbers — 1190, 1195, 1197 —
are `resolved` rather than `partial`/`candidate`, so they're new-entry
candidates for the gallery rather than open-research candidates; listed for
completeness in `join-results.json`.)

This is a **small yield** relative to the issue's original framing
("58 `partial` + 47 `candidate` entries [across the whole 427-problem
dataset] are exactly the shape the Seeker wants") — most of VibeMathed's
`partial`/`candidate` pool is non-Erdős (other fields: number theory,
combinatorics, geometry, etc. outside the `erdos-*` gallery slug space) or
duplicates problems we already track. If Seeker intake from VibeMathed is
adopted (see §4), it should not be scoped to Erdős-only — the non-Erdős
`partial`/`candidate` entries (which this report doesn't enumerate, since
they fall outside this repo's `erdos-*` join key) are a larger and untapped
pool.

## 4. Recommendations (judgment calls)

### 4a. Ingestion mode: one-off report vs. scheduled fetch

**Recommendation: start as a one-off, cached snapshot (this PR) — do not
wire up a recurring job yet.** Reasons:

- The Tier-1 list above (46 candidates) already exceeds what a single triage
  pass can responsibly verify; a recurring fetch would pile up more
  candidates before the backlog is worked down, with no consumer ready to
  act on them.
- VibeMathed's own `resolution: retracted`/`contested` entries (2 each in
  this snapshot) confirm the feed **self-corrects** — a naive append-only
  ingestion would need re-sync logic from day one, not just a fetch cron.
  That's real design work (dedup by `slug`, handle retraction, re-run the
  numeric join against a repo that has also moved since the last sync) that
  shouldn't be built speculatively before the one-off report proves useful.
- The dataset is small (~784 KB) and cheap to refetch on demand
  (`curl ... && python3 research/vibemathed/join.py`, both committed here),
  so there's no efficiency reason to pre-schedule it.

**If** a recurring job is wanted later, the natural home is a **Scout**
step (per CLAUDE.md's agent table, Scout already "surveys gallery proofs,
techniques, and literature" on-demand) or a periodic Guide/Curator check,
re-running `join.py` against a fresh snapshot and filing/updating a
tracking issue with the diff — not silently mutating gallery `meta.json`,
consistent with the Axiom Integrity Policy's "when in doubt, axiomatized"
stance on unverified external claims.

### 4b. Attribution mechanics

**Recommendation:** the attribution note in `research/vibemathed/README.md`
(citing vibemathed.com, the GitHub source, and CC BY 4.0) is sufficient for
the snapshot/join artifacts committed here, since no VibeMathed field is
copied verbatim into any gallery-facing file in this PR. **If a future PR
copies VibeMathed text** (e.g. a `resultNote` or `verificationNote` string)
into a gallery `meta.json`/annotation or the public website, that specific
file should carry its own inline attribution (e.g. a `source: "VibeMathed
(CC BY 4.0), https://vibemathed.com/erdos-N"` field or an annotation
footnote) at the point of use — a repo-wide README is not enough once the
data appears on the live site, since CC BY 4.0 attribution should travel
with the reused content, not just live in a research/ subdirectory a site
visitor never sees.

### 4c. Contribute back

**Recommendation: yes, worth pursuing as a separate, later issue — not in
scope here.** This repo holds 130+ Lean-verified proofs (per repo status)
and VibeMathed has a `/submit` flow; several of our `verified`/`axiomatized`
Erdős entries with strong Lean formalizations are plausible submissions
once their formalization is stable. This report doesn't attempt that
submission — it requires per-entry judgment (which of our 1195 Erdős
entries meet VibeMathed's own bar) that's out of scope for a discovery
report, and touches an external site's contribution flow with rate limits
and review latency this exploration can't characterize. Suggest filing a
narrower follow-up issue (e.g. "submit our N strongest Lean-verified Erdős
proofs to VibeMathed") if this is wanted.

## Appendix: files in this directory

- `dataset-snapshot.json` — raw fetch, 427 entries, CC BY 4.0 (VibeMathed).
- `join.py` — the join script (re-runnable, read-only against the gallery).
- `join-results.json` — full machine-readable join output (regenerate via
  `join.py`; this is what the tables above are drawn from).
- `README.md` — attribution note and directory index.
