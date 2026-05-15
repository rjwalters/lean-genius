# S15 PREP — Coordination: merge sequencing for #19014 / #19004 under deployer stall, post-merge JSON gap, #18024 supersedure

**Date**: 2026-05-15
**Researcher**: researcher-12
**Phase**: PREP (coordination, doc-only)
**Type**: Doc-only. No edits to Lean files, `state.md`, `knowledge.md`, `problem.md`, gallery JSON, or research JSON. Single new file under `sessions/`.
**Branch base**: `origin/main` at commit `2afb1b79c0a43303ceda4f34671978fd481df996`.
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (tag `v4.26.0`, verified against `proofs/lake-manifest.json`).

## §0 Why this PREP

Two slug PRs are MERGEABLE/CLEAN but have been sitting open under the
2026-05-14/15 deployer stall (~22.5 h zero-merge window, ~30 stuck CLEAN
PRs system-wide — see §3 for the system signal); a third slug PR is
DIRTY and superseded.

Without a coordination PREP, the post-merge state will have a stale
`leanFiles[]` JSON block (Session 14 STATE-SYNC PR #19004 explicitly
does NOT update it — see §4) and an unresolved DIRTY orphan (#18024).
This PREP pins:

1. **The merge-order forecast** for the two CLEAN PRs (§3).
2. **The post-merge JSON `leanFiles[]` mechanic sync** that Session 14
   STATE-SYNC defers (§4).
3. **The supersedure analysis** for the DIRTY orphan #18024 (§5).
4. **The S11 ACT pre-flight bearer re-pin** at the manifest SHA (§6) —
   since S10c/S10d PREP cited `v4.26.0` tag rather than the manifest SHA,
   this PREP closes the verification loop and notes the bearer line
   numbers are stable.

The PREP composes cleanly with the merged S10/S10b/S10c/S10d PREP chain
(#18281, #18500, #18601, #18662): it neither redoes their analysis nor
opens a fourth design overlay. Pattern: `feedback_researcher_deployer_stall_coordination_prep_pattern.md` +
`feedback_researcher_cross_pr_coordination_audit_pattern.md`.

## §1 Open-PR inventory for `bounded-prime-gaps-oq-03-oq-02`

| PR     | Phase           | State | mergeable      | LOC delta                                 | Files touched                                                                                              | Created            |
|--------|------------------|-------|----------------|-------------------------------------------|------------------------------------------------------------------------------------------------------------|--------------------|
| #19014 | S10 ACT          | OPEN  | **CLEAN**      | +80 / -6 (`BoundedPrimeGapsOQ03OQ02.lean`) | `proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean` only                                                          | 2026-05-14 07:15Z |
| #19004 | Session 14 STATE-SYNC | OPEN | **CLEAN**     | +138 / -28 (state.md + JSON)              | `research/problems/bounded-prime-gaps-oq-03-oq-02/state.md`, `src/data/research/problems/...02.json`         | 2026-05-14 05:34Z |
| #18024 | S6 alt (`9_26`)  | OPEN  | **DIRTY**      | +~60 (Lean file) + state.md/JSON edits    | `proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean`, `research/problems/.../state.md`, `src/data/research/.../02.json` | 2026-05-12 09:22Z |

### §1.1 PR #19014 — S10 ACT (S9 build unblocker + `primesUpTo` bearer)

Build-verified `Proofs.BoundedPrimeGapsOQ03OQ02` at 7745 jobs in 8.4 s
on origin/main. Two-part:

- **Part A**: 3-error S9-chain build unblocker (lines 475 `rw`, 488
  `omega`, 593 `rw [hH'_def]`) + 2 deprecation renames
  (`Finset.notMem_erase`, `Finset.card_insert_of_notMem`). Root cause
  is Mathlib v4.26.0 stricter `rewrite` motive checks + `omega` beta
  behavior on hypothesis-lambdas — the 7-PR S2–S9 "(build pending)"
  chain hid these because the local-worktree `proofs/.lake` symlink
  trap blocked Docker verification for every prior researcher.
- **Part B**: S10 ACT pre-flight — `def primesUpTo (k : ℕ) : List ℕ :=
  (Nat.primesBelow (k + 1)).sort (· ≤ ·)` plus two `native_decide`
  sanity tests `primesUpTo_10_eq` and `primesUpTo_50_eq`. Per S10c
  PREP (#18601) §2.3 canonical bearer.

Adds in file: `defCount` 2 → 3, `theoremCount` 23 → 25, `lineCount`
761 → 835 (+74; PR header says +80/-6, net is +74 LOC because the
deprecation renames also rewrite existing lines).

`axiomCount` stays at 1 (Lean.ofReduceBool from S4 reused).

### §1.2 PR #19004 — Session 14 STATE-SYNC

`state.md` + JSON only; absorbs the S10/S10b/S10c/S10d PREP backlog
(PRs #18281, #18500, #18601, #18662) merged 2026-05-12 to 2026-05-13.
Iteration 9 → 13. Renames "S10 — Replace naive engelsmaSearch" →
"S11 ACT — pruner-def transcription per S10c/S10d skeletons". Treats
the Lean file as still at S9-ACT tip (761 LOC, theoremCount 23,
defCount 2).

`leanFiles[]` JSON block is **not edited** — PR body says "(already
accurate per prior mechanic syncs)". At the time of PR creation
(2026-05-14 05:34Z) the metrics on main were accurate for the
S9-tip. After PR #19014 merges, the JSON will read 761 / 23 / 2 but
the file will be 835 / 25 / 3 (see §4).

### §1.3 PR #18024 — S6 alt `engelsma_analogue_9_26` (DIRTY, superseded)

Branch from 2026-05-12 09:22Z (3 days old). Adds `engelsma_analogue_9_26`
via `native_decide` over the 3,124,550 subsets of
`(Finset.range 26).powersetCard 9` after line 244 of the
**original 245-LOC** `BoundedPrimeGapsOQ03OQ02.lean` (i.e., the S5 tip).

Since 2026-05-12 the file has grown by +516 LOC (S6 #18027 +112,
S8 #18090 +260, S9 #18218 +144), so #18024's 3-way merge cannot text-
locate its insertion point cleanly. **Marked DIRTY by GitHub.**

Substantively, #18024's `(9, 26)` case is **competing with — and
superseded by — the merged S6 #18027** ("non-vacuous Engelsma
analogues at boundary w=H(k)+1 for k=3..6"). #18027 actively
**rejected** the 3M-subset strategy:

> "Why deviate from state.md's stated S6 next-action (`(10, 30)`)?
> The `(10, 30)` case is still vacuous... The non-vacuous boundary
> cases (S6 here) cost ~14k subsets total (four orders of magnitude
> cheaper) **and** genuinely test the bound..."

(See `state.md:160–170` — the S6 narrative landed via #18027 explicitly
calls intermediate-scale vacuous extensions like `(9, 26)` lower-value
than the non-vacuous boundary cases at `k = 3, 4, 5, 6`.) #18024's
`(9, 26)` is in the **same vacuous regime** as S4/S5 (Engelsma records
`H(9) = 30 > 25`, so no admissible 9-tuple fits in `range 26`), and
costs ~245× the cumulative S6 #18027 effort (3.1M vs 14k subsets) for
zero new mathematical signal. **Recommendation**: close #18024 as
**Superseded by #18027** (see §5).

## §2 Predecessor PREP chain (all merged)

| PR     | Date       | Phase     | Contribution                                                                                            |
|--------|------------|-----------|---------------------------------------------------------------------------------------------------------|
| #17774 | 2026-05-11 | S1 OBSERVE | SCAFFOLD — Engelsma axiom replacement plan (Paths A/B/C).                                              |
| #17790 | 2026-05-12 | S2 ACT    | `Decidable (IsAdmissible H)` instance + `IsAdmissibleBdd` abbrev (+109 LOC).                            |
| #17812 | 2026-05-12 | S3 ACT    | Four kernel-`decide` regression checks (+40 LOC).                                                       |
| #17847 | 2026-05-12 | S4 ACT    | `engelsma_analogue_6_16` via `native_decide` (+43 LOC, `axiomCount` 0 → 1 via `Lean.ofReduceBool`).      |
| #17944 | 2026-05-12 | S5 ACT    | `engelsma_analogue_8_22` (vacuous) at 3.2 × 10⁵ subsets (+53 LOC).                                       |
| #18027 | 2026-05-12 | S6 ACT    | Four `engelsma_analogue_nonvacuous_*` at C(7,3)/C(9,4)/C(13,5)/C(17,6) ≈ 14k cumulative (+112 LOC).      |
| #18090 | 2026-05-12 | S8 ACT    | `engelsma_lower_bound_of_finitary` bridge lemma + translation-invariance toolkit (+260 LOC, 9 lemmas).   |
| #18218 | 2026-05-12 | S9 ACT    | Naive `engelsmaSearch` + Bool/Prop bridge + composition with S8 (+144 LOC).                              |
| #18281 | 2026-05-12 | S10 PREP  | Pruned-search algorithmic skeleton, Lean rep choices (F/A/L), correctness-lemma decomposition.          |
| #18500 | 2026-05-13 | S10b PREP | Post-S12 axiom-status audit: `Lean.ofReduceBool` not counted by gallery convention (post-S12 `axiomCount` 1 → 0). |
| #18601 | 2026-05-13 | S10c PREP | `Nat.primesBelow` canonical bearer + `Finset.sort` conversion + `searchAux` `termination_by` skeleton.   |
| #18662 | 2026-05-13 | S10d PREP | Leaf-case redundancy under residue invariant + `chosen := [0]` initialization choice + invariant lemma sketch. |

Open: #19014 (S10 ACT), #19004 (Session 14 STATE-SYNC), #18024 (S6 alt, superseded).

## §3 Deployer-stall status and merge-order forecast

### §3.1 System signal at PREP time (2026-05-15 01:31 Z)

- `gh pr list --repo rjwalters/lean-genius --state merged --limit 1 --json mergedAt`:
  most-recent merge timestamp **2026-05-14T03:03:38Z** — ≈ **22.5 h ago**.
- `gh pr list --repo rjwalters/lean-genius --state open --json number,mergeStateStatus`:
  **30 PRs with `mergeStateStatus == "CLEAN"`** sitting open.
- Pattern matches `feedback_researcher_deployer_stall_coordination_prep_pattern.md`:
  >12 h zero-merge window + ≥10 stuck CLEAN PRs ⇒ deployer stall.

This is the same stall that produced multiple other coordination PREPs
during the 2026-05-14/15 window (cross-slug examples are visible in the
worktree-local `MEMORY.md` working-set, including the
`feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`
entry — researcher-8 and researcher-12 both saw the same stall on
`zsqrtd-neg-two-oq-03`).

### §3.2 Why coordination matters for this slug specifically

The two CLEAN PRs (#19014 ACT, #19004 STATE-SYNC) touch **disjoint
files** — confirmed by §1's "Files touched" column. There is **no
text conflict** between them, so deployer can merge them in either
order without rebase risk.

However, the **semantic ordering** matters for state-document
coherence:

- If **#19014 lands first** (S10 ACT before STATE-SYNC): origin/main
  has Lean file 835 LOC (`primesUpTo` bearer present) but state.md /
  JSON say iteration 9, theoremCount 23, defCount 2. Mismatch window
  until #19004 lands. PR #19004 then needs no rebase (it doesn't touch
  the Lean file).
- If **#19004 lands first** (STATE-SYNC before S10 ACT): origin/main
  has state.md / JSON at iteration 13 with "S11 ACT ready for
  pruner-def transcription" wording, but the Lean file is still at
  S9 tip (761 LOC, no `primesUpTo`). Mismatch window until #19014 lands.
  PR #19014 then needs no rebase (it doesn't touch state.md / JSON).

**Either order is acceptable.** The shorter mismatch window is
preferable; the deployer typically processes by PR-number-ascending,
which gives #19004 first. Recommendation: **do not intervene**; let
the deployer merge in its natural order. Both mismatch windows are
short and self-healing.

### §3.3 What ACTIVE intervention would look like (and why not to)

Intervention options researchers sometimes attempt during deployer stall:

- **Force a rebase merge via `gh pr merge --rebase`**: requires push
  access; this slug is in the `loom:research` flow which the deployer
  agent owns. Bypasses the deployer's serialization. **Don't.**
- **Open a `loom:review-requested` PR variant**: per CLAUDE.md §"PR
  Labels for Math Agents", math PRs MUST NOT add `loom:review-requested`;
  the Loom Judge / Champion path is reserved for code-quality review,
  not deployer bypass. **Don't.**
- **Comment on the PR pinging the deployer**: deployer is fully
  autonomous (5–30 min cycle); commenting adds noise without effect.
  **Don't.**

The only researcher-facing intervention pattern is **closing
superseded PRs** (see §5 for #18024) so the deployer's working set
shrinks. That's a pure cleanup operation, not a bypass.

## §4 Post-merge JSON `leanFiles[]` mechanic-sync gap

### §4.1 Current state of `src/data/research/problems/bounded-prime-gaps-oq-03-oq-02.json` on origin/main

Verified 2026-05-15 ~01:32 Z via
`gh api repos/rjwalters/lean-genius/contents/src/data/research/problems/bounded-prime-gaps-oq-03-oq-02.json | jq '.leanFiles | map(select(.filename == "BoundedPrimeGapsOQ03OQ02.lean")) | .[0]'`:

```json
{
  "lineCount": 761,
  "theoremCount": 23,
  "defCount": 2,
  "axiomCount": 1,
  "sorryCount": 0
}
```

These reflect the S9 ACT tip (PR #18218, merged 2026-05-12). Accurate
at PR #19004's creation time.

### §4.2 What PR #19004 says about `leanFiles[]`

Verbatim from PR body §"What this PR does NOT change":

> "`leanFiles[]` JSON metrics (already accurate per prior mechanic syncs)"

This is **correct** at the moment PR #19004 was created (S9 tip, 761 LOC)
but **becomes stale** the moment PR #19014 merges.

### §4.3 Post-merge truth (after BOTH PRs land)

The Lean file on origin/main will be:

- `lineCount`: 761 → **835** (+74 net; PR header says +80 / -6, but
  net non-deletion is +74 because two deprecation-rename lines are
  rewrites, not pure adds).
- `theoremCount`: 23 → **25** (+2: `primesUpTo_10_eq`, `primesUpTo_50_eq`).
- `defCount`: 2 → **3** (+1: `primesUpTo`).
- `axiomCount`: **1** (unchanged; the two `native_decide` sanity tests
  in #19014 reuse the S4 `Lean.ofReduceBool` axiom).
- `sorryCount`: **0** (unchanged).

But the JSON will continue to read 761 / 23 / 2 / 1 / 0 until a
follow-up sync.

### §4.4 Required follow-up

A **Session 15 mechanic-sync PR** (or absorbed into S11 ACT as a
side-channel) needs to bump `leanFiles[BoundedPrimeGapsOQ03OQ02].{lineCount, theoremCount, defCount}`
to the §4.3 values. The bump is ~5-line surgical edit:

```json
{
  "lineCount": 835,
  "theoremCount": 25,
  "defCount": 3,
  "axiomCount": 1,
  "sorryCount": 0
}
```

Plus `lastUpdate` refresh and (recommended) a sentence in
`currentState.focus` acknowledging S10 ACT shipment.

This PREP **deliberately does not write that sync PR** because:

1. The base-truth (post-merge file state) is contingent on the
   deployer stall resolving; writing the JSON now risks the wrong
   `lastUpdate` timestamp if #19014's actual merge time differs.
2. Cleaner separation: this PREP documents the gap; a future Session
   15 ACT or mechanic-sync PR closes it (≤30-min task, can be done
   by any researcher within ~10 minutes after the merges fire).

### §4.5 Forecast-error budget

The §4.3 numbers assume **PR #19014 merges as-is** (no further commits).
The PR has been CLEAN since 2026-05-14 07:15 Z with no doctor / mechanic
edits; no rebase commits have landed. Confidence: 95%.

If a doctor or mechanic adds a fix commit before merge (e.g., a
review-requested change), the §4.3 numbers shift by ≤10 LOC. The sync
should **re-read the file post-merge** rather than blindly trust §4.3.

## §5 PR #18024 supersedure recommendation

### §5.1 Mathematical content comparison

| PR     | Iteration | Case        | Search space        | Status at v4.26.0           | Mathematical signal                                |
|--------|-----------|-------------|---------------------|------------------------------|---------------------------------------------------|
| #18024 | "S6 alt"  | `(k, w) = (9, 26)` | C(26, 9) = 3,124,550 | **Vacuous** (`H(9) = 30 > 25`) | Stress-test of decider at 3.1M; no diameter bound exercised |
| #18027 | S6 ACT (merged) | `(k, w) ∈ {(3,7), (4,9), (5,13), (6,17)}` | 35 + 126 + 1,287 + 12,376 ≈ 14k | **Non-vacuous** (each H(k) bound is tight, witnessed by classical admissible tuples) | Actually exercises the diameter bound + Decidable instance over real cases |

#18024's `(9, 26)` provides **lower mathematical value** at **245× the
runtime cost** of the merged S6 #18027 contribution. The current
state.md narrative (lines 119–170, landed via #18027) **explicitly
rejects** the intermediate-vacuous-scaling strategy in favor of the
non-vacuous boundary cases.

### §5.2 Technical state

- `mergeStateStatus`: **DIRTY** since at least 2026-05-13 (S8 #18090
  +260 LOC + S9 #18218 +144 LOC merged AFTER #18024 was created;
  the 245-LOC base file has grown to 761 LOC, so #18024's text-level
  insertion point at "old line 244" cannot resolve).
- Rebasing #18024 would require: (a) repositioning the new theorem
  in the current file structure (~line 360 region, after the merged
  S6 non-vacuous block), (b) updating its state.md / JSON edits to
  reflect the post-S6/S8/S9 narrative, (c) Docker-verifying the
  3.1M-subset `native_decide` at v4.26.0 (≥30 s runtime, possible
  CI timeout risk), (d) justifying the vacuous-case extension that
  #18027 explicitly avoided. Cumulative effort: ~2-3 h.
- Marginal mathematical value: near-zero (vacuous case stress-test
  redundant with S5 #17944's `(8, 22)` at 3.2 × 10⁵).

### §5.3 Recommendation

**Close #18024 as "Superseded by #18027".** A close-comment can cite:

> "S6 ACT #18027 (merged 2026-05-12T09:55:13Z) landed the S6 iteration
> via four non-vacuous boundary cases at C(7,3)/C(9,4)/C(13,5)/C(17,6) ≈
> 14k cumulative subsets, four orders of magnitude cheaper than this
> PR's `(9, 26)` 3.1M-subset case AND exercising the diameter bound
> non-vacuously. See state.md:160–170 for the deviation rationale.
> This PR's `(9, 26)` extension would re-introduce a vacuous case
> in the same regime as S5 #17944's `(8, 22)`; the S7 deferred
> queue still allows revisiting `(10, 30)` later if scaling evidence
> from S11/S12 demands it."

**This PREP does not close #18024 itself** — the close action is left
to a deployer / doctor / human reviewer with PR-state write access.
The close justification is documented here for the record.

## §6 S11 ACT pre-flight: bearer re-pin at manifest SHA

### §6.1 Manifest-SHA verification (closes a S10c/S10d PREP loop)

S10c PREP §6 and S10d PREP §11 cited Mathlib bearers at "tag
`v4.26.0`" and noted line numbers may drift relative to the manifest
SHA. This PREP closes that verification gap.

`gh api` calls executed 2026-05-15 ~01:33 Z against
`ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (the actual manifest pin):

| Bearer                                                | File path                                          | Manifest-SHA line | S10d PREP cite | Drift |
|-------------------------------------------------------|----------------------------------------------------|-------------------|----------------|-------|
| `Nat.primesBelow`                                     | `Mathlib/NumberTheory/SmoothNumbers.lean`          | **41**            | 41             | 0     |
| `Finset.sort`                                         | `Mathlib/Data/Finset/Sort.lean`                    | **33**            | 33             | 0     |
| `List.toFinset_card_of_nodup`                         | `Mathlib/Data/Finset/Card.lean`                    | **205**           | 205            | 0     |
| `card_union_eq_card_add_card`                         | `Mathlib/Data/Finset/Card.lean`                    | **563**           | 563            | 0     |
| `card_union_of_disjoint` (`@[simp] alias`)            | `Mathlib/Data/Finset/Card.lean`                    | **566**           | 566            | 0     |
| `Finset.powersetCard_nonempty`                        | `Mathlib/Data/Finset/Powerset.lean`                | **232**           | (not pinned)   | new   |
| `Multiset.nodup_range`                                | `Mathlib/Data/Multiset/Range.lean`                 | **73**            | 73             | 0     |
| `List.Nodup.filter`                                   | `Mathlib/Data/List/Nodup.lean`                     | **235**           | (not pinned)   | new   |

**All S10c / S10d PREP citations are stable at the manifest pin.** No
re-citation needed in S11 ACT.

Two new bearer pins added: `Finset.powersetCard_nonempty` at line 232
(S10d §3.4 form (B) — pinned now, was not pinned inline before) and
`List.Nodup.filter` at line 235 (S10d §5.2 — pinned now, was vague
before).

### §6.2 What S11 ACT actually needs to ship

Per S10c PREP §3.4 + S10d PREP §5, the S11 ACT deliverable is:

```lean
-- Pruned recursion (S10d form (C) + option (i))
def searchAux (w k : ℕ) :
    (primes : List ℕ) → (candidates : List ℕ) → (chosen : List ℕ) → Bool
  | [], candidates, chosen =>
      decide (candidates.length ≥ k - chosen.length)
  | p :: primes', candidates, chosen =>
      if candidates.length < k - chosen.length then false
      else
        (List.range p).any (fun r =>
          let candidates' := candidates.filter (fun n => n % p ≠ r)
          let chosen'     := chosen.filter (fun n => n % p ≠ r)
          if chosen'.length < chosen.length then false
          else searchAux w k primes' candidates' chosen')
termination_by primes _ _ => primes.length
decreasing_by simp_wf; omega

-- Entrypoint (S10d option (i))
def engelsmaSearchPruned (w k : ℕ) : Bool :=
  searchAux w k (primesUpTo k) ((List.range w).filter (· ≠ 0)) [0]
```

Plus 2-3 small-case unit tests via `native_decide`
(`engelsmaSearchPruned_6_16_eq_engelsmaSearch_6_16`, etc.).

S11 ACT LOC budget: ~25 LOC for the two definitions + ~10–20 LOC for
unit tests + (optionally) ~30–50 LOC for the disjointness + residue
invariant private lemmas. Total: ~35–95 LOC. Well within S10 PREP §8's
"+120–180 LOC" estimate.

### §6.3 What S11 ACT does **not** need to do

- **Does not need to prove `searchAux` correctness.** That's S12 ACT
  (`searchAux_sound` + `searchAux_complete` + `engelsmaSearchPruned_eq_engelsmaSearch`).
  S10 PREP §4 decomposes the correctness lemmas; S11 ACT just ships
  the executable definition + sanity tests.
- **Does not need to discharge the axiom.** That's S12+ ACT
  (`engelsmaSearchPruned 246 50 = false := by native_decide`).
- **Does not need to touch `BoundedPrimeGapsOQ03.lean`.** The axiom
  closure lives in OQ-03 but the discharge composes through
  `engelsma_lower_bound_of_engelsmaSearch_false` (already shipped by
  S9 #18218).

### §6.4 S11 ACT pre-flight checklist (for the future S11 author)

Pre-claim:

- [ ] `gh pr list -R rjwalters/lean-genius --search "bounded-prime-gaps-oq-03-oq-02 in:title" --state open`
      — confirm neither #19014 nor #19004 still pending (block S11 until
      both land, OR rebase against `#19014`'s tip if doing it before
      #19004).
- [ ] Verify the JSON `leanFiles[]` block matches §4.3 (post-merge);
      if stale, fold the sync into the S11 ACT PR.
- [ ] Skim the §6.1 bearer table; no re-verification needed unless
      `proofs/lake-manifest.json` has rotated.

Implementation:

- [ ] Add `def searchAux` + `def engelsmaSearchPruned` per §6.2.
- [ ] Add 2-3 small-case `native_decide` unit tests (mirror
      `engelsmaSearch_7_3_eq_true` at line 758 of the S9 tip).
- [ ] Optionally add 2-3 private invariant lemmas per S10d §5.1.

Build:

- [ ] `./proofs/scripts/docker-build.sh Proofs.BoundedPrimeGapsOQ03OQ02`
      — expect 7745 jobs clean (S10 ACT baseline) plus 2-3 new jobs for
      the searchAux unit tests; runtime delta should be < 5 s if the
      pruning is effective on small cases.

Race:

- [ ] Re-run the pre-claim `gh pr list` immediately before `git push`
      per `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`.

## §7 Race check + diff scope (this PREP)

### §7.1 Race check (2026-05-15 ~01:33 Z)

- `gh pr list --repo rjwalters/lean-genius --search "bounded-prime-gaps-oq-03-oq-02 in:title" --state open`
  → 3 results (#19014, #19004, #18024) — all cataloged in §1.
- **No competing S15 / coordination PREP** on this slug currently
  open. Filename `2026-05-15-s15-prep-coord-merge-sequencing.md` is
  unique under `sessions/` (existing files: `s10`, `s10b`, `s10c`,
  `s10d` PREPs from 2026-05-12 / 2026-05-13).
- This PREP creates **exactly one file** under
  `research/problems/bounded-prime-gaps-oq-03-oq-02/sessions/` and
  edits no other file in the repo.

### §7.2 Diff scope

This PREP adds **exactly one file**:

- `research/problems/bounded-prime-gaps-oq-03-oq-02/sessions/2026-05-15-s15-prep-coord-merge-sequencing.md`

**No edits** to:

- `problem.md`, `state.md`, `knowledge.md`.
- `src/data/research/problems/bounded-prime-gaps-oq-03-oq-02.json`.
- `proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean` or any `.lean` file.
- Gallery `src/data/proofs/bounded-prime-gaps-oq-03/...`.

No `lake build` attempted; doc-only.

### §7.3 What this PREP intentionally does NOT do

- **Does not close PR #18024.** §5 documents the supersedure case;
  the close action requires PR write access (deployer / doctor / human).
- **Does not update `leanFiles[]` JSON.** §4 documents the post-merge
  gap; the sync requires the merges to fire first (otherwise the
  `lastUpdate` timestamp races).
- **Does not modify `state.md`.** PR #19004 is the canonical
  STATE-SYNC for the S9 → S11 transition; modifying state.md here
  would conflict with #19004 once it merges.
- **Does not open a fourth S10 PREP overlay.** S10/S10b/S10c/S10d
  PREPs (#18281, #18500, #18601, #18662) collectively pin the S11
  ACT design; nothing in §1–§6 contradicts or extends those
  decisions, only re-pins them at the manifest SHA and surfaces the
  merge-sequencing + JSON-sync gaps.

## §8 Honesty disclosures

1. **§3.1 deployer-stall numbers are point-in-time.** The 22.5 h
   zero-merge window and 30 stuck CLEAN PRs were measured at
   2026-05-15 ~01:31 Z; the stall may resolve between PREP submission
   and merge. The coordination value of §3.2 (merge-order forecast)
   is unaffected by stall duration.

2. **§4.3's LOC delta forecast (+74 net, not +80)** is derived from
   PR #19014's `+80 / -6` header by subtracting the two deprecation
   renames (which read as `+` adds and `-` removes in unified diff
   even though they replace existing lines). The actual post-merge
   `wc -l` should match 835 ± 2 LOC. If post-merge reading differs
   by > 5 LOC, this PREP's forecast was wrong and a doctor should
   investigate.

3. **§5.1's "245× runtime cost" comparison** divides 3,124,550 by
   the cumulative 14,024 of #18027's four non-vacuous cases. The
   actual native_decide runtime scales sub-linearly with `Nat.choose`
   due to pruning + IR reuse; the ratio is a "decoder work" upper
   bound, not a wall-clock prediction. Mathematical-value comparison
   (vacuous-vs-non-vacuous) is independent of runtime ratio and is
   the decisive factor in §5.3.

4. **§6.1 Mathlib bearer line numbers** verified via
   `gh api repos/leanprover-community/mathlib4/contents/...?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
   on 2026-05-15. Lines may drift if the manifest pin rotates before
   S11 ACT; the **bearer names** are stable (these are foundational
   Finset/List/Nat lemmas).

5. **§6.2's S11 ACT skeleton** is reproduced verbatim from S10d PREP
   §5; not independently derived. The forecast LOC budget (~35–95 LOC
   total) is the union of S10c §3.4 + S10d §5.1 budgets.

6. **No `.lake` build attempted; no `proofs/.lake` directory
   modifications.** Per `feedback_researcher_lake_symlink_loop_and_wipe.md`.

7. **§4.1 JSON-content fetch was performed via
   `gh api repos/rjwalters/lean-genius/contents/src/data/research/problems/bounded-prime-gaps-oq-03-oq-02.json | jq`.**
   Total gh API calls this session: 1 contents-API + 7
   contents-API for Mathlib bearers + 4 `gh pr list / view` calls.
   `gh api /search/code` usage: 0 (avoids the 30/hr cap documented
   in `feedback_researcher_11_2026_05_13_sextuple_audit_correction_session.md`).

## §9 Decision log

- **2026-05-15 S15 PREP**: Decision to write a coordination PREP rather
  than a Session 15 STATE-SYNC absorbing the post-merge state. Reason:
  PR #19004 is the canonical STATE-SYNC for the S9 → S11 transition
  and is already CLEAN-mergeable; preempting it would race-conflict
  the deployer. A coordination PREP documents the gaps without
  competing for state.md / JSON write authority.

- **2026-05-15 S15 PREP**: Decision to recommend **closing #18024**
  rather than rebasing it. Reason: §5.1 / §5.2 — the merged S6 #18027
  explicitly rejected the strategy #18024 attempts, and the rebase
  cost (~2-3 h) far exceeds the mathematical value (~0). The S7
  deferred-queue slot still allows revisiting `(10, 30)` if S11/S12
  scaling evidence justifies it.

- **2026-05-15 S15 PREP**: Decision to **not** update `leanFiles[]`
  JSON in this PREP, even though §4.3 has the post-merge values
  forecast. Reason: writing the JSON now risks `lastUpdate` timestamp
  race against the actual merge of #19014; a follow-up sync PR
  written after merges fire is cleaner.

- **2026-05-15 S15 PREP**: Decision to re-pin Mathlib bearers at the
  manifest SHA rather than the v4.26.0 tag (§6.1). Reason: closes the
  verification loop S10c/S10d PREP left open ("if manifest has
  drifted, line numbers may shift"). All seven existing pins are
  stable; two new pins added.

- **2026-05-15 S15 PREP**: Decision to publish this PREP under
  `s15-prep-coord-merge-sequencing` rather than `s14b-prep-` or
  similar. Reason: PR #19004's title is "Session 14 STATE-SYNC", so
  Session 14 is allocated. This PREP intentionally claims a Session
  15 slot to leave room for the post-merge JSON sync as a possible
  "Session 15 STATE-SYNC" or "Session 15 mechanic-sync" sibling.

## §10 References

### Mathlib v4.26.0 manifest-pinned bearers (verified 2026-05-15)

- `Mathlib/NumberTheory/SmoothNumbers.lean:41` — `Nat.primesBelow`.
- `Mathlib/Data/Finset/Sort.lean:33` — `Finset.sort`.
- `Mathlib/Data/Finset/Card.lean:205` — `List.toFinset_card_of_nodup`.
- `Mathlib/Data/Finset/Card.lean:563` — `card_union_eq_card_add_card`.
- `Mathlib/Data/Finset/Card.lean:566` — `card_union_of_disjoint` (alias).
- `Mathlib/Data/Finset/Powerset.lean:232` — `powersetCard_nonempty`.
- `Mathlib/Data/Multiset/Range.lean:73` — `nodup_range`.
- `Mathlib/Data/List/Nodup.lean:235` — `List.Nodup.filter`.

### Local Lean file (post-merge truth)

- `proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean:78` — `IsAdmissibleBdd`.
- `proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean:88` — `isAdmissible_iff_bdd`.
- `proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean:~573` — `engelsma_lower_bound_of_finitary` (S8).
- `proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean:~702` — naive `engelsmaSearch` (S9).
- `proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean:~734` — `engelsma_lower_bound_of_engelsmaSearch_false` (S9).
- `proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean:~758` — `engelsmaSearch_7_3_eq_true` (S9 unit test).
- `proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean:~770` — `primesUpTo` (S10 ACT, post-#19014).
- `proofs/Proofs/BoundedPrimeGapsOQ03.lean:134` — `engelsma_lower_bound` axiom (target of replacement).

### Open PRs surveyed

- #19014 — S10 ACT (S9 unblocker + `primesUpTo` bearer), build-verified 7745 jobs.
- #19004 — Session 14 STATE-SYNC absorbing S10/S10b/S10c/S10d PREP backlog.
- #18024 — S6 alt `(9, 26)` (DIRTY, superseded by merged S6 #18027).

### Predecessor PREP files (`sessions/`)

- `2026-05-12-s10-prep-pruned-search-design.md` (PR #18281).
- `2026-05-12-s10b-prep-axiom-status-audit.md` (PR #18500).
- `2026-05-13-s10c-prep-primesBelow-termination.md` (PR #18601).
- `2026-05-13-s10d-prep-leaf-case-and-initialization.md` (PR #18662).
- **This file**: `2026-05-15-s15-prep-coord-merge-sequencing.md`.

### Sibling memory cross-references

- `feedback_researcher_deployer_stall_coordination_prep_pattern.md` — the umbrella pattern this PREP instantiates.
- `feedback_researcher_cross_pr_coordination_audit_pattern.md` — multi-open-PR audit shape.
- `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md` — pre-claim + pre-push race check.
- `feedback_researcher_gh_default_repo_mathlib4_fork_trap.md` — gh CLI default-repo trap (used `-R rjwalters/lean-genius` throughout).
- `feedback_researcher_lake_symlink_loop_and_wipe.md` — why no `lake build` attempted.

**End of S15 PREP.**
