# Session 22 — S21 STATE-SYNC — JSON `knowledge.*` catchup post-S11a-ACT + S20-PREP (doc-only)

**Date**: 2026-05-16
**Researcher**: researcher-11
**Phase**: S21 STATE-SYNC (doc-only — JSON `knowledge.{progressSummary,
builtItems,nextSteps}` + `lastUpdate` refresh; no Lean changes, no
`knowledge.md` body edit, no `problem.md` edit, no `meta.json` edit)
**Risk**: LOW (documentation only; no math claim changes; absorbs
already-merged S11a ACT + S20 PREP narrative into the JSON registry).

## §0 What this PR does

S20 PREP (PR #19570, researcher-10) merged 2026-05-16T13:52:39Z (~1h
before this claim) updated `state.md` head + JSON `currentState.{phase,
iteration,focus,nextAction}` to reflect post-S11a-ACT + S20 PREP
reality. However the JSON catchup was incomplete:

| Field | S20 PREP state | Drift |
|---|---|---|
| `currentState.phase` | "PREP" + S20 focus | ✅ current |
| `currentState.iteration` | 20 | ✅ current |
| `currentState.focus` | S20 PREP focus paragraph | ✅ current |
| `currentState.nextAction` | Path A/B/C structure | ✅ current |
| `currentState.blockers` | B1 (Docker hung) | ✅ current |
| `knowledge.progressSummary` | mentions S17+S18+S19 only | ❌ missing S11a ACT + S20 PREP absorption |
| `knowledge.builtItems` | S10 ACT items only | ❌ missing 7 S11a ACT Lean items + S17/S18/S19/S11a/S20 session memos |
| `knowledge.nextSteps` | "S11 ACT — transcribe pruned engelsmaSearchPruned ..." | ❌ stale — S11 = S11a ACT already shipped (PR #19519, merged 08:52Z); needs S11a-VERIFY + S11b-α/β/γ/δ four-sub-PR split per S20 PREP §5 |
| `knowledge.mathlibGaps` | (preserved) | ✅ current — S20 PREP §4 zero-drift confirmed |
| `knowledge.insights` | (preserved) | ✅ current |
| `lastUpdate` | 2026-05-16T09:30:00Z | ❌ stale — should be post-S20-PREP-merge |

This S21 STATE-SYNC closes the 4 ❌ rows with no Lean changes and no
bearer re-spot-check (S20 PREP §4 already confirmed zero drift; doing
it again at SHA-stable T+1h would be busywork per
`MEMORY.md` `feedback_researcher_postship_pivot_to_own_just_merged_prep_with_zero_json_edits_at_T_plus_minutes_ship_tight_json_catchup_only_no_bundled_respotcheck.md`).

## §1 Pre-flight signal: 0 open PRs, Docker still hung, host disk stable

```bash
$ gh pr list -R rjwalters/lean-genius --state open --search "bounded-prime-gaps-oq-03-oq-02 in:title"
[]

$ timeout 30 docker info 2>&1 | grep -E "^Client|^Server" | head -3
Client:
Server:

# Server block returns no Containers/Runtime/Storage Driver/Server Version
# lines — canonical signature of hung daemon (continues B1 from S20 PREP).

$ df -h /System/Volumes/Data
/dev/disk3s5   926Gi   883Gi   6.7Gi   100%   /System/Volumes/Data
```

B1 remains RED at S21 STATE-SYNC open. The 12 h cancellation clause
(state.md "Path C") triggers at 2026-05-16T18:01:00Z (Docker hang
since 2026-05-16T06:01:00Z); currently 2026-05-16T~15:00Z → 3 h
remaining within the Path A window. S21 STATE-SYNC does NOT activate
Path C; it preserves the Next Action Path A/B/C structure verbatim.

## §2 S11a ACT additions (7 new Lean items, PR #19519)

Per the S11a ACT session memo (`sessions/2026-05-16-s11a-act-engelsma-pruned-build-pending.md`)
+ `git show origin/main:proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean | wc -l` (953 LOC, was 835):

1. `private def tryBranch (p r : ℕ) (candidates chosen : List ℕ) (cont : List ℕ → List ℕ → Bool) : Bool` (line ~849, ~8 LOC + docstring)
2. `def searchAux (w k : ℕ) : List ℕ → List ℕ → List ℕ → Bool` (line ~860, ~11 LOC + docstring + `termination_by primes.length` + `decreasing_by all_goals (simp_wf; omega)`)
3. `def engelsmaSearchPruned (w k : ℕ) : Bool` (line ~881, ~2 LOC + docstring)
4. `theorem engelsmaSearchPruned_eq_false_iff (w k : ℕ) : engelsmaSearchPruned w k = false ↔ ∀ H ∈ powersetCard k (Finset.range w), 0 ∈ H → ¬ IsAdmissible H` (line ~893, ~3 LOC + docstring; **bridge with `sorry`** at line 925; S11b-β/γ/δ discharge)
5. `theorem engelsma_lower_bound_of_engelsmaSearchPruned_false : engelsmaSearchPruned 246 50 = false → engelsma_lower_bound` (line ~927, ~5 LOC; chains pruned bridge through `engelsma_lower_bound_of_finitary` from S8 ACT)
6. `theorem engelsmaSearchPruned_7_3_eq_true : engelsmaSearchPruned 7 3 = true := by native_decide` (line ~937, ~2 LOC)
7. `theorem engelsmaSearchPruned_11_5_eq_true : engelsmaSearchPruned 11 5 = true := by native_decide` (line ~942, ~2 LOC)

Total: 7 new declarations (1 private def + 2 def + 4 theorem),
+118 LOC vs S10 ACT baseline (835 → 953); axiomCount stays 1
(`Lean.ofReduceBool` reused via `native_decide`); sorries 0 → 1
(line 925, named for S11b-β/γ/δ discharge).

## §3 S20 PREP additions (sessions memo only, no Lean delta)

- `sessions/2026-05-16-s20-prep-s11a-paste-audit-and-shipped-api-resync.md` (~720 LOC):
  §2 paste audit (7/7 sub-sections verbatim), §3 SHIPPED API resync
  with 3 DELTAs vs S18 PREP §2, §4 4-Mathlib-bearer SHA spot-check at
  pin `2df2f0150c…` zero drift, §5 S11b 4-sub-PR split recommendation
  (α/β/γ/δ), §6 paste-ready S11b-α combiner skeleton with 2 named
  sorries S11b-α-1 / S11b-α-2, §7 risk inventory R1-R8, §8
  ACT-readiness gate refresh.

## §4 Files modified in this S21 STATE-SYNC

| File | Change shape |
|---|---|
| `src/data/research/problems/bounded-prime-gaps-oq-03-oq-02.json` | `knowledge.progressSummary` rewritten to absorb S11a ACT + S20 PREP; `knowledge.builtItems` appended with 7 S11a Lean items + S17 + S18 + S19 + S11a-ACT + S20 PREP session memos; `knowledge.nextSteps` rewritten to S11a-VERIFY + S11b-α/β/γ/δ structure; top-level `lastUpdate` refreshed |
| `research/problems/bounded-prime-gaps-oq-03-oq-02/state.md` | bump Iteration 20 → 21; append "## Session 22 — S21 STATE-SYNC" block |
| `research/problems/bounded-prime-gaps-oq-03-oq-02/sessions/2026-05-16-s21-statesync-knowledge-catchup-post-s20.md` | new file (this memo) |

**0 Lean files modified.** **0 `knowledge.md` body edits** (catalog
of new built items lives only in JSON `knowledge.builtItems`, matching
how previous STATE-SYNCs handled the same drift). **0 `problem.md`
edits.** **0 gallery `meta.json` / annotations / index.ts edits.**
**0 Mathlib pin upgrades.** **0 bearer re-spot-check** (S20 PREP §4
confirmed zero drift at SHA `2df2f0150c…` 1h ago; pin unchanged).

## §5 Honest calibration

This S21 STATE-SYNC:

- Adds 0 Lean to the project.
- Closes 0 sorries.
- Resolves 0 of the open mathematical questions.
- States 0 new theorems.
- Does NOT verify the S11a ACT paste by Docker build (S11a-VERIFY does;
  B1 still RED).
- Does NOT discharge the S11b-α-1 / S11b-α-2 paper sorries from S20
  PREP §6 (Path C activation — deferred to S21 PREP or later when
  Docker recovery exceeds 12 h, currently 9 h since hang at 06:01Z).

It does:

- Refresh JSON `knowledge.progressSummary` from "S17+S18+S19 STATE-SYNC"
  framing to current "S11a ACT shipped + S20 PREP closing audit"
  framing.
- Append S11a ACT's 7 new Lean items to `knowledge.builtItems`
  (matching the file's current 953-LOC reality).
- Append S17 PREP / S18 PREP / S19 STATE-SYNC / S11a ACT / S20 PREP
  session memos to `knowledge.builtItems` (was missing).
- Rewrite `knowledge.nextSteps` to point at S11a-VERIFY + S11b-α/β/γ/δ
  four-sub-PR split (was stuck at pre-S11 ACT "transcribe pruned
  engelsmaSearchPruned" item).
- Refresh top-level `lastUpdate` from 09:30Z to post-S20-PREP-merge time.
- Append S21 STATE-SYNC entry to state.md Session Log so future
  readers see the catchup.

The 4-sub-PR split (S11b-α/β/γ/δ) recipe from S20 PREP §5 is preserved
verbatim; this PR re-references it without re-spending the LOC budget
or re-spot-checking the Mathlib bearers.
