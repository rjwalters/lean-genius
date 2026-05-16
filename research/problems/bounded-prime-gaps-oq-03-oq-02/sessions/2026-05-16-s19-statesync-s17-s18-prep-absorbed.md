# Session 19 STATE-SYNC — S17 PREP (#19354) + S18 PREP (#19386) absorbed (doc-only)

**Date**: 2026-05-16
**Researcher**: researcher-12
**Phase**: STATE-SYNC (doc-only). Absorbs two sibling PREP merges that
landed after Session 15 STATE-SYNC (#19342, merged 01:08:53Z) into
`state.md` head + JSON `currentState`. Strictly additive.
**Type**: Doc-only. New `sessions/` file + state.md head replacement
(historical tail preserved) + JSON refresh. **No** edits to
`knowledge.md`, `problem.md`, gallery `meta.json`, or any `.lean`
file. **No `lake build` attempted.**
**Branch base**: `origin/main` at commit `78448f56d0a`
(`research(birthday-problem-oq-01-oq-02): S5 STATE-SYNC ... (#19355)`,
HEAD at STATE-SYNC creation time).
**Mathlib pin**: v4.26.0 = `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(unchanged from S15/S16/S17/S18 PREP base; re-verified against
`proofs/lake-manifest.json` line 8 at branch HEAD).

## §0 Why this STATE-SYNC exists

Session 15 STATE-SYNC (#19342, merged 2026-05-16T01:08:53Z) brought
`state.md` head + JSON to **iteration 16** by absorbing S10 ACT
(#19014) + S15 PREP (#19201) + S16 PREP (#19273). Two further
doc-only PREP PRs have since landed on `origin/main`:

| PR     | Phase     | Researcher    | Merged (UTC)        | Net delta to slug                            |
|--------|-----------|---------------|---------------------|----------------------------------------------|
| #19354 | S17 PREP  | researcher-10 | 2026-05-16 01:08:19 | +1 session log (~705 LOC); paste-ready S11 skeleton |
| #19386 | S18 PREP  | researcher-8  | 2026-05-16 02:46:?? | +1 session log (~715 LOC); §6.4 sub-lemma decomposition |

Both PRs touch **only** `sessions/` files; neither edits `state.md`,
`knowledge.md`, `problem.md`, gallery `meta.json`, or any `.lean`
file. So Lean file metrics (835 / 25 / 3 / 1, 0 sorries) are
unchanged on `origin/main`, but the state.md narrative head + JSON
`currentState.focus` / `nextAction` / `iteration` / `since` /
`lastUpdate` lag behind the post-S18-PREP recipe.

Per S18 PREP §6 step 11 (verbatim): "**Update `state.md` + JSON via
S19 STATE-SYNC PR (separate from ACT).**" This Session 19
STATE-SYNC discharges that owed update.

## §1 Drift recheck since S18 PREP

S18 PREP completed at 2026-05-16T~02:35Z (PR creation time, per
session file §1). This STATE-SYNC opens at 2026-05-16T~03:59Z
(~84 min later).

| Surface                                                  | S18 PREP value                              | This STATE-SYNC          | Drift |
|----------------------------------------------------------|---------------------------------------------|--------------------------|-------|
| `proofs/lake-manifest.json` Mathlib `rev`                | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`  | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` | **0** |
| `BoundedPrimeGapsOQ03OQ02.lean` LOC                       | 835                                         | 835                      | **0** |
| `BoundedPrimeGapsOQ03OQ02.lean` `end namespace` line      | 835                                         | 835                      | **0** |
| Open PRs on slug                                         | 0                                           | 0                        | **0** |
| Sessions/ file count                                     | 7 (incl. S17 PREP just merged)              | 8 (incl. S18 PREP)       | **+1** |
| Mathlib `Finset/Card.lean` SHA (spot-check via gh api)   | `ce82fb5788b6...` (S18 §3 table line 8/9)   | `ce82fb5788b6...`        | **0** |

**Verdict**: zero substantive drift on any Lean / manifest /
Mathlib-bearer surface. The S17 PREP §6 paste-ready skeleton +
S18 PREP §2 sub-lemma decomposition both remain paste-ready against
current `origin/main`.

## §2 Lean file shape (unchanged from S15 STATE-SYNC tip)

`proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean` on `origin/main` at
HEAD `78448f56d0a`:

| Metric        | Value |
|---------------|-------|
| `lineCount`   | 835   |
| `theoremCount`| 25    |
| `defCount`    | 3     |
| `axiomCount`  | 1 (`Lean.ofReduceBool`, propagated from S4) |
| `sorryCount`  | 0     |
| Insertion pt  | line 833 (after `primesUpTo_50_eq`, before `end BoundedPrimeGapsOQ03OQ02`) |

JSON `leanFiles[BoundedPrimeGapsOQ03OQ02]` reads `835 / 25 / 3 / 1`
matching. No mechanic-sync gap. Gallery `meta.json` for this slug
not touched by either PREP; no drift call-out owed.

## §3 S17 PREP (#19354) — Net summary

**Researcher**: researcher-10 (`research/bounded-prime-gaps-oq-03-oq-02-s17-prep-postS10ACT-drift-recheck`).
**Branch base**: `origin/main` at `d35a6f0f2ac` (creation time).
**Scope**: drift recheck of S15 PREP bearer table + S16 PREP Option
α/β/γ trilemma against the post-S10-ACT-merge file shape, plus a
**paste-ready S11 ACT skeleton** composing Option α + the new
`primesUpTo` bearer.

**Five sections**:

- **§2** Mathlib SHA drift recheck. Zero drift; SHA unchanged.
- **§3** Post-S10-ACT-merge file shape inventory (835 LOC, namespace
  structure, insertion pt for S11 ACT).
- **§4** S15 PREP §6 10-bearer table drift recheck (all 10 still
  valid at the pinned SHA).
- **§5** S16 PREP Option α/β/γ survival recheck. All three options
  still apply; Option α remains the primary recommendation (LOC
  overhead, idiomatic shape, no termination-binder count risk).
- **§6** **Paste-ready S11 ACT skeleton**: §6.1 `tryBranch` helper
  (~6 LOC), §6.2 `searchAux` recursive body (~22 LOC,
  `termination_by primes.length` 0-binder + `decreasing_by
  all_goals (simp_wf; omega)`), §6.3 `engelsmaSearchPruned` Bool
  surface (~5 LOC), §6.4 bridge theorem `sorry`-scaffold (~12 LOC,
  S11 ACT author owns discharge), §6.5 two `native_decide` sanity
  tests at `(7, 3)` and `(11, 5)` (~6 LOC). Total skeleton LOC:
  ~51 (within S10 PREP §8 budget).

**S17 PREP §7 ACT-readiness checklist (verbatim summary)**:
- Step 1 paste §6.1+§6.2+§6.3 (+33 LOC) — 0 Docker iter.
- Step 2 Docker round 1 build `Proofs.BoundedPrimeGapsOQ03OQ02` — 1 Docker iter.
- Step 3a/3b/3c branch on round-1 verdict (Option α PASS / Option β fallback / re-pin).
- Step 4 paste §6.4 sorry + §6.5 tests (+18 LOC) — 1 Docker iter (test pass).
- Step 5 discharge §6.4 sorry: 3 sub-lemmas per S10 PREP §8.
- Step 6 axiomCount recheck.

**Net**: +1 sessions/ file (705 LOC). 0 Lean lines. No state.md /
JSON / knowledge.md / meta.json edits.

## §4 S18 PREP (#19386) — Net summary

**Researcher**: researcher-8 (`research/bounded-prime-gaps-oq-03-oq-02-s18-prep-bridge-decomp`).
**Branch base**: `origin/main` at `8a3cda556b6` (creation time).
**Scope**: §6.4 bridge sub-lemma decomposition extending S17 PREP's
single-`sorry` scaffold into three sub-lemmas + combiner + worked
goal-state for the simpler case, plus a recommended **S11a / S11b
split**.

**Five sections**:

- **§1** Drift recheck since S17 PREP @ 01:04Z (~91 min). Zero
  drift on all surfaces.
- **§2** Sub-lemma signatures:
  - **§2.1 `searchAux_sound`** — induction on `primes`, leaf via
    `Finset.card_union_le` + cardinality arithmetic; inductive via
    `tryBranch` decomposition + IH. ~55-90 LOC.
  - **§2.2 `searchAux_complete`** — induction on `primes`, residue
    witness `r := (H \ chosen.toFinset).min' _ % p`. ~90-140 LOC.
    **Dominant cost.**
  - **§2.3 `IsAdmissible_iff_residue_disjoint_primesUpTo`** —
    combiner; reverse direction splits on `p ≤ k` (hypothesis) vs.
    `p > k` (cardinality bound). ~25-40 LOC.
  - Forward + reverse direction of bridge: ~20-30 LOC combined.
- **§3** Mathlib bearer additions over S17 PREP §4's 10-bearer
  table: 15 total (10 from S17 + 5 new — `List.length_filter_le`,
  `List.mem_filter`, `Finset.mem_powersetCard`,
  `Finset.card_image_le`, `Finset.card_union_le`). All pinned at
  the unchanged Mathlib SHA `2df2f0150c...` with file SHAs
  recorded.
- **§4** Worked goal-state for `searchAux_sound` leaf + inductive
  cases (paper-only; the S11b ACT author uses this as paste-ready
  reasoning, not paste-ready tactic body).
- **§5** **S11a / S11b split recommendation** (now primary path,
  not just escape hatch):
  - **S11a** (skeleton + `sorry` bridge): +~59 LOC, 1-2 Docker
    iters, axiomCount=1, sorries+=1.
  - **S11b** (bridge discharge): +~190-300 LOC, 3-4 Docker iters,
    axiomCount=1, sorries net 0 (S11a +1, S11b -1).
  - Total: ~249-359 LOC across two PRs (vs original S10 PREP §8
    single-PR budget +120-180 LOC).

**S18 PREP §6 staged pickup plan (11 steps)** — see S18 §6 table
for full breakdown; this STATE-SYNC re-prints §6 step 11 verbatim
under §7 below.

**Net**: +1 sessions/ file (715 LOC). 0 Lean lines. No state.md /
JSON / knowledge.md / meta.json edits.

## §5 What this STATE-SYNC absorbs

This Session 19 STATE-SYNC absorbs the following into `state.md`
head + JSON:

1. **Iteration bump**: 16 → 18 (S17 PREP added as Session 17, S18
   PREP added as Session 18).
2. **`Since` bump**: `2026-05-16T00:25:00Z` → `2026-05-16T03:59:00Z`.
3. **`lastUpdate` bump**: same.
4. **`Researcher` attribution**: prepended with `researcher-12
   (Session 19 STATE-SYNC); researcher-8 (S18 PREP); researcher-10
   (S17 PREP)`.
5. **`focus`** rewrite: replaces the iter-16 "S10 ACT shipped +
   S15/S16 PREP doc backlog complete" framing with the iter-18
   "S17 PREP drift recheck + paste-ready S11 ACT skeleton; S18
   PREP §6.4 sub-lemma decomposition + S11a/S11b split
   recommendation" framing.
6. **`nextAction`** rewrite: replaces the unstaged "S11 ACT
   transcribe pruner def + correctness lemma in ~120-180 LOC"
   framing with the **S11a-first** staged framing (paste +
   Docker-verify the §6.1-§6.3 skeleton first, then §6.4
   sorry-scaffold + §6.5 tests; S11b owns the §2 sub-lemma
   discharge separately).
7. **`progressSummary`** prepend: one paragraph summarizing S17 +
   S18 PREP deliverables.
8. **`insights`** append: 2 new entries for S17 PREP + S18 PREP.

**Not absorbed** (intentional):
- `leanFiles[BoundedPrimeGapsOQ03OQ02]` metrics — unchanged
  on origin/main (835 / 25 / 3 / 1, 0 sorries) since both PREPs
  are doc-only.
- Gallery `meta.json` — not touched by either PREP; no drift
  call-out owed.
- `knowledge.md` / `problem.md` — both unchanged, both still
  current.

## §6 ACT-readiness gate (refreshed for S11a)

A 6-item gate copying S18 PREP §6's step structure, refreshed at
STATE-SYNC creation:

| # | Condition                                                      | Status @ 2026-05-16T03:59Z |
|---|----------------------------------------------------------------|----------------------------|
| 1 | Predecessor PREPs merged: S15 + S16 + S17 + S18                | **GREEN** (all 4 merged)   |
| 2 | Mathlib pin SHA unchanged since latest PREP                     | **GREEN** (`2df2f0150c...`) |
| 3 | Open PRs on slug                                                | **GREEN** (0)               |
| 4 | Lean file at expected baseline (835 LOC, 25 thm, 3 def, 1 ax)  | **GREEN** (matches JSON)    |
| 5 | Paste-ready skeleton text present in S17 PREP §6.1-§6.5         | **GREEN** (~51 LOC across 4 sub-§§) |
| 6 | Bearer table re-verified at unchanged Mathlib SHA              | **GREEN** (S18 §3 15-bearer table; SHAs pinned) |

All 6 gates GREEN. **S11a ACT is paste-paste-Docker-verify ready
for the next picker.** Estimated cycle time: ~15-30 min (paste 33
LOC + 1 Docker iter warm cache 60-180s + paste 18 LOC + 1 Docker
iter test pass 60-180s + state-sync follow-up).

## §7 Next ACT picker priority (verbatim from S18 PREP §6, step 11)

> **Step 11**: Update `state.md` + JSON via S19 STATE-SYNC PR
> (separate from ACT).

This Session 19 STATE-SYNC closes step 11. The next ACT picker
picks up at **step 1** of S18 PREP §6:

> **Step 1**: **S11a PR**: paste S17 PREP §6.1 + §6.2 + §6.3 into
> file at line 833. +33 LOC, 0 Docker iters (paste-only).

**S11a deliverable** (per S18 PREP §5.1, restated):

1. `tryBranch` helper (`private def`, ~6 LOC) — S17 PREP §6.1
   verbatim.
2. `searchAux` recursive body (`def`, ~22 LOC,
   `termination_by primes.length` 0-binder +
   `decreasing_by all_goals (simp_wf; omega)`) — S17 PREP §6.2 verbatim.
3. `engelsmaSearchPruned` Bool surface (`def`, ~5 LOC) — S17 PREP §6.3 verbatim.
4. `engelsmaSearchPruned_eq_false_iff` bridge with `sorry`
   placeholder (`theorem`, ~12 LOC) — S17 PREP §6.4 scaffold, sorry
   discharged in S11b.
5. `engelsma_lower_bound_of_engelsmaSearchPruned_false` chained
   from the `sorry`-bridge (~8 LOC).
6. Two `native_decide` sanity tests at `(7, 3)` and `(11, 5)` (~6
   LOC) — S17 PREP §6.5 verbatim.

**S11a estimated diff**: +~59 LOC, axiomCount stays at 1, sorries
0 → 1. Docker iters 1-2 (Option α verify; Option β fallback per
S16 PREP §3.3 if needed).

**S11b deliverable** (deferred separately, per S18 PREP §5.2):

1. `IsAdmissible_iff_residue_disjoint_primesUpTo` combiner (~25-40 LOC).
2. `searchAux_sound` (~55-90 LOC).
3. `searchAux_complete` (~90-140 LOC) — dominant cost.
4. Discharge bridge forward + reverse (~20-30 LOC).

**S11b estimated diff**: +~190-300 LOC, axiomCount stays at 1,
sorries 1 → 0.

## §8 ACT-time traps to budget (S11a picker)

Carry-over from S16 PREP §3 + S17 PREP §8 + S18 PREP §8 honesty
notes. The S11a picker should budget for at least one of these:

1. **Option α elaboration risk** (S16 PREP §3.2). Lean's WF
   elaborator may not descend through `(List.range p).any (fun r =>
   tryBranch ... (searchAux w k primes'))` to find the recursive
   call. **Mitigation**: Option β (mutual recursion) per S16 §3.3,
   +~12 LOC over Option α.
2. **`termination_by primes.length` 0-binder** (S16 PREP §2.2). All
   5 Mathlib precedents at the pinned SHA use 0-binder form. The
   `decreasing_by all_goals (simp_wf; omega)` chain has 1 direct
   precedent (`Mathlib/Data/List/Defs.lean:170`). **Mitigation**:
   if `simp_wf; omega` fails, try `decreasing_tactic` or hand-roll
   the `List.length_filter_le` chain.
3. **`tryBranch` chosen-shrink early return** (S17 PREP §6.1). The
   `if chosen'.length < chosen.length then false` guard returns
   `false` when residue filtering shrinks the prefix. **Trap**:
   in §6.4 bridge proof, this case needs to be eliminated by the
   `hchosen_residue` hypothesis (the prefix is already
   residue-disjoint at every prime, so filtering by `r` preserves
   it). The S11a author should NOT discharge §6.4 — that's S11b's
   job — but should sanity-check the early-return logic at
   `native_decide` time.
4. **`primesUpTo k` membership reasoning** (S18 PREP §3 bearer
   #1 + §2.3 combiner reverse direction). `p ∈ primesUpTo k →
   p ≤ k ∧ p.Prime` is needed in S11b §2.3 but not in S11a.
   **Mitigation**: defer to S11b.
5. **Lake symlink loop on researcher worktrees** (S18 PREP §8.8).
   `proofs/.lake` in each researcher worktree is a self-loop;
   `lake build` direct will loop or fail. **Mitigation**: use
   `./proofs/scripts/docker-build.sh Proofs.BoundedPrimeGapsOQ03OQ02`
   exclusively. The Docker wrapper bypasses the symlink loop by
   containerizing the build.

## §9 Race-check (2026-05-16T03:59Z)

- **Open PRs on slug at STATE-SYNC creation**: 0
  (`gh pr list --search "bounded-prime-gaps-oq-03-oq-02" --state
  open` returns `[]`).
- **Last merged research PR on slug**: #19386 (S18 PREP) at
  2026-05-16T~02:46Z, ~73 min before this STATE-SYNC opens.
- **Last merged research PR on slug touching Lean**: #19014 (S10
  ACT) at 2026-05-15T23:28:41Z, ~4.5 h before this STATE-SYNC.
- **Sibling-worktree race check**: only `researcher-12` (this
  worktree) currently holds a `bounded-prime-gaps-oq-03-oq-02-*`
  branch. No sibling researcher is on slug.
- **Mathlib pin re-verified** at SHA `2df2f0150c...` matching
  S15/S16/S17/S18 PREP base.
- **Files touched by this STATE-SYNC**:
  - `research/problems/bounded-prime-gaps-oq-03-oq-02/sessions/2026-05-16-s19-statesync-s17-s18-prep-absorbed.md` (NEW)
  - `research/problems/bounded-prime-gaps-oq-03-oq-02/state.md` (HEAD replaced; historical tail preserved)
  - `src/data/research/problems/bounded-prime-gaps-oq-03-oq-02.json` (`currentState` block + `lastUpdate` + `progressSummary` prepend + 2 `insights` appends)
- **Files NOT touched**: any `.lean` file, `knowledge.md`,
  `problem.md`, gallery `meta.json`, sibling slug files.

This STATE-SYNC is **conflict-free**: 0 open PRs, paste-only doc
edits, orthogonal to any future PR shape (S11a ACT will touch only
`.lean` + `meta.json` + JSON; S11b will too; S20+ STATE-SYNCs will
touch `state.md` + JSON head).

## §10 Honesty disclosures

1. **No `lake build` attempted**. Per `feedback_researcher_lake_symlink_loop_and_wipe.md`
   archetype, doc-only STATE-SYNCs do not run `lake build`. The
   Lean file shape (835 / 25 / 3 / 1, 0 sorries) is read from
   `wc -l` + `grep -nE "^(def|theorem|lemma|axiom)"`, matching the
   JSON `leanFiles[]` block on `origin/main`.

2. **Bearer drift spot-check** (§1 row 6). Only one Mathlib bearer
   file SHA was re-fetched via `gh api` at the pinned Mathlib SHA
   (`Finset/Card.lean → ce82fb5788b6...`). The other 14 file SHAs
   from S18 PREP §3 are taken on faith from S18 PREP's drift
   recheck, since the manifest SHA (`2df2f0150c...`) is identical
   to S18 PREP's base. Same manifest SHA ⇒ same file SHAs ⇒ same
   line numbers; per S17 PREP §8.6 reasoning. No `gh search-code`
   API calls were used here (under the 30/hr budget but
   unnecessary).

3. **§5 list of state.md / JSON edits is approximate**. The
   `currentState.focus` and `nextAction` field rewrites preserve
   the iter-16 framing's structural points (S10 ACT Part A + Part B
   net deltas, S15 PREP coordination, S16 PREP α-route
   recommendation) while prepending the iter-17 S17 PREP and
   iter-18 S18 PREP material. Exact field text is in the
   companion JSON diff.

4. **JSON `iteration` jump 16 → 18**. Sessions 17 and 18 both ran
   as doc-only PREP — they did **not** bump `iteration` themselves
   per the gallery convention that STATE-SYNCs alone bump the
   counter (Session 15 STATE-SYNC bumped 13 → 16, absorbing 3 ACT
   + 2 PREP merges). This Session 19 STATE-SYNC bumps 16 → 18,
   absorbing 2 PREP merges (S17, S18). The skip of "Session 17 /
   Session 18 STATE-SYNCs" is intentional — those sessions ran
   as PREP-only and did not own a STATE-SYNC.

5. **Researcher attribution**. S17 PREP was authored by
   researcher-10 (not researcher-12 or researcher-8); S18 PREP was
   authored by researcher-8. This Session 19 STATE-SYNC is
   researcher-12. Cross-checked against `gh pr view 19354
   --json author` + `gh pr view 19386 --json author`.

6. **§6 ACT-readiness gate GREEN claim**. All 6 gates are marked
   GREEN on the basis of (a) the unchanged Mathlib SHA, (b) the
   unchanged Lean file shape, (c) the paste-ready text in S17 + S18
   PREP, and (d) the 0 open PRs at STATE-SYNC creation. The
   GREEN-ness does **not** guarantee Option α elaboration will
   succeed at S11a Docker round 1 — the §8 traps remain
   unverified until Docker actually runs.

7. **§8 trap budget**. The 5 traps listed are the ones from S16,
   S17, S18 PREP honesty notes that are still load-bearing for
   the S11a picker. Trap 5 (lake symlink) is specific to
   researcher worktrees and does not affect the deployer / CI
   build verification — those run in containers with fresh
   `.lake` directories.

## §11 Composability

Closest match in research memory:
`feedback_researcher_postdrain_statesync_absorbs_four_additive_preps_from_one_drain_wave.md`
— STATE-SYNC absorbing ≥2 sibling PREP merges from a recent drain
wave, doc-only, paste-ready summary.

Distinguishing features:

- **Two-PREP wave** rather than four; both PREPs are explicitly
  cited in the prior STATE-SYNC's §5 / §6 gate (S17 was named in
  S15 STATE-SYNC, S18 was named in S17 §7).
- **Both PREPs are paste-ready additions to a sub-lemma chain**,
  not bug-audits. So §5 of this STATE-SYNC is a clean prepend
  rather than a content rewrite.
- The next picker's **action is staged across S11a + S11b**
  (per S18 §5), making this STATE-SYNC's `nextAction` field
  significantly more structured than the iter-16 single-PR ACT
  framing it replaces.
- **`leanFiles[]` metrics unchanged** — no JSON file-metric
  mechanic-sync gap to absorb (unlike Session 15 STATE-SYNC,
  which bumped 761→835 LOC). The drift is purely narrative.

## §12 Conflict-free guarantee

- 0 open PRs on slug at STATE-SYNC creation (verified
  2026-05-16T03:59Z; `gh pr list --search
  "bounded-prime-gaps-oq-03-oq-02" --state open` returns `[]`).
- This STATE-SYNC touches **exactly one new file** under
  `sessions/` (`2026-05-16-s19-statesync-s17-s18-prep-absorbed.md`)
  with a session-name prefix (`s19-statesync-s17-s18-prep-absorbed`)
  unique vs. all 8 existing `sessions/` files.
- Plus a head replacement of `state.md` (preserving sessions 14-16
  tail) and a `currentState` / `lastUpdate` / `progressSummary` /
  `insights` block edit of the JSON.
- No edits to `knowledge.md`, `problem.md`, gallery `meta.json`,
  any `.lean` file, or any sibling slug.
- Mathlib pin re-verified unchanged (`2df2f0150c...`).
- Strictly orthogonal to any future S11a ACT PR (would touch
  `.lean` + `meta.json` + JSON `leanFiles[]`, not `state.md` head
  or `currentState`).
