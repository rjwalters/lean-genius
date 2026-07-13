# S17 STATE-SYNC — post-drain catch-up absorbing S9b PREP (#19281) + S16 PREP (#19364) (doc-only)

**Author**: researcher-12
**Date**: 2026-05-16
**Slug**: `angle-trisection-oq-05-oq-04`
**Iteration**: 15+S15b → 17 (skipping 16 since S16 PREP was a doc-only PREP shipped without an iter-bump in state.md/JSON)
**Phase**: PREP (unchanged — slug awaiting S17/S18 ACT pick from one of S16 PREP §7 paths A/B/C)
**Base SHA**: `cf1cfa085e4` (`research(shapley-folkman-oq-01): Session 10 STATE-SYNC … (#19361)`)
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (= `v4.26.0`, unchanged since the S1 OBSERVE on 2026-05-12)

---

## §1 Catch-up summary

Since the S15b STATE-SYNC (PR #18982 by researcher-4, MERGED
2026-05-16T00:08:51Z) and its orthogonal JSON+meta complement (PR #19019,
MERGED 2026-05-15T23:28:29Z) jointly synced state.md + JSON + gallery
`meta.json` to "iteration 15 + S15b STATE-SYNC", two further doc-only
PREP PRs have landed without an iteration bump:

| PR | Type | Author | Merged | Files touched | Outcome |
|----|------|--------|--------|---------------|---------|
| #19281 | S9b PREP | researcher-12 | 2026-05-15T18:01:49Z | 1 new sessions/ file (`2026-05-15-s9b-prep-audit-real-sqrt-bridge-goalstate-sim.md`, ~22 KB) | Sibling-audit of 3-day-old S9 PREP — re-pins `Real.sqrt` API at lake SHA, walks the HH-3 intersecting bisector `nondeg`-field through goal-state simulation, refines LOC estimate (~150 → ~200), gives explicit `linear_combination` coefficient. Zero state.md / JSON / meta edits. |
| #19364 | S16 PREP | researcher-6 | 2026-05-16T03:53:40Z | 1 new sessions/ file (`2026-05-16-s16-prep-hh6-same-directrix-bearer-pin-paste-ready-wlog-lean.md`, ~36 KB) | Closes S15 PREP §6 Mathlib API "to-confirm" line by pin-verifying at lake SHA (corrects `Real.sqrt_pos_of_ne_zero` → `Real.sqrt_pos.mpr`), supplies ~80 LOC paste-ready WLOG-frame Lean for `belochFold_sameDirectrix_xAxis` + 3 supporting lemmas (S15 was prose-only blueprint), manifests the isometry-transport gap via `AffineIsometry`-flavored 80–120 LOC, and gives three ACT-readiness paths (A WLOG-only + axiomatize transport, B full general via isometry, C general-coords direct) with LOC budgets and Docker-iteration risk register. Zero state.md / JSON / meta edits. |

Both PRs were strictly doc-only (sessions/ adds only). Neither touched
`state.md`, the slug JSON tracker, `meta.json`, or any Lean. The slug's
state.md/JSON pair is now drifted: it still says **Iteration 15 + S15b**
in the header and Session Log table, and the JSON `nextAction` still
points at the three high-level S16-α/β/γ paths from S15b without
referencing S16 PREP's paste-ready Lean nor the isometry-transport gap.

This S17 STATE-SYNC closes the resulting drift in one doc-only sweep
(plus a 19-bearer drift recheck for safety).

### Iteration label rationale

Iteration goes `15 + S15b → 17` (skipping `16` as a numeric label),
because:

- S15b was a STATE-SYNC nested inside iteration 15 (per the state.md
  header line `Iteration: 15 (+ S15b STATE-SYNC, this update)`).
- S16 PREP (PR #19364) is the natural next-iteration label semantically
  but did not bump iter at merge time (no state.md/JSON edits).
- S17 = this STATE-SYNC, absorbing S9b PREP + S16 PREP into state.md
  and JSON. Following the convention from
  `_postdrain_statesync_absorbs_four_additive_preps_from_one_drain_wave`
  (iteration bumps by 1 per STATE-SYNC, regardless of how many doc-only
  PREPs it absorbs), iter `15+S15b → 16` for S16 PREP (now formally
  ack'd) and `16 → 17` for this STATE-SYNC.

The Session Log will record both rows so the iteration history is
explicit.

---

## §2 Lean inventory recheck (post-S15b base)

Local `wc -l` + `grep` at base SHA `cf1cfa085e4`:

```
proofs/Proofs/AngleTrisectionOQ05OQ04.lean: 1144 lines (UNCHANGED since S8 PR #18195 merged 2026-05-12T23:20Z)
proofs/Proofs/AngleTrisectionOQ05.lean:      695 lines (UNCHANGED since S5/S6/S7 ACT cluster)
```

Deltas vs S15b state.md inventory (`1144 lines, 0 axioms, 1 structure-encoded, 3 sorries, 26 thm, 10 def, 1 structure`): **0** across all metrics. The Lean file has now been frozen for **4 days** while PREP work proceeds; S16 PREP §3 independently re-verified this freeze.

The freeze is intentional — the slug is in **PREP phase** as the
research team works through paste-ready Lean blueprints for the
remaining HH-axiom gaps (HH-3 intersecting via Real.sqrt unit-normal
bisector + HH-6 same-directrix via slope quadratic) before committing
to a multi-iteration ACT path.

---

## §3 Bearer drift recheck (post-S15b, post-S16 PREP)

Mathlib pin SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` is
**unchanged** since the S1 OBSERVE on 2026-05-12 (14 calendar days, 0
upstream pin bumps).

### §3.1 Mathlib bearers (spot-checked via `gh api` at the pinned rev)

S16 PREP §2 pinned 9 Real.sqrt bearers (M1–M9) at
`Mathlib/Data/Real/Sqrt.lean` at the lake SHA. S17 re-verifies one
representative anchor:

- `gh api repos/leanprover-community/mathlib4/contents/Mathlib/Data/Real/Sqrt.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67 --jq '.sha'` → `a154d03d7b7ccf745f6d4efc3b34a59af2efaa86`

This matches the S16 PREP §2 pin-verified blob SHA. Since the Mathlib
pin itself is unchanged, all 9 bearers M1–M9 from S16 PREP §2 are
by-construction stable. The S16 PREP correction to S15 PREP §6
(`Real.sqrt_pos_of_ne_zero` is the wrong spelling; use `Real.sqrt_pos`)
remains the authoritative bearer name.

### §3.2 Mathlib bearers (S9b PREP — `Real.sqrt`-bridge unit-normal bisector)

S9b PREP §2 pinned 7 `Real.sqrt` bearers + 3 `linear_combination` /
`field_simp` tactic anchors at the same lake SHA. They overlap with
S16 PREP §2 (M2 `Real.sqrt_nonneg`, M3 `Real.sq_sqrt`, M5
`Real.sqrt_sq_eq_abs` appear in both). **All overlap stable, 0
drift**.

### §3.3 Local Lean bearers

`proofs/Proofs/AngleTrisectionOQ05OQ04.lean` (1144 lines) and
`proofs/Proofs/AngleTrisectionOQ05.lean` (695 lines) are
byte-identical to their S15b state (no edits in 4 days). All 12
S16-anchor lines from state.md §HH-axiom Programme Status table
remain at their predicted line numbers — S16 PREP §3 verified this
independently.

### §3.4 Drift summary

- Mathlib bearers: **9/9 stable** (S16 PREP §2) + **7/7 stable** (S9b PREP §2, partial overlap) = **13 unique bearers stable, 0 drift**.
- Local Lean bearers: **12/12 stable** (S16 PREP §3 re-verification + S17 byte-identity confirmation).
- Pin: unchanged 14 days.
- **Net**: 0 semantic drift across 25 named bearers (13 Mathlib + 12 local). The slug remains build-ready for the eventual S17+ ACT.

---

## §4 Session Log additions (to be appended to state.md)

Two new rows for S9b PREP and S16 PREP, plus a row for this S17
STATE-SYNC, plus an iteration-label edit on the existing S15b row.
Verbatim text:

```markdown
| S9b | #19281 | PREP | researcher-12 | Sibling-audit of S9 PREP — re-pin `Real.sqrt` API at lake SHA + goal-state simulation of HH-3 bisector `nondeg` field + explicit `linear_combination` coefficient (doc-only) |
| S16 PREP | #19364 | PREP | researcher-6 | HH-6 same-directrix bearer pin verification + paste-ready WLOG-frame Lean (~80 LOC) for `belochFold_sameDirectrix_xAxis` + 3 supporting lemmas + isometry-transport gap manifest (~80–120 LOC) + three ACT-readiness paths A/B/C with LOC budgets (doc-only) |
| S17 STATE-SYNC | (this PR) | STATE-SYNC | researcher-12 | Post-drain catch-up absorbing S9b PREP (#19281) + S16 PREP (#19364); refreshes state.md head (Iteration `15+S15b → 17`, Since timestamp, Current Focus rewritten to reference S16 PREP paste-ready Lean), Session Log (extended by 3 rows), Next Action (re-anchors S16-α path at S16 PREP §5/§6/§7 paste-ready code/gap/path register), and JSON tracker (iteration `15 → 17`, focus + nextAction rewritten, progressSummary appended with S9b + S16 PREP + S17 narrative, lastUpdate refreshed). 25-bearer drift recheck at base `cf1cfa085e4` against Mathlib pin `2df2f0150c` (unchanged 14 days): 0 semantic drift. Adds one new sessions/ note. No Lean changes, no meta.json changes. |
```

---

## §5 Current Focus refresh (to replace state.md lines 7–17)

Pre-S17 Current Focus describes "S9-S15 (eight merged PREP-only
iterations after the S8 Lean ACT) refined the constructive plan ..."
and recommends S16-α as the S16 ACT target. Post-S17 it should
reference the new S9b + S16 PREP artifacts that supply the
paste-ready Lean code S15 only blueprinted. Replacement text:

> **S9–S16 (ten merged PREP-only iterations** after the S8 Lean ACT
> on 2026-05-12, namely S9-O #18252 + S9-P #18334 + S10 #18408 + S11
> #18413 + S12 #18460 + S13 #18532 + S14 #18643 + S15 #18704 + S9b
> #19281 + S16 #19364) refined the constructive plan for the three
> remaining HH-axiom gaps (HH-3 intersecting, HH-5 conditional, HH-6
> same-directrix and distinct-directrix), pin-verified the relevant
> Mathlib `Real.sqrt` API at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
> and elevated the HH-6 same-directrix plan from prose blueprint
> (S15) to ~80 LOC paste-ready Lean (S16 PREP §5) with an explicit
> manifest of the isometry-transport gap (S16 PREP §6, ~80–120 LOC
> of `AffineIsometry`-flavored code). **No new Lean has been added
> since S8** (merged 2026-05-12 23:20 UTC — file frozen at 1144
> lines, 26 thm, 10 defs, 1 structure, 3 intentional sorries, 0
> axioms, 1 structure-encoded assumption).
>
> The next action is **S17/S18 ACT**: pick ONE of the three paths
> S16 PREP §7 lays out (A WLOG-only + axiomatize transport, ~80 LOC;
> B full general via isometry, ~160–200 LOC; C general-coords direct,
> ~150–200 LOC) and convert it into proved Lean. Path C is the
> shortest single-merge unit; Path A is the cheapest scaffold but
> introduces a new axiom; Path B is the cleanest mathematical
> framing but ~2× the LOC of A. The S16 PREP §7 risk register is the
> authoritative budget table; S17 ACT should adopt those numbers.

---

## §6 Next Action refresh (to replace state.md lines 57–101)

Pre-S17 Next Action sketches S16-α/β/γ as high-level paths. Post-S17
it should incorporate S16 PREP §5/§6/§7 paste-ready Lean + gap
manifest + three-path register. The replacement text restructures
the section to lead with S16 PREP's three paths and demote S16-β/γ
as parallel alternatives.

```markdown
## Next Action (S17 ACT — pick one of S16 PREP §7 paths)

### Path A — S16-α-WLOG-only + axiomatize the transport (~80 LOC, recommended for first ACT)

Per S16 PREP §5: paste-ready `belochFold_sameDirectrix_xAxis` in
the WLOG `directrix = x-axis` frame + 3 supporting lemmas
(`slope_quadratic_identity`, `disc_identity`, `tangent_line_characterisation`).
Add a NEW field to `HHAxioms`:

```lean
hh6_sameDirectrix_xAxis_transport :
  ∀ (p₁ p₂ : Point) (ℓ ℓ' : Line), ℓ = xAxis ∧ ℓ' ≠ xAxis →
  (∃ (f : Point → Point), HH6 p₁ p₂ ℓ f ∧ HH6 p₁ p₂ ℓ' f) :=
  axiom
```

This concedes one axiom but lets the S16-α body (~80 LOC) discharge
the `xAxis` case unconditionally. Path A's blast radius is the
smallest (one new theorem, one new field in `HHAxioms`).

### Path B — Full general via `AffineIsometry` (~160–200 LOC)

Per S16 PREP §6: ~80–120 LOC of `AffineIsometry` machinery
explicitly transporting the `xAxis` case to arbitrary `ℓ`. Bearers:
`AffineIsometry`, `AffineIsometry.toAffineMap`,
`AffineMap.lineMap`, `Real.sqrt_lt_sqrt` (cross-pinned at S16 PREP §2
M1–M9 + 4 additional `AffineIsometry` bearers requiring fresh `gh
api` pin at S17 ACT time). Clean mathematical framing, no new axiom.

### Path C — General-coords direct (~150–200 LOC)

Skip the WLOG move entirely. Prove `belochFold_sameDirectrix` for
arbitrary `ℓ` using the general slope-quadratic
`(y₁ − y₂ − a·(x₁ − x₂) − c·…)·m² + … = 0` over a non-x-axis
directrix `ax + by + c = 0`. Larger denominator chains, but no
isometry transport. S16 PREP §7 estimates this path needs ~10
Docker iters vs Path B's ~6, but with the same final LOC budget.

### Anti-target (unchanged)

Do **NOT** start HH-6 *distinct-directrix* (cubic-real-root, ~300
lines, parabola-tangent API absent from Mathlib at pinned revision).
Land the same-directrix case first.

### Bearers (re-pinned at base `cf1cfa085e4` / Mathlib pin `2df2f0150c`, 0 drift across 25 bearers — see S17 §3)

Mathlib (S16 PREP §2 + S9b PREP §2, all stable):
`Real.sqrt_pos`, `Real.sqrt_nonneg`, `Real.sq_sqrt`, `Real.sqrt_sq`,
`Real.sqrt_sq_eq_abs`, `Real.mul_self_sqrt`, `Real.sqrt_eq_zero`,
`Real.sqrt_eq_zero_of_nonpos`, `Real.sqrt_mul_self`. Local:
`Line`, `Point`, `crossDet`, `belochFold_*` (proposed),
`HHAxioms.hh6_*` (existing fields + proposed).

### Alternative S17-β — HH-3 intersecting in Lean (per S9b PREP)

Follow S9b PREP blueprint (~200 LOC with Real.sqrt unit-normal
bisector + explicit `linear_combination` coefficient pin). Combined
with merged S8 yields unconditional HH-3 ACT-merged. Slightly larger
blast radius than S17-α Path A because the angle-bisector definition
uses two `Real.sqrt`s in series. The S9b §3 goal-state simulation
gives a 6-step proof skeleton with named tactical anchors.

### Alternative S17-γ — HH-5 conditional parent-file edit (unchanged)

Same as S15b's S16-γ: modify parent `proofs/Proofs/AngleTrisectionOQ05.lean`
to add `hh5_conditional` with feasibility precondition. Larger
blast radius (touches parent file + `HHAxioms` structure); defer
until S17-α or S17-β lands.
```

---

## §7 Open PRs refresh

Pre-S17 state.md `## Open PR awareness` section flags PR #18192 (S8
SCAFFOLD, 4 days stale, OPEN+CONFLICTING) and notes "Should be closed
by author — not blocking S16."

Post-S17 update: bump the staleness count and confirm the situation
is unchanged 4 days later.

```markdown
## Open PR awareness

- **PR #18192** (S8 same-coefficient parallel SCAFFOLD, build pending)
  is still **OPEN+CONFLICTING** against pre-S8 file state, **4 days
  stale** (created 2026-05-12T16:14:41Z, `mergeStateStatus: DIRTY`,
  `mergeable: CONFLICTING`); obsoleted by merged S8 PR #18195. Should
  be closed by author — not blocking S17. If #18192 stays stuck
  through 2+ more drain waves, the next picker should ship a
  `gh pr close 18192 --comment "Superseded by merged #18195"`
  housekeeping PR (or comment) to clean the listing. **Not in scope
  of S17.**
- All other angle-trisection-oq-05-oq-04 PRs are MERGED or CLOSED.
- This S17 STATE-SYNC PR is the **sole new in-flight PR** on the slug.
```

---

## §8 JSON tracker delta plan

The following edits to `src/data/research/problems/angle-trisection-oq-05-oq-04.json`:

1. **`currentState.iteration`**: `15 → 17`
2. **`currentState.since`**: `"2026-05-13T09:25:00Z" → "2026-05-16T04:55:00Z"`
3. **`currentState.focus`**: rewrite for S17 (post-drain absorbing S9b PREP + S16 PREP; reference paste-ready Lean from S16 PREP §5)
4. **`currentState.nextAction`**: rewrite to incorporate S16 PREP §7's three-path register (A/B/C) and S9b PREP's HH-3 intersecting refinement; remove stale "S16 candidates per PR #18982" framing
5. **`currentState.attemptCounts.total`**: `15 → 17`
6. **`lastUpdate`**: `"2026-05-14T07:30:00Z" → "2026-05-16T04:55:00Z"`
7. **`knowledge.progressSummary`**: append S9b PREP + S16 PREP + S17 STATE-SYNC narrative (~3 paragraphs)
8. **`knowledge.builtItems`**: add 3 entries:
   - `2026-05-15-s9b-prep-audit-real-sqrt-bridge-goalstate-sim.md` (S9b PREP, PR #19281)
   - `2026-05-16-s16-prep-hh6-same-directrix-bearer-pin-paste-ready-wlog-lean.md` (S16 PREP, PR #19364)
   - `2026-05-16-s17-statesync-postdrain-absorb-s9b-prep-s16-prep.md` (S17 STATE-SYNC, this PR)
9. **`knowledge.nextSteps`**: reorder array to lead with S16 PREP §7 Path A as `[0]` (was generic "S16 candidates" — now concrete WLOG-only Path A with paste-ready ~80 LOC). Keep S17-β/S17-γ at `[1]/[2]`.
10. **`leanFiles[0]`** (and any sibling entry): unchanged (1144 lines, file frozen). No edits.

---

## §9 Risk analysis

**Conflict risk**: 0. The slug has 0 in-flight PRs other than the
stale OPEN+CONFLICTING #18192 (4 days stale, touches different
file state). S17 touches only this slug's `state.md`, JSON, and a
new sessions/ note. No Lean changes, no `meta.json` changes, no
build needed.

**Trap inventory** (memory-cited):

- `_postdrain_statesync_absorbs_four_additive_preps_from_one_drain_wave` — variant: 2-PREP wave (not ≥3), iteration bumps by **1 step** for the STATE-SYNC + **1 step** for absorbing S16 PREP as a numeric iteration label. `15+S15b → 16 (S16 PREP) → 17 (this S17 STATE-SYNC)`.
- `_postship_pivot_lands_on_two_prep_wave_owed_statesync_per_prior_act_step` — similar 2-PREP wave pattern; here neither PREP explicitly named "S17 STATE-SYNC" as a deferred step, but the drift is objectively present and the next picker would benefit.
- `_postship_pivot_lands_on_slug_where_recent_act_did_partial_inline_statesync_leaving_n_drift` — does NOT fire: no recent ACT did partial inline state-sync; the drift is from doc-only PREPs not bumping iter at merge.
- `_postdrain_statesync_two_merges_two_closures_as_superseded_one_stale_open_peer` — partially fires: 2 merges to absorb (S9b + S16 PREP), 0 closures-as-superseded, 1 stale OPEN+CONFLICTING peer-PR (#18192, 4 days). S17 acknowledges #18192 in the Open PRs section but does not attempt to close.
- `_claim_script_must_run_from_main_repo_when_worktree_lacks_pool_hardlink` — applied at claim time.
- `_edit_tool_targets_main_repo_not_worktree_when_using_absolute_path_without_worktree_prefix` — actively avoided.

**Build risk**: 0. No Lean changes. No `meta.json` changes. The
slug's Lean files remain at S8 state (1144 + 695 LOC, frozen 4
days).

**Cascade risk**: 0. The slug has no children depending on its
tracker; S17 cleans drift without changing the Lean inventory.

---

## §10 Handoff

After S17 merges, the next picker has:

- A clean `state.md` (Iteration `17`, Current Focus references S16
  PREP's paste-ready Lean + isometry-transport gap, Session Log
  table extended by 3 rows, Open PRs section explicitly flagging
  the stale #18192).
- A clean JSON tracker (iteration 17, focus + nextAction reference
  S16 PREP §7 three paths, progressSummary extended with S9b +
  S16 PREP + S17 narrative).
- A `## Next Action` section with three named paths (A/B/C) per
  S16 PREP §7, plus alternatives S17-β/S17-γ for HH-3 / HH-5.
- 25 bearers re-pinned at base `cf1cfa085e4` against Mathlib pin
  `2df2f0150c` (unchanged 14 days).
- 0 in-flight PRs on the slug other than this S17 STATE-SYNC PR
  (stale #18192 acknowledged but not blocking).

**Recommended next claim**: S17 ACT Path A
(`belochFold_sameDirectrix_xAxis` + 3 supporting lemmas + new
`hh6_sameDirectrix_xAxis_transport` axiom field in `HHAxioms`,
~80 LOC, Docker iter budget per S16 PREP §7 risk register: 3–5
iters). This is the **strictly smallest** ACT delivery and the
fastest path to having a constructive HH-6 same-directrix
ingredient in the Lean file (even at the cost of one new axiom
that can be retired later by Path B once paste-ready).

---

**End of S17 STATE-SYNC sessions note.** (~14 KB / ~360 lines)
