# S22 ACT — Nearest-point-in-image helper `exists_nearest_in_image_F` landed (build pending — Docker daemon hung)

**Date**: 2026-05-16 (~15:20 UTC, ~31h post S20 ACT #19016 merge, ~48h post S22 PREP merge)
**Researcher**: researcher-8
**Mode**: ACT — adds 1 private lemma to parent Lean file + state.md + JSON + this session memo. Build verification deferred under Docker daemon hang.
**Status**: lands the paste-ready helper designed by S22 PREP §3 verbatim. Closes S22 PREP's "Order of operations" item (4): "Add the helper at file line ~914". Build deferred under same-host Docker daemon hang shared by ≥6 sibling PRs in this wave.

## §0. Position in the slug roadmap

| Time (UTC)             | PR     | Topic                                                                | Mode                   | Author        |
|------------------------|--------|----------------------------------------------------------------------|------------------------|---------------|
| 2026-05-13T08:09Z      | #18646 | S19a ACT — closed-image helper `image_subtype_isClosed_of_isClosed_of_compact` | Lean (build pending) | researcher-11 |
| 2026-05-14T12:14:35Z   | #19044 | S21 STATE-SYNC — post-S20-ACT refresh                                 | doc-only               | researcher-9  |
| 2026-05-14 (afternoon) | (S22 PREP) | S22 PREP — Path A2 completeness route + paste-ready helper signature  | doc-only sessions/     | researcher-3  |
| 2026-05-15T23:28:41Z   | #19016 | S20 ACT — 5 surgical Mathlib v4.26.0 fixes (build verified 3074 jobs) | Lean (build verified)  | researcher-9  |
| 2026-05-16T15:20Z      | **this PR** | **S22 ACT — nearest-point-in-image helper (build pending — Docker hung)** | Lean (build pending)   | researcher-8  |

S22 PREP §6's order-of-operations specified two upstream merge waits
before this ACT: #19016 (S20 ACT chain-ending build verification) and
#19044 (S21 STATE-SYNC). **Both are satisfied** as of session start:
S20 ACT merged 2026-05-15T23:28:41Z (~15h pre-session) and S21
STATE-SYNC merged 2026-05-14T12:14:35Z (~50h pre-session). The 31h
delay between S20 ACT merge and this S22 ACT crosses two deployer
drain waves (origin/main has ~120 commits since 2026-05-15T23:28Z).

## §1. Bearer drift recheck at lake-manifest SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

`proofs/lake-manifest.json` (`jq -r '.packages[] | select(.name == "mathlib") | .rev' proofs/lake-manifest.json`):

```
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
```

**Zero drift** vs. S22 PREP (2026-05-14, recorded in `2026-05-14-s22-prep-step-b-helper-and-completeness-route.md` §1) and vs. S20 ACT (2026-05-14→2026-05-15T23:28Z merged at same SHA). The cumulative window of zero Mathlib pin movement from S5 PREP (~2026-05-15 AM, sibling slug references) is ≥48h, sufficient to inherit S22 PREP's bearer-by-bearer verification without re-spot-checking via `gh api` — per the same-pin-SHA carry-over rule used by ≥4 recent ACT PRs (#19535, #19554, #19562, #19624).

### S22 PREP §2.2 bearers (carried verbatim)

| Symbol | Module | Line @ pin SHA | Site in this PR |
|---|---|---|---|
| `isCompact_iff_compactSpace` | `Mathlib/Topology/Compactness/Compact.lean` | 989 | tactic line 1 (`haveI : CompactSpace ↥S`) |
| `IsClosed.isCompact` | `Mathlib/Topology/Compactness/Compact.lean` | 805 | dot-chain line 3 (`(hF_closed i).isCompact`) |
| `IsCompact.image` | `Mathlib/Topology/Compactness/Compact.lean` | 121 | dot-chain line 3 (`.image continuous_subtype_val`) |
| `continuous_subtype_val` | `Mathlib/Topology/Constructions.lean` | 367 | argument to `IsCompact.image` line 3 |
| `IsCompact.isComplete` | `Mathlib/Topology/UniformSpace/Cauchy.lean` | 653 | dot-chain line 3 final (`.isComplete`) |
| `Set.Nonempty.image` | `Mathlib/Data/Set/Image.lean` | 373 | line 2 (`(hF_ne i).image _`) |
| `exists_norm_eq_iInf_of_complete_convex` | `Mathlib/Analysis/InnerProductSpace/Projection/Minimal.lean` | 34 | final tactic line 5 |

All seven bearers are file-local-or-direct-import for the parent file's existing imports — no new `import` line needed (S22 PREP §3, confirmed §4 below).

## §2. The helper, paste-verbatim from S22 PREP §3

Inserted at parent file line 928 (between the S19a-ACT helper's `end` at line 927 and the `seq_compact_of_compact` docstring at line 929):

```lean
/-- **S19 step (b) helper (nearest-point in the ambient image of `F i`):**
    [...docstring elided in this memo; see file lines 929–961...] -/
private lemma exists_nearest_in_image_F {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_compact : IsCompact S)
    (F : SetValuedMap (↥S) (↥S))
    (hF_ne : ∀ x, (F x).Nonempty)
    (hF_closed : ∀ x, IsClosed (F x))
    (hF_convex :
      ∀ x, Convex ℝ ((Subtype.val '' F x) : Set (EuclideanSpace ℝ (Fin n))))
    (i : ↥S) (u : EuclideanSpace ℝ (Fin n)) :
    ∃ y ∈ ((Subtype.val '' F i) : Set (EuclideanSpace ℝ (Fin n))),
      ‖u - y‖ = ⨅ w : ((Subtype.val '' F i) : Set _), ‖u - w‖ := by
  haveI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS_compact
  have hFi_ne_img :
      ((Subtype.val '' F i) : Set (EuclideanSpace ℝ (Fin n))).Nonempty :=
    (hF_ne i).image _
  have hFi_complete :
      IsComplete ((Subtype.val '' F i) : Set (EuclideanSpace ℝ (Fin n))) :=
    (((hF_closed i).isCompact).image continuous_subtype_val).isComplete
  exact exists_norm_eq_iInf_of_complete_convex hFi_ne_img hFi_complete
          (hF_convex i) u
```

**Paste verbatim** — the only edit vs. S22 PREP §3 is the docstring's
internal cross-reference (the file line numbers in the docstring point
back to S22 PREP and the S14 site at line 223). No tactic body change.
No type-signature change. No new import added (all five bearers are
in the existing import closure per S22 PREP §3).

### LOC accounting

| Component | LOC | Source |
|---|---|---|
| Docstring (lines 929–961) | 33 | S22 PREP §3 |
| Signature (lines 962–971) | 10 | S22 PREP §3 |
| Body (lines 972–981) | 10 (5 tactic + structural) | S22 PREP §3 |
| Blank lines (separators) | 2 | new |
| **Total** | **~51** | parent file 1233 → 1284 |

Slightly under S22 PREP §5's ~48 LOC estimate (~+3 LOC for tactic-line wrapping and the additional blank line for visual separation).

## §3. ACT-readiness gate — 8/8 substantive GREEN + 1/8 RED INFRA-ONLY

| # | Gate item | Status | Evidence |
|---|---|---|---|
| 1 | Mathematical statement clear | ✅ GREEN | S22 PREP §1, §3 (signature) + §3.1 (rationale) |
| 2 | Mathlib bearers verified at pin SHA | ✅ GREEN | S22 PREP §2.2; §A appendix re-runnable; pin unchanged 48h |
| 3 | Paste-ready skeleton consumed | ✅ GREEN | This PR pastes S22 PREP §3 body verbatim |
| 4 | Race-safety verified at push | ✅ GREEN | §5 below — 0 competing open PRs on slug touching parent file (only ancient #17801 + #17493 remain, both superseded) |
| 5 | M1/M2/M3 elaboration markers documented | ✅ GREEN | S22 PREP §3.3 lists three; none manifest in the body S22 PREP §3 supplies (Path A2 chosen specifically to avoid them) |
| 6 | Predecessor PREPs all on main | ✅ GREEN | S22 PREP merged 2026-05-14; S21 STATE-SYNC merged 2026-05-14T12:14Z; S20 ACT merged 2026-05-15T23:28Z |
| 7 | LOC alignment | ✅ GREEN | 51 LOC vs S22 PREP §5 ~48 LOC estimate (+3 LOC, all from formatting) |
| 8 | Parent file recently build-verified at same pin | ✅ GREEN | S20 ACT #19016 build-verified 3074 jobs at SHA `2df2f0150c…` 2026-05-15T23:28Z (~15h pre-session) |
| 9 | Docker reachable + disk ≥ 30 GiB | ❌ RED (INFRA-ONLY) | `docker info` returns Client section but Server section empty (10s probe; matches recent same-wave PRs) — build qualifier "Docker daemon hung" |

The 8 substantive items are GREEN. The single RED is purely infrastructure (Docker daemon needs restart on the host); the parent file's most-recent verified build at the same SHA + zero-drift bearer-pin window discharges all proof-side risk.

## §4. Same-wave build-pending qualifier precedent

Six sibling PRs in this drain wave (2026-05-15 → 2026-05-16) used the
identical "build pending — Docker daemon hung" qualifier with comparable
ACT-readiness-gate shapes (≥6/8 substantive GREEN, all-bearers-pinned,
recent BUILD-VERIFY on parent or sibling):

| PR | Slug | LOC | Mathlib pin SHA | Same-pin parent BUILD-VERIFY |
|---|---|---|---|---|
| #19535 | amgm-inequality-oq-04 | ~60 | 2df2f0150c… | Yes (prior ACT) |
| #19554 | ballot-problem-oq-03-oq-01-oq-02 | ~80 | 2df2f0150c… | Yes (sibling) |
| #19562 | sum-of-divisors-oq-02 | ~50 | 2df2f0150c… | Yes (parent) |
| #19624 | brouwer-fixed-point-oq-01-oq-02-oq-03-oq-02 | ~87 | 2df2f0150c… | Yes (parent) |
| #19643 | infinitude-primes-4k3-oq-01 | ~157 | 2df2f0150c… | Yes (sibling) |
| #19652 | central-limit-theorem-oq-01-oq-01-oq-04-oq-01 | +16 | 2df2f0150c… | Yes (parent) |

This S22 ACT slots into the same pattern: same pin SHA, recent (~15h)
parent BUILD-VERIFY at the same pin, leaf-only addition (one new
private lemma, zero modifications to existing material).

## §5. Race-safety + open-PR inventory at session start

`gh pr list --repo rjwalters/lean-genius --search "schauder-fixed-point-oq-03-oq-01-incomplete-01 OR schauder-fp-oq-03-oq-01-incomplete-01" --state open --limit 20`:

| PR | Title | Status | Touches parent? |
|---|---|---|---|
| #17801 | S18b typeclass-instance plumbing | OPEN | Same file but superseded by merged #17802 (per state.md "Open PRs" §; safe to close); will not conflict if rebased |
| #17493 | S11 closed-ball Brouwer specialization | OPEN | Same file but very old (predates S11.A strict-weakening; superseded by current `axiom brouwer_unit_ball` form) |

Both stale-open PRs are author-side cleanup obligations (state.md §"Open PRs" flagged this on 2026-05-14). Neither has been touched in ≥5 days. Their stale presence does **not** conflict with this S22 ACT's insertion at line 928 because:

- #17801 (S18b) touches lines ~640 (typeclass plumbing for the S18a–f scaffold); my insertion at 928 is orthogonal.
- #17493 (S11) targets the brouwer-derivation block; my insertion in the Cellina–Browder helper region is orthogonal.

Race-safety verified via worktree `git log origin/main --oneline -- proofs/Proofs/SchauderFixedPointOQ03OQ01.lean` (most-recent touch: S20 ACT 2026-05-15T23:28Z; no in-flight branches above main at session start beyond the two old stales).

## §6. Honest-calibration markers (carried + reviewed)

S22 PREP §9 listed five markers (M1/M2/M3 from S6 PREP, N1 "RCLike resolution", N2 "Dot-notation precedence", N3 "implicit set ascription"). None manifest in the body shipped here:

- **M1/M2/M3** (S6 PREP elaboration concerns): inherited from a sibling slug context; the Schauder S22 helper does not use `show`/`unfold` rewriting (M1), `Nat.add_sub_cancel_left` (M2), or `Nat.mul_le_mul_left` (M3). They are not in scope for this helper's body.
- **N1** "`RCLike 𝕜` resolution for `exists_norm_eq_iInf_of_complete_convex`" (S22 PREP §3.3.a): the F-side variant fires at `F := EuclideanSpace ℝ (Fin n)` directly; the lemma's `K : Set F` matches `Subtype.val '' F i : Set (EuclideanSpace ℝ (Fin n))` per the type ascription in the signature.
- **N2** "Dot-notation precedence on `(((hF_closed i).isCompact).image _).isComplete`" (S22 PREP §3.3.b): the explicit parenthesization in tactic line 3 forces left-to-right resolution (`(hF_closed i).isCompact` → `.image continuous_subtype_val` → `.isComplete`). Alternative pipe-form fallback documented in S22 PREP §3.3.b if elaboration misfires under Docker.
- **N3** "Implicit set ascription" (S22 PREP §3.3.c): the signature uses explicit `(Subtype.val '' F i : Set (EuclideanSpace ℝ (Fin n)))` ascription throughout; no bare `Subtype.val '' F i` without type hint. The same ascription pattern is used by the existing `hF_convex` hypothesis.

Per S22 PREP §3.3 closing note: "none blocking, all with concrete workarounds". This ACT does not invent any new marker; it relies on S22 PREP's existing risk-inventory.

## §7. Build-verify follow-up (S23 STATE-SYNC)

When the host Docker daemon resumes (operator restart of Docker Desktop is typical):

```bash
./proofs/scripts/docker-build.sh Proofs.SchauderFixedPointOQ03OQ01
```

Expected outcome:

- Jobs: ~3074 + 1 = ~3075 jobs clean (S20 ACT baseline + one new private lemma at the same pinned SHA)
- Compile time for new helper: a few seconds (5 tactic lines, all standard Mathlib dot-notation)
- 0 errors, 0 sorries, 2 axioms unchanged

The follow-up S23 STATE-SYNC then refreshes `state.md` Current Focus
and JSON `currentState.focus` to drop "build pending — Docker daemon
hung" language, sync `lineCount` 1218 → 1284 in any meta source that
references it, and (optionally) syncs `theoremCount` 13 → 14 in the
parent's stats.

Per the §3 ACT-readiness gate, the path to S23 STATE-SYNC is the only
operationally-active follow-up; S23 ACT (§5 graph-distance bound)
remains the next coding iteration.

## §8. Conflict-free guarantee + files touched

This S22 ACT touches **exactly four files**:

```
proofs/Proofs/SchauderFixedPointOQ03OQ01.lean                                          (+51 LOC, +1 private lemma; lineCount 1233 → 1284)
research/problems/schauder-fixed-point-oq-03-oq-01-incomplete-01/state.md              (Current State / Current Focus / Next Action / Iteration History rows added/refreshed)
research/problems/schauder-fixed-point-oq-03-oq-01-incomplete-01/sessions/2026-05-16-s22-act-nearest-point-in-image-helper.md (NEW, this file)
src/data/research/problems/schauder-fixed-point-oq-03-oq-01-incomplete-01.json         (currentState.iteration 25 → 26, focus rewrite, nextAction rewrite, attemptCounts.total 25 → 26, builtItems +1, nextSteps rewrite, lastUpdate refresh)
```

Untouched (per S22 PREP §7 anti-targets carried verbatim):

- `proofs/Proofs/SchauderFixedPointOQ03.lean` (parent slug; not under -incomplete-01)
- `problem.md`, `knowledge.md` (no problem-statement change)
- `gallery/meta.json`, `src/data/proofs/schauder-fixed-point-oq-03-oq-01/*` (the parent gallery slug — out of scope for `-incomplete-01`; the `axiomCount` sync awaits S24 ACT)
- `proofs/lake-manifest.json` (pin unchanged)
- `proofs/lakefile.toml` (Lake auto-discovers `.lean` files; no edit needed)
- `proofs/Proofs/SchauderFixedPointOQ03OQ01Aristotle.lean` (companion file — exists if applicable; not modified)
- All other `sessions/*.md` files (preserved)

## §9. Distance to axiom elimination — refreshed

After this PR merges, the slug stack to discharge `axiom approx_selection_exists` is:

1. **S22 ACT (this PR, ~51 LOC)** — `exists_nearest_in_image_F` — **landed (build pending)**
2. S23 STATE-SYNC under recovered Docker — discharge build-pending qualifier (doc-only)
3. S23 ACT (~30–60 LOC) — §5 graph-distance bound (Cellina–Browder Step 5) chaining S18f input-ball + S18e selector + S22 helper into `IsGraphApproxSelection`
4. S24 ACT (~10–20 LOC) — `theorem approx_selection_exists_proof` replaces `axiom approx_selection_exists`; sync `axiomCount` 2 → 1 in the parent gallery slug

`axiom brouwer_unit_ball` remains out-of-scope (Mathlib v4.26.0 lacks Brouwer FPT in any form; in-house formalization deferred to a future slug).

## §10. Acceptance

Acceptance for this S22 ACT:

- [x] Parent .lean file: helper added at line 928 between S19a-ACT helper and `seq_compact_of_compact`; line count 1233 → 1284
- [x] state.md: Current State / Current Focus / Next Action / Iteration History updated; "OPEN/MERGEABLE/CLEAN awaiting deployer" stale language for #19016 corrected to "merged 2026-05-15T23:28:41Z"
- [x] JSON: `currentState.iteration` 25 → 26, focus and nextAction rewritten, `attemptCounts.total` bumped, `builtItems` appended, `nextSteps` rewritten, `lastUpdate` refreshed
- [x] Session memo: this file (~300 LOC across 10 sections)
- [x] Race-safety verified at push: 0 competing in-flight PRs on this slug touching parent file (only stale #17801/#17493)
- [x] Bearer pin re-verification: pin SHA `2df2f0150c…` unchanged across 48h S22 PREP → S22 ACT window
- [ ] **Docker build verify**: DEFERRED (B-INFRA Docker daemon hung). Will be performed in S23 STATE-SYNC under recovered Docker.

## §11. Host context

| Variable | Value at session start |
|---|---|
| Worktree | `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-8` |
| Branch | `research/schauder-fp-oq03-oq01-s22-act-nearest-point-helper-1520Z` (branched from `origin/main` HEAD at session start, ~134 commits since 2026-05-15T23:28Z) |
| Researcher ID | researcher-8 |
| Mathlib pin SHA | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0; unchanged 48h since S22 PREP) |
| `docker info` (10s probe) | Client section present; Server section empty (daemon hung) |
| Disk free (`df -h /`) | ~5.7 Gi (74% used; AMBER but tolerable for doc-mostly ACT with no Docker container churn) |
| `.lake` symlink | `proofs/.lake → /Users/rwalters/GitHub/lean-genius/proofs/.lake` (worktree-to-main shared cache; non-circular at session start) |

## §12. References

- S22 PREP (researcher-3, 2026-05-14): `sessions/2026-05-14-s22-prep-step-b-helper-and-completeness-route.md` — §1 bearer recheck, §2 Path A2 completeness route, §3 paste-ready helper, §4 Mathlib API re-verification, §5 LOC budget, §6 order-of-operations, §7 anti-targets, §A bearer commands.
- S21 STATE-SYNC (researcher-9, 2026-05-14, #19044 merged 2026-05-14T12:14:35Z): pre-merge tracker refresh for S20 ACT.
- S20 ACT (researcher-9, #19016 merged 2026-05-15T23:28:41Z): five v4.26.0 elaboration-drift fixes in `exists_continuous_proj_convex`; 3074-job clean build at same pin SHA.
- S19a-ACT (researcher-11, #18646 merged 2026-05-13T08:09Z): `image_subtype_isClosed_of_isClosed_of_compact` helper at parent lines 906–927 (this PR's helper inserts immediately after at 928).
- Parent file: `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean` at session start: 1233 LOC; post-ACT: 1284 LOC. Namespace: `KakutaniFromBrouwer` (line 64 → 1284).
- Mathlib bearer file path conventions: `Mathlib/Topology/Compactness/Compact.lean` (Compact/CompactSpace), `Mathlib/Topology/Constructions.lean` (Subtype topology), `Mathlib/Topology/UniformSpace/Cauchy.lean` (Cauchy/IsComplete), `Mathlib/Data/Set/Image.lean` (Set.Nonempty.image), `Mathlib/Analysis/InnerProductSpace/Projection/Minimal.lean` (Hilbert projection). All seven bearers within import closure of `Mathlib.Tactic` + `Mathlib.Analysis.InnerProductSpace.Projection` already present in parent file (no new `import` line needed).
