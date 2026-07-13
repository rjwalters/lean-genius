# S9b PREP — Deployer-Stall Coordination + 3-Way Merge Sequencing

**Date**: 2026-05-15
**Author**: researcher-9
**Phase**: ACT (no phase change)
**Iteration**: 8 (no iteration bump — coordination doc only)
**Class**: deployer-stall coordination PREP (doc-only, conflict-free)

## §1. Situation

The next-action target in `state.md` (S9 — prove `cbrt3_a7 = 1`) has
**three open MERGEABLE+CLEAN PRs** queued against the deployer:

| PR | Author | Title | Files touched | Created |
|---|---|---|---|---|
| #19011 | researcher-12 | S9-prep MATH-CORRECTION — `a₈ = 1` (not 4); proposed lower bound `949/658` not `2485/1723` (doc-only) | `state.md`, `knowledge.md`, slug JSON | 2026-05-14T06:33Z |
| #19039 | (Robb Walters) | S9 ACT — eighth partial quotient `a₇=1` via `949/658 < cbrt3 < 512/355` (build verified, 7745 jobs) | both Lean files, `state.md`, slug JSON, **new** `sessions/2026-05-14-s9-act-eighth-partial-quotient.md` | 2026-05-14T11:49Z |
| #19057 | (Robb Walters) | S9 ACT — `a₇=1` via convergent `949/658` (build verified); corrects `a₈` math | both Lean files, `state.md`, slug JSON | 2026-05-14T13:55Z |

All three are CLEAN+MERGEABLE at the time of this PREP (2026-05-15T02:05Z),
~23 h into a system-wide deployer stall (see §5).

## §2. Math (canonical, per all 3 PRs)

The corrected OEIS A002945 prefix is `[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, …]`, so
`a₈ = 1` (not `4`). The eighth CF convergent is therefore

```
p₈ = a₈·p₇ + p₆ = 1·512 + 437 = 949
q₈ = a₈·q₇ + q₆ = 1·355 + 303 = 658
p₈/q₈ = 949/658 ≈ 1.4422492401  <  cbrt3 ≈ 1.4422495703   ✓ (even-index, below)
```

Cube check (lower bound): `949³ = 854_670_349`, `3·658³ = 854_670_936`,
diff `+587 > 0` ⟹ `(949/658)³ < 3` ⟹ `949/658 < cbrt3`.

Upper bound reused from S8 (PR #18932, merged): `cbrt3 < 512/355`,
cube diff `+1103`.

The (incorrect) prior S8 sketch proposed `2485/1723` (using `a₈ = 4`).
Direct cube: `2485³ = 15_345_434_125`, `3·1723³ = 15_345_360_201`,
diff `+73_924` ⟹ `2485/1723 > cbrt3`, i.e. WRONG SIDE for a lower bound.
All three PRs agree on this correction.

## §3. PR-by-PR triage

### PR #19011 — MATH-CORRECTION (doc-only, researcher-12)

- **Status**: CLEAN+MERGEABLE, age 19.5 h.
- **Lean diff**: zero.
- **State.md diff**: rewrites `## Next Action` block to use `949/658`;
  appends `## S9-prep MATH-CORRECTION` footnote (~+170 LOC).
- **Knowledge.md diff**: appends `## S9-prep MATH-CORRECTION` section.
- **Subsumption**: **subsumed by both #19039 and #19057** — the next
  action sketch it corrects is itself rewritten by either ACT.
- **Independent value**: documents the math error (50-digit `Decimal`
  computation, sign-of-bound proof, methodological lesson) for the
  knowledge.md/insights trail. The footnote in state.md and the
  knowledge.md addition do **not** appear in either ACT.

### PR #19039 — S9 ACT (build verified, Robb Walters via researcher)

- **Status**: CLEAN+MERGEABLE, age 14.2 h.
- **Lean diff**: +245 LOC `CubeRoot3IrrationalOQ04.lean` (new
  theorem `cbrt3_a7` + prose section) + ~+30 LOC `Helpers.lean`
  (new lemma `nine_forty_nine_over_six_fifty_eight_lt_cbrt3`).
- **Build**: `./proofs/scripts/docker-build.sh Proofs.CubeRoot3IrrationalOQ04`
  succeeds with 7745/7745 jobs.
- **Extra**: includes new `sessions/2026-05-14-s9-act-eighth-partial-quotient.md`
  (~120 LOC session report).
- **Total**: +562/-55 LOC across 5 files.

### PR #19057 — S9 ACT (build verified, Robb Walters via researcher)

- **Status**: CLEAN+MERGEABLE, age 12.1 h.
- **Lean diff**: +245 LOC `CubeRoot3IrrationalOQ04.lean` (new
  theorem `cbrt3_a7` + prose section + `set_option maxHeartbeats 800000 in`
  on the main theorem) + ~+53 LOC `Helpers.lean` (same new lemma).
- **Build**: same Docker target, 7745/7745 jobs.
- **Extra**: explicitly forward-projects S10 next-action in `state.md`
  with the 9th CF convergent `6206/4303` (using `a₉ = 6` per OEIS).
- **Total**: +468/-81 LOC across 4 files (no `sessions/` file).

### Duplication summary

`#19039` and `#19057` are **content-equivalent** — both prove the same
target via the same helper and the same 13/14-step linarith chain, in
the same two Lean files. The differences are local:

- `#19057` adds `set_option maxHeartbeats 800000 in` on `cbrt3_a7`
  (the septuple-nested goal needs more heartbeats than the default
  `200_000`); `#19039` does not, suggesting either (a) different
  factoring of intermediate `have` steps that kept the goal under
  `200_000` heartbeats, or (b) a stale-baseline build at the time of
  #19039 that didn't surface the heartbeat issue.
- `#19057` forward-projects S10 (`a₈ = 1`, 9th convergent `6206/4303`
  as upper bound) in `state.md`; `#19039` leaves S10 implicit.
- `#19039` writes a `sessions/` session report; `#19057` does not.

Both Lean payloads are mathematically equivalent — the eighth partial
quotient is proved once either way.

## §4. File-overlap matrix

| File | #19011 | #19039 | #19057 | This PREP |
|---|---|---|---|---|
| `proofs/Proofs/CubeRoot3IrrationalOQ04.lean` | — | ✓ | ✓ | — |
| `proofs/Proofs/CubeRoot3IrrationalOQ04Helpers.lean` | — | ✓ | ✓ | — |
| `research/problems/cube-root-3-irrational-oq-04/state.md` | ✓ | ✓ | ✓ | — |
| `research/problems/cube-root-3-irrational-oq-04/knowledge.md` | ✓ | — | — | — |
| `src/data/research/problems/cube-root-3-irrational-oq-04.json` | ✓ | ✓ | ✓ | — |
| `research/problems/cube-root-3-irrational-oq-04/sessions/2026-05-14-s9-act-…md` | — | ✓ (new) | — | — |
| `research/problems/cube-root-3-irrational-oq-04/sessions/2026-05-15-s9b-prep-deployer-stall-coord.md` | — | — | — | ✓ (this file, new) |

This PREP's single new file is disjoint from every open PR's file set.
**Zero merge-conflict risk** under any sequencing.

## §5. Deployer-stall context

System-wide observation as of 2026-05-15T02:05Z:

- Most recent merge: PR #18980 at `2026-05-14T03:03:38Z`.
- Zero-merge duration: ~23.0 h.
- `gh pr list --state open --limit 50 --json mergeStateStatus | jq '[.[] | select(.mergeStateStatus == "CLEAN")] | length'` → **50** (window saturated).

Same stall is documented in four sister coordination PREPs filed today:

- PR #19193 — brouwer-fixed-point-oq-01-oq-02-oq-03-oq-02 S10 (4-PR cascade)
- PR #19201 — bounded-prime-gaps-oq-03-oq-02 S15
- PR #19205 — circumference-via-differentiation-oq-03 S4 (3-way merge)
- PR #19209 — chebyshev-bounds-oq-04-oq-01 S5 (3-way merge + close-as-superseded)

(MEMORY: `feedback_researcher_deployer_stall_coordination_prep_pattern.md`.)

## §6. Recommended post-stall merge sequence

### Option A (chronological, preserves all attribution; recommended)

1. **Merge #19011** first (oldest, doc-only, smallest diff).
   - Lands the math-correction footnote in `state.md` + the knowledge.md
     methodological lesson. These are not in either ACT PR.
2. **Merge #19039** second (second-oldest ACT, ships the Lean payload).
   - State.md/JSON will conflict-resolve against #19011's footnote
     additions: #19011's content lives in the appended footnote section,
     #19039's content rewrites `## Current Focus` and the `## Next Action`
     block. The two are mechanically disjoint (different sections);
     a 3-way merge succeeds, but the maintainer should hand-verify that
     #19011's footnote survives.
3. **Close #19057** with the comment template:
   > Closing as superseded by merged PR #19039 (content-equivalent S9 ACT:
   > same `cbrt3_a7` theorem, same helper `nine_forty_nine_over_six_fifty_eight_lt_cbrt3`,
   > same 13/14-step linarith chain, both build-verified).
   > The `set_option maxHeartbeats 800000 in` annotation on `cbrt3_a7`
   > (added in this PR but not in #19039) may need to be re-applied as a
   > follow-up if S10 ACT surfaces heartbeat regressions; capture as a
   > 1-LOC follow-up PR rather than a rebase of this one.
   > Forward-projected S10 next-action (`a₈=1`, 9th convergent `6206/4303`)
   > should be reproduced in the next S10 PREP — see this PREP's §7.

### Option B (skip the doc-only fix; simplest)

1. **Merge #19039** alone (lands the canonical S9 ACT with math correction
   subsumed in the rewritten `## Next Action` block).
2. **Close #19011** with the comment template:
   > Closing as superseded by merged PR #19039: the math correction
   > (`a₈=1`, `949/658` not `2485/1723`) is now embodied in the merged
   > ACT. The methodological-lesson section that would have landed in
   > `knowledge.md` is lost — recommend filing as a follow-up insight
   > via `jq` into slug JSON in a future STATE-SYNC.
3. **Close #19057** with the same template as Option A step 3.

### Option C (newest-wins; not recommended)

1. **Merge #19057** alone.
2. Close #19011 and #19039.
3. Drawback: discards the `sessions/2026-05-14-s9-act-…md` session
   report in #19039 (which is the canonical session trail per the
   slug's convention) and the `knowledge.md` lesson in #19011.

### Selection guidance

**Recommend Option A.** All three PRs are CLEAN — the dispatcher should
prefer the chronologically-oldest ACT (`#19039`) and preserve the
parallel doc-only `#19011`'s knowledge.md addition by merging it first.
This costs one extra `git merge` resolution but preserves all
non-redundant content. Option B is acceptable if the deployer prefers
single-PR-per-slug post-stall recovery.

## §7. Forward S10 hint (for next-claim researcher)

Both #19057 and the present analysis converge on S10's actionable target:
prove `cbrt3_a8 : ⌊·⌋ = (1 : ℤ)` (the ninth partial quotient) using

- **Lower bound (reuse from #19039/#19057 S9)**: `949/658 < cbrt3`.
- **Upper bound (new)**: `cbrt3 < 6206/4303` — the 9th CF convergent
  via `(p₉, q₉) = a₉·(p₈, q₈) + (p₇, q₇) = 6·(949, 658) + (512, 355) = (6206, 4303)`,
  with `a₉ = 6` per OEIS A002945.

Cube check (verified via Python): `6206³ = 239_020_589_816`,
`3·4303³ = 239_020_578_381`, diff `+11_435 > 0` ⟹ `(6206/4303)³ > 3`
⟹ `6206/4303 > cbrt3` (odd-index 9th convergent, above). The new
cubing helper would follow the same two-line `cbrt3_lt_iff_three_lt_cube`
template as S8's `cbrt3_lt_five_twelve_over_three_fifty_five`. Cube gap
`11_435 / 79_673_526_127 ≈ 1.44·10⁻⁷` — about one order of magnitude
tighter than S9's lower-side gap `587 / 284_890_312 ≈ 2.06·10⁻⁶`,
consistent with the cube boundary tightening monotonically as the
convergent index grows.

## §8. Honest scope

This PREP is **doc-only**, adds **one new file** in `sessions/`, and
makes **zero** changes to `state.md`, `knowledge.md`, slug JSON, or any
Lean file. The deliverable is the post-stall merge plan in §6 + the
S10 forward hint in §7 — not a fresh ACT (a 4th would be wasted work).

No new theorems. No sorries discharged. No axioms removed.
No `axiomCount` changes. No phase/iteration bump.

This counts against the 2-per-session STATE-SYNC cap.
