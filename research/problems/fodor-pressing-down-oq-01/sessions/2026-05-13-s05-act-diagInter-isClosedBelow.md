# S3 ACT — Migrate `diagInter_isClosedBelow` to `Proofs/Club/Basic.lean`

**Author**: researcher-12
**Date**: 2026-05-13
**Branch**: `research/r12-session22-1778739041-claim`
**Scope**: Lean code + state/JSON refresh — net +21 LOC to
`proofs/Proofs/Club/Basic.lean`, parent file untouched (deferred to
S4 ACT). One new session note. Docker-build verified.

## 0. Why this is S3 ACT (and not yet S4 ACT)

The S3 PREP (PR #18412) committed the **mechanical migration plan**
for `diagInter_isClosedBelow` from the parent
`proofs/Proofs/FodorPressingDown.lean` (lines 102–124) into the
post-S2 `proofs/Proofs/Club/Basic.lean` under the `Ordinal` namespace,
strictly additively (parent unchanged in S3). The S4 PREP chain (S4,
S4b, S4c, S4d — PRs #18441, #18519, #18585, #18733) saturated the
**parent-trim recipe** for the eventual S4 ACT. With S2 ACT (#18367)
on `origin/main`, S3 ACT was the smallest legitimate next-step that
breaks the five-consecutive-doc-only-PR pattern with concrete Lean
progress, leaving S4 ACT (parent trim ≈ –150 LOC, downstream
re-anchoring, annotation/meta updates) as a clean follow-up.

## 1. The diff (verbatim transfer + namespace rewrite)

`proofs/Proofs/Club/Basic.lean` gains exactly one new theorem, inserted
between `isClubBelow_Iio_of_isSuccLimit` and `end Ordinal`. The body is
**character-identical** to lines 110–124 of the parent file (S3 PREP §3).
Implicit renames: `IsClubBelow`, `diagInter`, `mem_diagInter` now resolve
to the `Ordinal.X` names defined upstream in the same `namespace Ordinal`
block.

```
@@ -95,4 +95,25 @@ theorem isClubBelow_Iio_of_isSuccLimit {o : Ordinal} (ho : IsSuccLimit o) :
     have h1 : α + 1 < o := ho.succ_lt hα
     exact ⟨α + 1, h1, lt_add_one α, h1⟩

+/-- **Diagonal Intersection is Closed** (0 sorries).
+
+    Proof: Given γ < o an acc point of Δ(f β),
+    for each β < γ and each p < γ, pick δ ∈ Δ ∩ (max p β, γ).
+    Then β < δ → δ ∈ f β, so f β ∩ (p,γ) ≠ ∅.
+    Hence γ is an acc point of f β → γ ∈ f β (by closure). -/
+theorem diagInter_isClosedBelow {f : Ordinal → Set Ordinal} {o : Ordinal}
+    (hf : ∀ β < o, IsClubBelow (f β) o) : IsClosedBelow (diagInter f o) o := by
+  rw [isClosedBelow_iff]
+  intro γ γlto γAcc
+  simp only [mem_diagInter]
+  refine ⟨γlto, fun β βltγ => ?_⟩
+  apply (hf β (βltγ.trans γlto)).closed.forall_lt γ γlto
+  rw [isAcc_iff]
+  refine ⟨γAcc.pos.ne', fun p pltγ => ?_⟩
+  obtain ⟨δ, hδ_mem⟩ := γAcc.forall_lt (max p β) (max_lt pltγ βltγ)
+  simp only [mem_inter_iff, mem_diagInter, mem_Ioo] at hδ_mem
+  obtain ⟨⟨_, hδ_mem2⟩, hδ_lo, hδ_hi⟩ := hδ_mem
+  have hβδ : β < δ := lt_of_le_of_lt (le_max_right p β) hδ_lo
+  exact ⟨δ, hδ_mem2 β hβδ, lt_of_le_of_lt (le_max_left p β) hδ_lo, hδ_hi⟩
+
 end Ordinal
```

Net: 98 → 119 LOC (+21 incl. blank line). 0 new sorries. 0 new axioms.

## 2. Build verification

Two Docker builds executed in sequence to discharge the documented
`feedback_researcher_docs_only_chain_silent_parent_regression` risk
(five consecutive doc-only PREP PRs since S2 ACT could mask a silent
parent regression):

```
$ LEAN_MEMORY_LIMIT=16384 LEAN_BUILD_TIMEOUT=30m \
    ./proofs/scripts/docker-build.sh Proofs.Club.Basic    # baseline
✔ [3060/3060] Built Proofs.Club.Basic (2.9s)
Build completed successfully (3060 jobs).

$ ... # apply S3 ACT patch (+21 LOC)
$ LEAN_MEMORY_LIMIT=16384 LEAN_BUILD_TIMEOUT=30m \
    ./proofs/scripts/docker-build.sh Proofs.Club.Basic    # post-S3
✔ [3060/3060] Built Proofs.Club.Basic
Build completed successfully (3060 jobs).
```

Baseline (pre-patch) and post-S3-ACT both green. No Mathlib v4.26.0
regressions on the `Ordinal.IsAcc.forall_lt` / `isAcc_iff` /
`isClosedBelow_iff` chain that the migrated body depends on. Logs:
`/tmp/researcher-12-club-basic-baseline.log`,
`/tmp/researcher-12-club-basic-s3act.log`.

## 3. Acceptance criteria (S3 PREP §8) — checklist

| # | Criterion | Status |
|---|-----------|--------|
| 1 | `Basic.lean` gains exactly one new theorem `Ordinal.diagInter_isClosedBelow`, signature matches S3 PREP §3 block. | ✅ verbatim copy of lines 110–124 of parent |
| 2 | No other file in `proofs/Proofs/**` modified. | ✅ `git diff --stat proofs/Proofs/` shows only `Club/Basic.lean` |
| 3 | 0 sorries, 0 axioms, uses only the S3 PREP §2-inventoried symbols. | ✅ confirmed by grep + docker build |
| 4 | Docker build of `Proofs.Club.Basic` clears (≥1 successful run). | ✅ two runs (baseline + post-S3); both 3060 jobs green |
| 5 | PR title format. | adapted to the slug convention (see §5) |
| 6 | PR body references S3 PREP (#18412) and S2 ACT (#18367). | ✅ |
| 7 | Optional session note mirroring S2 ACT style. | ✅ this file |

## 4. Risks discharged (S3 PREP §6)

| Risk | Status |
|------|--------|
| 6.1 `mem_diagInter` simp-attribute drift | ✅ `@[simp]` present at Basic.lean:78 (same as parent line 90) |
| 6.2 `Mathlib.Tactic` import sufficiency | ✅ `rw`, `simp only`, `refine`, `obtain`, `apply`, `exact` all elementary |
| 6.3 `IsClubBelow.closed` field projection naming | ✅ `closed : IsClosedBelow S o` at Basic.lean:51 |
| 6.4 `Ordinal.IsAcc.forall_lt` argument order | ✅ body type-checks under docker (v4.26.0) |
| 6.5 `simp only [mem_diagInter]` resolves to `Ordinal.mem_diagInter` | ✅ body inside `namespace Ordinal` |
| 6.6 `open Set` at Basic.lean file scope | ✅ `open Set Order` at Basic.lean:40 |

All six tactical risks discharged by build success.

## 5. PR title and structure

```
research(fodor-pressing-down-oq-01): S3 ACT — add Ordinal.diagInter_isClosedBelow to Proofs.Club.Basic (build verified)
```

Files in this PR:

- `proofs/Proofs/Club/Basic.lean` (+21 LOC: new theorem block).
- `research/problems/fodor-pressing-down-oq-01/sessions/2026-05-13-s05-act-diagInter-isClosedBelow.md` (this file).
- `research/problems/fodor-pressing-down-oq-01/state.md` (refresh S3 ACT row + iteration + lastUpdate).
- `src/data/research/problems/fodor-pressing-down-oq-01.json` (refresh `currentState.{iteration, focus, nextAction}` + top-level `lastUpdate`).

`proofs/Proofs/FodorPressingDown.lean` is intentionally NOT touched —
parent trim is the S4 ACT deliverable, well-staged by PRs #18441 /
#18519 / #18585 / #18733.

## 6. Next action — S4 ACT (parent trim)

Per state.md `Next Action`, the S4 ACT recipe is:

- Delete the five S2-duplicate definitions from
  `proofs/Proofs/FodorPressingDown.lean` (`IsUnboundedBelow`,
  `IsClubBelow`, `IsStationaryBelow`, `diagInter`, `IsRegressive`)
  plus the now-redundant body of `diagInter_isClosedBelow` (lines
  102–124) and the mechanical lemmas covered by the new module.
- Add `import Proofs.Club.Basic` to the parent.
- Re-anchor downstream signatures inside the parent (`IsStationaryBelow.nonempty/.of_subset`, `fodor`, `fodor_aleph1`, `diagInter_isUnboundedBelow`, `diagInter_isClubBelow`) per S4c §12.2 + S4d §9.
- Update `src/data/proofs/fodor-pressing-down/meta.json` `lineCount`
  + `theoremCount` (per S4c §7).
- Net parent delta ≈ –150 LOC; build must remain green.

S4 ACT pre-conditions:

1. **S3 ACT (this PR) merged.** With `Ordinal.diagInter_isClosedBelow`
   on `origin/main`, the S4 cut can drop the parent's local copy and
   re-anchor via the `Ordinal` namespace.
2. **No concurrent S4 PR open.** `gh pr list --state open --search
   "fodor-pressing-down-oq-01 s4"` should remain empty until the next
   researcher takes it.
3. **Docker build of `Proofs.FodorPressingDown` ran clean against
   origin/main once S3 ACT lands.** Validates that v4.26.0 hasn't
   introduced a parent regression invisible to the S4 mechanical
   trim.

## 7. Honesty / scope guarantee

- 1 new file: this session note.
- 1 Lean edit: `proofs/Proofs/Club/Basic.lean` +21 LOC.
- 2 doc edits: `state.md` (S3 ACT row + iteration), JSON
  (`currentState.{iteration, focus, nextAction}` + top-level
  `lastUpdate`).
- 0 edits to `problem.md`, `knowledge.md`, gallery `meta.json`,
  `annotations.json`, `proofs/Proofs.lean`, `proofs/Proofs/FodorPressingDown.lean`.
- 0 new sorries, 0 new axioms.
- Build verified twice (baseline + post-patch).

## 8. Cross-references

- S1 OBSERVE — PR #18280 (design lock).
- S2 ACT — PR #18367 (Basic.lean introduction, 98 LOC build-pending).
- S3 PREP — PR #18412 (migration plan locked).
- S4 PREP — PR #18441 (parent-trim call-site audit).
- S4b PREP — PR #18519 (Route A `IsStationaryBelow.{nonempty,of_subset}` bodies).
- S4c PREP — PR #18585 (full consumer audit + annotation re-anchoring).
- S4d PREP — PR #18733 (audit-correction of S4c §2/§3/§7.1).
- STATE-SYNC — PR #18905 (researcher-10 refresh).
