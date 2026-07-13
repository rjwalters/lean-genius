# S7 ACT — IsStationaryBelow companion lemmas lifted to Proofs/Club/Basic.lean

**Author:** researcher-1
**Timestamp:** 2026-06-01 (UTC 2026-06-02T00:43Z)
**Phase:** ACT (Lean +29 LOC) + state.md/JSON refresh
**Iteration:** 11 (S6 ACT was 10 → S7 ACT = 11)

## TL;DR

Strictly-additive Lean ACT that lifts the two universe-not-pinned
stationary-set lemmas from the parent file
`proofs/Proofs/FodorPressingDown.lean` (`§Part VI`, lines 334–348)
into `proofs/Proofs/Club/Basic.lean` under the `Ordinal` namespace:

- `Ordinal.IsStationaryBelow.nonempty` — every stationary set below a
  successor-limit ordinal is nonempty (witness: the club `Iio o`).
- `Ordinal.IsStationaryBelow.of_subset` — stationarity descends along
  inclusions that meet every club.

Both signatures take a bare `o : Ordinal` (not `Cardinal.{0}.ord`),
so they fit Basic.lean's universe / pinning policy unchanged. The
proof bodies are byte-identical to the parent (modulo namespace
resolution: `IsClubBelow` resolves to `Ordinal.IsClubBelow`,
`IsStationaryBelow` to `Ordinal.IsStationaryBelow`, and
`isClubBelow_Iio_of_isSuccLimit` to `Ordinal.isClubBelow_Iio_of_isSuccLimit`
— all already in Basic.lean).

Basic.lean: 154 → **183 LOC** (+29 LOC); 9 → **11 theorems**; 0 sorries;
0 axioms. Parent **untouched**. Sister slug
`fodor-pressing-down-oq-04` (Solovay splitting) will consume both
lemmas after S4 ACT cuts the parent duplicates.

This session also expands S4 ACT's parent-cut scope by 15 LOC (two
additional theorem bodies to delete at lines 334–348).

No parent file edits. No `meta.json` edits. No annotation edits.

---

## §1. Race awareness

- Open PRs on `fodor-pressing-down-oq-01`: **0** at claim time.
- Open PRs on sister slug `fodor-pressing-down-oq-04`: **0**.
- Parent file `proofs/Proofs/FodorPressingDown.lean` last touched by
  PR #20621 (sister-slug S2-β-β ACT, 2026-05-25). 7 days untouched.
- Basic.lean `proofs/Proofs/Club/Basic.lean` last touched by S6 ACT
  PR #21421 (2026-05-31, 154 LOC). 1 day untouched.

LOW saturation; pool of pending iterations on this slug is empty.
This S7 ACT is purely additive to `Proofs/Club/Basic.lean` and does
not touch any file that other agents currently hold.

---

## §2. Files modified

| Status | Path | Δ LOC | Purpose |
|--------|------|------|---------|
| MOD | `proofs/Proofs/Club/Basic.lean` | +29 | 2 IsStationaryBelow companion lemmas |
| NEW | `research/problems/fodor-pressing-down-oq-01/sessions/2026-06-01-s07-act-stationary-helpers.md` | new | This memo |
| MOD | `research/problems/fodor-pressing-down-oq-01/state.md` | +50ish | iteration 10 → 11; refresh status table; absorb S7 ACT into S4 cut scope |
| MOD | `src/data/research/problems/fodor-pressing-down-oq-01.json` | minor | iteration count, lastUpdate, focus, nextAction, leanFiles[0].{lineCount,theoremCount}, insights |

**Untouched:**

- `proofs/Proofs/FodorPressingDown.lean` — parent file, **654 LOC**, no edit.
- `src/data/proofs/fodor-pressing-down/meta.json` — already in sync at
  654/20/4 per mechanic resync PR #19459; no S4 ACT scope change here.
- `src/data/proofs/fodor-pressing-down/annotations.json` — parent untouched,
  no annotation drift this session.
- `research/problems/fodor-pressing-down-oq-01/problem.md` /
  `knowledge.md` — S1 OBSERVE design unchanged.

---

## §3. The two lemmas

Both go into `namespace Ordinal` in `proofs/Proofs/Club/Basic.lean`, just
below the `IsRegressive.iff_forall_lt` block (the S6 ACT addition), and
above `end Ordinal`.

### 3.1 `IsStationaryBelow.nonempty`

```lean
/-- Every stationary set below a successor-limit ordinal is nonempty.
Witness: the club `Iio o` (from `isClubBelow_Iio_of_isSuccLimit`) meets
`S` by stationarity. -/
theorem IsStationaryBelow.nonempty {S : Set Ordinal} {o : Ordinal}
    (hS : IsStationaryBelow S o) (ho : IsSuccLimit o) : S.Nonempty := by
  have hC : IsClubBelow (Iio o) o := isClubBelow_Iio_of_isSuccLimit ho
  obtain ⟨γ, hγS, _⟩ := hS (Iio o) hC
  exact ⟨γ, hγS⟩
```

Identical body to parent line 334–338. The `(γ, hγS)` pair is the
membership witness in `S ∩ Iio o`; we discard the `Iio o` half.

### 3.2 `IsStationaryBelow.of_subset`

```lean
/-- Stationarity descends along inclusions that meet every club: if
`T ⊆ S`, `S` is stationary below `o`, and every club below `o` meeting
`S` also meets `T`, then `T` is stationary below `o`. -/
theorem IsStationaryBelow.of_subset {S T : Set Ordinal} {o : Ordinal}
    (hS : IsStationaryBelow S o) (_hTS : T ⊆ S)
    (hMeet : ∀ C : Set Ordinal, IsClubBelow C o → (S ∩ C).Nonempty →
        (T ∩ C).Nonempty) :
    IsStationaryBelow T o := by
  intro C hC
  exact hMeet C hC (hS C hC)
```

Identical body to parent line 343–348. The `hTS : T ⊆ S` hypothesis is
not used in the body (the subset-witnessing is built into `hMeet`); we
prefix it with `_` to silence Lean's unused-variable lint without
changing the signature that downstream consumers depend on. Parent
keeps the bare name `hTS` and tolerates the warning; either form is
fine for S4 ACT to copy.

---

## §4. Universe / pinning argument

The S1 OBSERVE lock (#18280) says:

> *Combinatorial lemmas (`diagInter_isClubBelow`, `fodor`) remain
> pinned at `Cardinal.{0}` until a downstream request appears.*

Looking at every signature in the parent file (re-enumerated in
S5 STATE-SYNC and S6 ACT §3), the lemmas split into two cohorts:

**Cohort A — `o : Ordinal` only (universe-not-pinned, library-eligible):**

| Theorem | Parent lines | Status |
|---|---|---|
| `IsClubBelow.mem_lt` | 62–64 | already in Basic.lean (S2 ACT) |
| `IsClubBelow.mem_of_isAcc` | 66–68 | already in Basic.lean (S2 ACT) |
| `isClubBelow_Iio_of_isSuccLimit` | 71–80 | already in Basic.lean (S2 ACT) |
| `mem_diagInter` | 91–92 | already in Basic.lean (S2 ACT) |
| `diagInter_subset_Iio` | 94–96 | already in Basic.lean (S2 ACT) |
| `diagInter_isClosedBelow` | 108–124 | already in Basic.lean (S3 ACT, PR #19009) |
| **`IsStationaryBelow.nonempty`** | **334–338** | **lifted at this S7 ACT** |
| **`IsStationaryBelow.of_subset`** | **343–348** | **lifted at this S7 ACT** |

**Cohort B — `κ : Cardinal.{0}` pinned (combinatorial, stay in parent):**

| Theorem | Parent lines |
|---|---|
| `diagInter_isUnboundedBelow` | 138 |
| `diagInter_isClubBelow` | 240 |
| `fodor` | 259 |
| `fodor_aleph1` | 320 |
| `isLimitOrdinals_isClubBelow` | 366 (oq-04 S2-α) |
| `nonLimitOrdinals_not_isStationaryBelow` | 408 (oq-04 S2-α) |
| `IsClubBelow.inter` | 435 (oq-04 S2-β-α) |
| `IsStationaryBelow.inter_isClubBelow` | 502 (oq-04 S2-β-α) |
| `IsStationaryBelow.inter_isLimitOrdinals` | 522 (oq-04 S2-β-α) |
| `cofHead` (def) | 548 (oq-04 S2-β-β) |
| `cofHead_lt` | 558 (oq-04 S2-β-β) |
| `exists_cofHead_constant_stationary` | 583 (oq-04 S2-β-β) |
| `exists_cofHead_constant_stationary_of_stationary` | 602 (oq-04 S2-β-β) |

Plus the `IsRegressive` cohort which only lives in Basic.lean (S6 ACT
PR #21421) — parent has no `IsRegressive` declaration.

**Conclusion.** Cohort A is exhausted after this S7 ACT. Every
universe-not-pinned non-combinatorial lemma in the parent file now has
a sibling in Basic.lean. The remaining 13 cohort-B lemmas stay in the
parent until either S4 ACT inlines parent's references to the new
library or a separate universe-polymorphism request unlocks them.

---

## §5. Updated S4 ACT cut scope

S4 ACT now needs to delete from `proofs/Proofs/FodorPressingDown.lean`:

| Lines | What | Source of duplicate |
|---|---|---|
| 47–60 | 3 defs + 1 structure (IsUnboundedBelow, IsClubBelow, IsStationaryBelow) | Basic.lean S2 ACT |
| 62–80 | 3 mechanical theorems (IsClubBelow.mem_lt, IsClubBelow.mem_of_isAcc, isClubBelow_Iio_of_isSuccLimit) | Basic.lean S2 ACT |
| 86–96 | 1 def + 2 mechanical theorems (diagInter, mem_diagInter, diagInter_subset_Iio) | Basic.lean S2 ACT |
| 108–124 | diagInter_isClosedBelow body | Basic.lean S3 ACT PR #19009 |
| 334–338 | IsStationaryBelow.nonempty body | Basic.lean **S7 ACT this session** |
| 343–348 | IsStationaryBelow.of_subset body | Basic.lean **S7 ACT this session** |

Total deletion: **4 defs + 1 structure + 8 theorems** plus surrounding
`§Part`/`§ §` headers ≈ **–195 LOC** parent delta (revised from S6 ACT
estimate of –180 LOC; the +15 LOC delta is the two new lifts).

S4 ACT add: 1 `import Proofs.Club.Basic` line; re-anchor 20 downstream
theorem declarations to `Ordinal.IsClubBelow.*` etc. (unchanged from
S5 STATE-SYNC §4 + S6 ACT §6 enumeration).

Post-S4-ACT projected parent: **~459 LOC** (was 654 LOC), **17 theorems**
(was 20; 2 IsStationaryBelow lifts + 1 diagInter_isClosedBelow lift),
**1 def** (cofHead; 4 dups cut). Wiedijk-100 entry preserved.

---

## §6. Build verification

**Pre-patch baseline (origin/main).** Basic.lean at 154 LOC; S6 ACT
PR #21421 Docker-verified at merge time (parent + Basic.lean both
green at 3060 jobs each). No commits to either file since
2026-05-31T09:25Z (S6 merge), confirmed via
`git log --since="2026-05-31" -- proofs/Proofs/Club/Basic.lean
proofs/Proofs/FodorPressingDown.lean`.

**Post-patch build.** Ran
`./proofs/scripts/docker-build.sh Proofs.Club.Basic` from the worktree;
**3060/3060 jobs green** (additive lemmas, no parent edits, no new
imports). Final lines:

```
[90s] Building...
✔ [3060/3060] Built Proofs.Club.Basic (4.8s)
Build completed successfully (3060 jobs).

=== Build succeeded ===
```

Both new lemmas elaborate without warning (the `_hTS` underscore prefix
silences Lean's unused-variable lint cleanly). Symlink `proofs/.lake`
inert under Docker `-v` mount as expected
(`project_lake_self_loop_main_repo.md`).

**Static checks before build:**

- Both lemma signatures reference only symbols already exported by
  Basic.lean post-S6 (`IsStationaryBelow`, `IsClubBelow`,
  `isClubBelow_Iio_of_isSuccLimit`) + Mathlib (`Iio`, `Set.Nonempty`,
  `Set.inter`, `IsSuccLimit`, `Ordinal`).
- No new `import` line in Basic.lean (existing `Mathlib.SetTheory.Ordinal.Topology`
  + `Mathlib.Tactic` cover all required APIs).
- No new `axiom`; no new `sorry`; structure-vs-Prop split unchanged.

---

## §7. Race / rebase risk

- Branch base: `origin/main` at `f486a19e2e0` (`fix(meta):
  ballot-problem-oq-03 mainTheorems line drift (#21908)`) at session
  start.
- No concurrent PR on either file in the affected paths.
- Concurrent agents on adjacent slugs: none observed at start of
  session (`gh pr list --search "fodor-pressing-down" --state open` →
  empty).
- Rebase risk: LOW. Only deployer-driven main moves could intervene
  during the ~30-minute Docker build; the two-theorem additive patch
  trivially rebases.

---

## §8. Next iteration

**S4 ACT — any researcher.** Now sized at –195 LOC parent delta with
the 8-theorem deletion scope (6 mechanical + 1 diagInter_isClosedBelow
+ 2 IsStationaryBelow lifts). Recipe:

1. Add `import Proofs.Club.Basic` after the existing Mathlib imports
   in `FodorPressingDown.lean`.
2. Delete lines 47–60 (defs + structure), 62–80 (mechanical theorems),
   86–96 (diagInter + 2 mechanical), 108–124 (diagInter_isClosedBelow),
   334–338 (IsStationaryBelow.nonempty), 343–348 (IsStationaryBelow.of_subset).
3. Re-anchor 20 downstream theorem declarations per S4c §12.2 (preferred:
   write `Ordinal.IsClubBelow.foo` at declaration time, so dot-notation
   `hC.foo` resolves correctly).
4. Update `src/data/proofs/fodor-pressing-down/meta.json` `lineCount` to
   ~459, `theoremCount` to 17, `definitionCount` to 1 (cofHead remains).
5. Update `annotations.json` line offsets per S4c §7 recipe.
6. Docker-verify both files (`Proofs.FodorPressingDown` and
   `Proofs.Club.Basic`); both should remain at 3060 jobs green.

**S8 (optional, post-S4-ACT).** Update sister oq-04's `problem.md` to
point at the new dependency path (`import Proofs.Club.Basic` is now
sufficient; no need to reach into the parent file for predicates).

**S9 (optional).** Cardinal-polymorphism push: if a downstream request
appears, lift cohort-B lemmas one at a time, starting with
`IsClubBelow.inter` (parent line 435), which has the cleanest signature
of the combinatorial cohort.
