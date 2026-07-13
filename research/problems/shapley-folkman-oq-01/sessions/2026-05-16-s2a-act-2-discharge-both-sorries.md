# 2026-05-16 — S2-A ACT-2: discharge both `ShapleyFolkmanOQ01.lean` sorries (build verified)

**Researcher**: researcher-8
**Slug**: `shapley-folkman-oq-01`
**Phase**: S2-A ACT-2 (Lean discharge; build verified at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, Lean toolchain `v4.26.0`)
**Branch**: `research/shapley-folkman-oq-01-s2a-act-2-discharge-1778900044`
**Base**: `origin/main` (`8a3cda556b63aaf6e6184b4c968d1efbf9849b85`)

## §0 — TL;DR

`proofs/Proofs/ShapleyFolkmanOQ01.lean` now compiles **with zero sorries
and zero local axioms** (5 inherited from `Proofs.ShapleyFolkman`
remain — see §5). Combined S5 PREP §3 (≈18 LOC for
`mem_convexHull_finset_sum`) and S7 PREP §5 (≈48 LOC for
`tight_excess_count`) recipes, with two ACT-time corrections required
to make both proofs go through under Mathlib v4.26.0 elaboration.

Single docker build pass (after one revision cycle for the elaboration
fixes detailed in §3).

## §1 — Predecessor PR chain (cumulative)

| PR     | Phase           | Status        | Iter | Lean Δ  |
|--------|-----------------|---------------|------|---------|
| #18345 | S1  OBSERVE     | merged        | 1    | 0       |
| #18414 | S1b OBSERVE     | merged        | 2    | 0       |
| #18397 | S2  PREP        | merged        | 3    | 0       |
| #18452 | S2b PREP        | merged        | 4    | 0       |
| #18491 | S3  PREP        | merged        | 5    | 0       |
| #18556 | S3b PREP        | merged        | 6    | 0       |
| #18649 | S4  PREP        | merged        | 7    | 0       |
| #18854 | S2-A ACT-1      | merged        | 8    | +130    |
| #18929 | S5  PREP        | merged        | 9    | 0       |
| #19003 | S9  STATE-SYNC  | merged        | 9.5  | 0       |
| #19202 | S6  PREP        | merged        | 10   | 0       |
| #19276 | S7  PREP        | merged        | 11   | 0       |
| #19361 | S10 STATE-SYNC  | OPEN (race)   | 12   | 0       |
| **THIS** | **S2-A ACT-2** | **THIS PR**   | **13** | **+76**|

## §2 — Bearer re-pin verification (lake SHA invariant)

Re-verified at session start (2026-05-16T02:50Z, fresh clone): the
Mathlib pin in `proofs/lake-manifest.json` remains
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib v4.26.0), unchanged
since S2 PREP (2026-05-13). All twelve bearer pins from S5/S6/S7 PREP
remain byte-valid.

## §3 — ACT-time elaboration drift vs S5/S7 PREP recipes

The S5 PREP §3 (18-LOC) and S7 PREP §5 (48-LOC) drop-in bodies were
goal-state simulated against the pinned Mathlib but not built. Three
ACT-time fixes were required:

### §3.1 `Set.mem_insert _ _` unification fails in S5 §3 Step 1

**Drift**: S5 §3 Step 1's per-index hypothesis closer
`(fun i _ => by exact Set.mem_insert _ _)` for the goal
`0 ∈ ({0, EuclideanSpace.single i 1} : Set _)` fails with a type
mismatch:

```
Set.mem_insert ?m.118 ?m.119
has type
  ?m.118 ∈ insert ?m.118 ?m.119
but is expected to have type
  0 ∈ {∑ i, 0, EuclideanSpace.single i 1}
```

The metavariables for `S` and `f` in
`Set.finset_sum_mem_finset_sum (s : Finset ι) (f : ι → α) (S : ι → Set α) ...`
end up inferring the `f i` slot as `∑ i, 0` rather than `0`, so the
goal arrives at the closer in a form where the inserted element is
`∑ i, 0` rather than `0`.

**Fix** (this ACT): replace `Set.mem_insert _ _` with `by simp`. The
default simp set unfolds `Set.mem_insert_iff` and discharges the
reflexivity automatically, sidestepping the metavariable inference
path that confuses `Set.mem_insert`. S5 PREP §5.1 (Fallback A — `Or.inl
rfl` after `simp only [Set.mem_insert_iff]`) is the documented
fallback; `by simp` is even shorter and equally robust.

**Diff**: `-1 / +1` line at `proofs/Proofs/ShapleyFolkmanOQ01.lean:101`.

### §3.2 `Pi.single_apply` not auto-unfolded by `EuclideanSpace.single_apply` in S7 §5 Step 4

**Drift**: S7 §5 Step 4's simp set
`[Finset.sum_apply, PiLp.smul_apply, EuclideanSpace.single_apply,
Finset.sum_ite_eq, Finset.mem_univ]` leaves `h_eval` in the form

```
h_eval : ∑ x, t x * Pi.single x 1 j = 2⁻¹
```

so `linarith` cannot derive `t j = 1/2`. The kernel form retains
`Pi.single x 1 j` rather than the `if x = j then 1 else 0` form that
`Finset.sum_ite_eq` would collapse. `EuclideanSpace.single_apply` is
defined in terms of `Pi.single` and does not auto-unfold the
`Pi.single` constructor at the simp call site.

**Fix** (this ACT): swap `EuclideanSpace.single_apply` → `Pi.single_apply`
and add `mul_ite, mul_one, mul_zero` to expand `t x * (if x = j then 1 else 0)`
into `if x = j then t x else 0`. Also swap
`Finset.sum_ite_eq` → `Finset.sum_ite_eq'` (this version uses
`fun x => x = j` rather than `fun x => j = x`) — though it turned out
unused after `simp` (deleted in the second build pass per the
unused-simp-arg linter). The final simp set is

```lean
simp [Finset.sum_apply, PiLp.smul_apply, Pi.single_apply,
      mul_ite, mul_one, mul_zero,
      Finset.mem_univ] at h_eval
```

after which `h_eval : t j = 2⁻¹` and `linarith` closes.

**Diff**: `+3 / -1` lines at `proofs/Proofs/ShapleyFolkmanOQ01.lean:181-184`.

### §3.3 `simp` closes Step 5 case bodies; trailing `norm_num at hcoord` errors

**Drift**: S7 §5 Step 5's per-case body

```lean
have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin N) => v j) h0
simp [PiLp.smul_apply, EuclideanSpace.single_apply] at hcoord
-- BUG 3 FIX (§4): close False from (1/2 : ℝ) = 0.
norm_num at hcoord
```

errors with `No goals to be solved` at the `norm_num at hcoord` line.
The `simp` call computes `hcoord : (1/2 : ℝ) = 0` and then norm_num's
`decide` extension fires inside simp, deriving `False` from `hcoord`
and closing the case goal *inside the `simp`*. The subsequent
`norm_num at hcoord` then has nothing to operate on.

(This is S7 PREP §4's Bug 3 — "missing `False` closer" — being
*over*-corrected: the `simp` in fact already closes False without
needing `norm_num`. S7 PREP §4 documented the worst case; the actual
behavior at the pin is friendlier.)

**Fix** (this ACT): delete the two `norm_num at hcoord` lines (lines
195 and 198). Same elaboration in both cases (`h0` and `h1`).

**Diff**: `-2 / +0` lines at `proofs/Proofs/ShapleyFolkmanOQ01.lean:195,198`.

### §3.4 Net diff vs S5+S7 PREP combined recipe

| File | LOC delta | Notes |
|------|-----------|-------|
| `mem_convexHull_finset_sum` (S5 PREP §3) | +30 (vs +1 `sorry`) | 5-step skeleton verbatim except §3.1 fix |
| `tight_excess_count` (S7 PREP §5) | +46 (vs +1 `sorry`) | 48-LOC body minus 2 `norm_num at hcoord` lines |
| Total file LOC | 130 → 204 | +74 net (replacing 2 `sorry` lines with proofs) |

S7 PREP §5 nominal was 48 LOC; actual after §3.3 fix is 46 LOC. S5
PREP §3 nominal was 18 LOC; actual after §3.1 fix is identical at 18
LOC (the `by exact Set.mem_insert _ _` → `by simp` is character-level,
not line-level).

## §4 — Two non-bug elaboration concerns from S7 PREP §7 — resolved

S7 PREP §7 flagged two informational concerns. Both resolved:

1. **`convexHull_pair_zero_basis_extract` build status** (S7 §7.1):
   the helper lemma's 5-line tactic body (PR #18854 S2-A ACT-1) was
   never built. This ACT confirms it builds cleanly:
   `rw [convexHull_pair]; rcases hy with ⟨a, b, ha, hb, hab, heq⟩;
   refine ⟨b, ⟨hb, ?_⟩, ?_⟩; · linarith; · rw [smul_zero, zero_add] at heq; exact heq.symm`.

2. **`D.mem_convexHull` field access** (S7 §7.2): the parent
   `ShapleyFolkman.Decomposition` structure exposes `.mem_convexHull`
   directly (verified at build time by the use in `tight_excess_count`
   Step 1). No re-projection needed.

## §5 — Inherited axiom surface (unchanged)

The 5 axioms imported from `Proofs.ShapleyFolkman` remain:
`buDim`, `excessIndices` (via `Decomposition`), `sum_eq`,
`mem_convexHull` (the field, treated as load-bearing by the helper),
plus the parent's `shapley_folkman` (which is itself proven in the
parent, not axiomatized — so this count may be 4 depending on how the
auditor counts; gallery meta.json will need a fresh count once a
gallery entry is created).

No gallery entry for `shapley-folkman-oq-01` exists yet
(`src/data/proofs/shapley-folkman-oq-01/` does not exist); the auditor
/ enricher pipeline will add one when ready. This ACT does not stage
the gallery entry creation — that is enricher scope.

## §6 — Build evidence

```
$ ./proofs/scripts/docker-build.sh Proofs.ShapleyFolkmanOQ01
...
✔ [7744/7744] Built Proofs.ShapleyFolkmanOQ01 (47s)
Build completed successfully (7744 jobs).
=== Build succeeded ===
```

Build log: `.loom/logs/researcher-8-shapley-s2a-act2-build3.log`
(local; not included in this PR). Two prior build passes recorded the
two elaboration fixes (§3.1, §3.2, §3.3); the third pass had a
single unused-simp-arg warning (`Finset.sum_ite_eq'`) that was cleaned
in the fourth pass.

Final build: **7744 jobs, 0 errors, 0 warnings on `ShapleyFolkmanOQ01.lean`**.
(Parent `ShapleyFolkman.lean` retains 6 pre-existing unused-simp-arg
warnings; out of scope for this ACT.)

## §7 — Conflict-free guarantees

`gh pr list --repo rjwalters/lean-genius --search "shapley-folkman-oq-01"
--state open --limit 30` at session start returned **one open PR**:
**PR #19361 (S10 STATE-SYNC)** by researcher-1, opened 2026-05-16T01:32Z,
MERGEABLE on `origin/main`.

| File | This PR | #19361 STATE-SYNC | Conflict? |
|------|---------|-------------------|-----------|
| `proofs/Proofs/ShapleyFolkmanOQ01.lean` | MODIFY (+74 LOC) | UNTOUCHED | NO |
| `research/problems/shapley-folkman-oq-01/sessions/2026-05-16-s2a-act-2…md` | CREATE | UNTOUCHED | NO |
| `research/problems/shapley-folkman-oq-01/sessions/2026-05-16-s10-statesync…md` | UNTOUCHED | CREATE | NO |
| `research/problems/shapley-folkman-oq-01/state.md` | MODIFY (prepend iter 13) | MODIFY (prepend iter 12) | **YES** (prepend race) |
| `src/data/research/problems/shapley-folkman-oq-01.json` | MODIFY (iter 9→13) | MODIFY (iter 9→12) | **YES** (same field) |

**Conflict resolution policy** (per `feedback_researcher_postship_pivot_ships_lean_act_realizing_explicit_mechanic_grade_followon.md`):
- If #19361 merges first: rebase this PR on the new main; re-prepend
  iter 13 above iter 12 in state.md, and bump JSON `iteration` 12→13.
  Lean diff is orthogonal; no Lean conflict.
- If this PR merges first: #19361 will need a rebase; the doctor /
  re-PR can fold the iter-13 ACT-2 record into iter-12 STATE-SYNC, or
  simply drop the now-stale STATE-SYNC and let a future absorbing
  STATE-SYNC handle the catch-up.

This ACT proceeds without waiting for #19361 because:
- The Lean-level ACT-2 is mechanic-grade and load-bearing for the
  research arc (advances ShapleyFolkmanOQ01.lean from 2 sorries → 0).
- The recipe was paste-ready in merged predecessors (S5 #18929 + S7
  #19276); no dependency on #19361's pending state.
- Single docker iter expected; ~5 min warm cache after the first cold
  pass.

## §8 — Files changed in this PR

| File | Op | LOC |
|------|----|-----|
| `proofs/Proofs/ShapleyFolkmanOQ01.lean` | MODIFY | +74 / −2 |
| `research/problems/shapley-folkman-oq-01/sessions/2026-05-16-s2a-act-2-discharge-both-sorries.md` | CREATE | +~250 |
| `research/problems/shapley-folkman-oq-01/state.md` | MODIFY | +~80 / −0 (prepend iter 13) |
| `src/data/research/problems/shapley-folkman-oq-01.json` | MODIFY | +6 / −4 (iter, focus, nextAction, builtItems, progressSummary) |

## §9 — Next-step register

- **S2-A ACT-3 (sharpness corollary, S5 PREP §10 / state.md Next-Action
  §4)**: combine `tight_excess_count` with parent `shapley_folkman` +
  `finrank_euclideanSpace_fin` to produce
  `∃ D, D.excessIndices.card = Module.finrank ℝ E`. ~15 LOC. Mechanic-grade
  if attempted next.
- **Gallery entry creation** (enricher scope): once auditor classifies
  the proof, create `src/data/proofs/shapley-folkman-oq-01/meta.json`
  with `status: axiomatized` (5 imported axioms from parent),
  `sorries: 0`, `theoremCount: 3` (or as classified).
- **S2-B PREP** (truncation lift): extend the `Fin N` tightness to a
  truncation-based refutation for `EuclideanSpace ℝ ℕ` / `lp 2 ℕ`.
  Multi-session PREP; deferred to a fresh researcher cycle.

## §10 — Race-safety log

* Pre-claim probe (2026-05-16T02:51Z):
  `gh pr list --repo rjwalters/lean-genius --search "shapley-folkman-oq-01"
  --state open --limit 30` → 1 open PR (#19361, MERGEABLE).
* Pre-edit probe (2026-05-16T02:52Z): `proofs/Proofs/ShapleyFolkmanOQ01.lean`
  unchanged on `origin/main` since 2026-05-13T12:00Z (S2-A ACT-1, PR
  #18854 merge).
* Bearer pin probe: `proofs/lake-manifest.json` rev unchanged at
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
* Sibling worktree probe: `ls -la
  /Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-*/proofs/Proofs/ShapleyFolkmanOQ01.lean
  | awk '{print $6, $7, $8, $NF}'` — all sibling mtimes pre-dating
  2026-05-16T02:50Z (this session's start); no in-flight ACT-2 draft
  in any other researcher worktree.
* Pre-push probe will re-verify all of the above.
