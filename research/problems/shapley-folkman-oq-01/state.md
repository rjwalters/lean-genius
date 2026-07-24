# Research State: shapley-folkman-oq-01

## Current State
**Phase**: COMPLETED (S2-D ACT — Session 21, researcher-3, 2026-07-23.
Shipped and **Docker-verified** the genuine ℓ² lift: injective embedding
`ιN : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] lp (fun _:ℕ => ℝ) 2`, `ιN_apply_coord`,
`ιN_injective`, and the capstone `shapley_folkman_excess_unbounded_in_lp`
(excess card unbounded over ℓ² subsets, lifted from `Fin N` tightness via
the S2-C `Decomposition.map` core). Build clean at v4.31.0 — 8577 jobs,
0 sorries, 0 axioms — which ALSO retro-verifies the Session-20 S2-C core
left unverified during the 2026-06-13 Docker blackout, the sole reason
this problem was `blocked`. **OQ-01 answered NO, machine-verified end to
end.** Only remaining direction is the separate positive Aumann/Lyapunov
analog, out of scope for this OQ.)
**Path**: full
**Since**: 2026-06-13
**Last Updated**: 2026-07-23 (S2-D ACT VERIFIED, researcher-3)
**Iteration**: 21

## Session 21 — S2-D ACT: genuine ℓ² lift, VERIFIED (researcher-3, 2026-07-23)

**Mode.** ACT (`.lean` + JSON + docs). **Outcome: COMPLETED, 0-axiom VERIFIED.**

Executed the Session-20 §4 S2-D recipe with v4.31 API fixes and ran the
first Docker build since the blackout: `✔ Built Proofs.ShapleyFolkmanOQ01
(8577 jobs)`, 0 sorries, 0 axioms. Added `ιN`, `ιN_apply_coord`,
`ιN_injective`, `shapley_folkman_excess_unbounded_in_lp` (+ import
`Mathlib.Analysis.Normed.Lp.lpSpace`). The negative answer to OQ-01 is now
complete and machine-checked in both `EuclideanSpace` (tightness) and `ℓ²`
(unboundedness). Full write-up: `sessions/2026-07-23-s2d-act-lp2-lift-verified.md`.
Key v4.31 drift: `lp.single_apply_self/ne` need explicit `(E := fun _:ℕ => ℝ)`;
`map_add'/map_smul'` want the explicit `Finset.sum_congr` form, not one-shot simp.

## Session 20 — S2-C ACT: `Decomposition.map` transport core (researcher-2, 2026-06-13)

**Mode.** ACT (`.lean` + JSON edits).

Added a `namespace ShapleyFolkman` block to `ShapleyFolkmanOQ01.lean`
with four declarations general over any `f : E →ₗ[ℝ] F`:
`Decomposition.map` (transport), `map_point` (`rfl` simp lemma),
`map_excessIndices_of_injective` (injective ⟹ excess sets equal), and
`map_excessIndices_card_of_injective` (card form — the transfer lemma).

Proof bearers pinned via GitHub API at v4.26.0: `LinearMap.image_convexHull`
(`Hull.lean:167`), `Function.Injective.mem_set_image` (`Image.lean:192`),
`Finset.filter_congr` (`Filter.lean:179`), `map_zero`, `map_sum`. The two
HO-unification-exposed steps were hardened (`show` before the convexHull
`rw`; `rw [← D.sum_eq, map_sum]` for the sum field).

**Build status: UNVERIFIED locally.** Docker daemon is unresponsive
(`docker info`/`version` hang) and the `.lake` symlink loop persists, so
no `lake build` ran. Each step was hand-checked against the v4.26.0
bearer statements; the `simp only [Decomposition.excessIndices, …]`
unfold pattern is already used elsewhere in this file. CI/doctor verifies
on PR open. Fallback register in the session doc §3.

S2-B₂ is now reduced to "build one injective embedding + apply the
core"; §4 of the session doc gives the paste-ready `ιN`, `ιN_injective`,
and `shapley_folkman_excess_unbounded_in_lp`.

Full session report at
`sessions/2026-06-13-s2c-act-decomposition-map-transport.md`.

## Session 19 — S2-B₁ ACT: `no_universal_shapley_folkman_bound` (researcher-10, 2026-06-10)

**Mode.** ACT (`.lean` + JSON edits).

Executed Session 18 §3.1 recipe verbatim. Pasted 33 LOC (docstring +
theorem) immediately before `end ShapleyFolkmanOQ01`. The three-step
body — `refine ⟨midpointDecomp (K + 1), ?_⟩; rw [tight_excess_count
(K + 1) (midpointDecomp (K + 1))]; exact Nat.lt_succ_self K` —
elaborates without rewrite or fallback hints.

Docker build clean: `./proofs/scripts/docker-build.sh
Proofs.ShapleyFolkmanOQ01` →
`✔ [7744/7744] Built Proofs.ShapleyFolkmanOQ01 (231s)`.

Full session report at
`sessions/2026-06-10-s2b1-act-no-universal-bound.md`.

## Session 18 — S2-B PREP: truncation-lift design (researcher-1, 2026-06-09)

**Mode.** PREP (doc-only; no `.lean` / no `meta.json` edits).

**Outcome.** Designed S2-B, the long-flagged "truncation lift to
`EuclideanSpace ℝ ℕ` / `lp 2 ℕ`" from the Session 17 (S2-A ACT-4 ACT)
Next-action register. Found that the natural S2-B goal cleanly splits
into two independent claims of different cost, only the first of which
is paste-ready:

* **S2-B₁** (~15 LOC, paste-ready): `no_universal_shapley_folkman_bound`,
  a direct three-line corollary of the existing `midpointDecomp` (S2-A
  ACT-4) and `tight_excess_count` (S2-A ACT-2). States: for every `K : ℕ`
  there is a decomposition with `excessIndices.card > K`. Achieves the
  qualitative "no fixed `Nat` bound suffices" claim entirely within
  finite-dim ambients of growing dimension.

* **S2-B₂** (~150-250 LOC, multi-session): genuine `lp (fun _ : ℕ => ℝ) 2`
  lift via a linear isometric embedding `ι_N : EuclideanSpace ℝ (Fin N)
  →ₗᵢ lp …` and a `Decomposition.map` transport function. Designed in
  §4 of the session file; deferred to S2-C with bearer pins for `lp.single`,
  `lp.lsingle`, `lp.isometry_single`, `lp.singleContinuousLinearMap` and
  the (to-pin) `AffineMap.image_convexHull` from
  `Mathlib.Analysis.Convex.Combination`.

**Recommendation.** Ship S2-B₁ next (~5-10 min wall-clock once docker is
available). Defer S2-B₂ to a future S2-C PREP that fully pins the
embedding-transport machinery.

**Mathlib v4.26.0 bearer re-verification** (via GitHub raw at tag
`v4.26.0`; researcher worktree `.lake` symlink loop precludes the local
lake-pinned audit used in Sessions 11–17):

| Bearer (S2-B₁)        | Location                                               | Use                              |
|-----------------------|---------------------------------------------------------|----------------------------------|
| `Nat.lt_succ_self`    | `Mathlib/Data/Nat/Defs.lean`                            | `K < K + 1` discharge            |

| Bearer (S2-B₂ preliminary) | Location                                            | Use                              |
|----------------------------|------------------------------------------------------|----------------------------------|
| `lp.single`                | `Mathlib/Analysis/Normed/Lp/lpSpace.lean:883`        | Per-index basis vector in `lp`   |
| `lp.lsingle`               | `Mathlib/Analysis/Normed/Lp/lpSpace.lean:943`        | `lp.single` as `LinearMap`       |
| `lp.isometry_single`       | `Mathlib/Analysis/Normed/Lp/lpSpace.lean:980`        | Witnesses isometry of `lp.single`|
| `lp.singleContinuousLinearMap` | `Mathlib/Analysis/Normed/Lp/lpSpace.lean:998`    | `lp.single` as `ContinuousLinearMap` |
| `AffineMap.image_convexHull` | `Mathlib/Analysis/Convex/Combination.lean` (TBD)   | Pushforward of convex hulls       |

All S2-A bearers (`Finset.smul_sum`, `convexHull_pair`,
`convex_convexHull`, `subset_convexHull`, `finrank_euclideanSpace_fin`)
remain valid at the lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

**Risks identified**: none material for S2-B₁ (single Mathlib bearer,
two local bearers, three-line proof). S2-B₂ is high-complexity and
multi-session; the §4 design identifies the embedding-transport step as
the single load-bearing non-trivial piece.

**Race-safety log.**
* Pre-claim probe: 0 open OQ01 PRs at session start (2026-06-09 ~17:18Z).
* Pre-edit probe: OQ01 `.lean` unchanged on `origin/main` since
  2026-06-05T01:45Z (S2-A ACT-4 ACT, PR #22322).
* HEAD probe: `origin/main` at `535c25c5e60`; this PREP branches from
  there.

**Files modified.**
* `research/problems/shapley-folkman-oq-01/sessions/2026-06-09-s2b-prep-truncation-lift-no-universal-bound.md`
  (CREATE) — full PREP document, §1–§9.
* `research/problems/shapley-folkman-oq-01/state.md` (this file) — this
  entry + header bump (iteration 17 → 18, phase ACT → PREP,
  last-updated 2026-06-04 → 2026-06-09).
* `src/data/research/problems/shapley-folkman-oq-01.json` — iter 17 → 18,
  `currentState.phase` ACT → PREP, `currentState.focus` updated to reflect
  S2-B PREP backing, `currentState.nextAction` updated to point at S2-B₁
  §3.1 verbatim recipe, `knowledge.progressSummary` extended,
  `knowledge.nextSteps` refreshed, top `updatedAt` 2026-06-04 → 2026-06-09.

**No `.lean` source changes**, no `meta.json` edits, no `problem.md` /
`knowledge.md` / `approaches/` edits. The strategic-level S2-B plan
described under §137 of `knowledge.md` already covered the truncation
direction; this session adds only the tactical recipe layer.

**Iteration history update.**

| Iter | Phase | Mode | PR | Description |
|------|-------|------|----|----|
| 17   | ACT   | `.lean` | #22322 | S2-A ACT-4 ACT: `exists_tight_decomposition` (recipe executed). |
| 18 | PREP | doc | #22542 | S2-B PREP: truncation-lift design — split into S2-B₁ paste-ready recipe (~15 LOC, `no_universal_shapley_folkman_bound`) and S2-B₂ (`lp 2` lift) multi-session deferred. |
| **19** | **ACT** | **`.lean`** | **(this PR)** | **S2-B₁ ACT: `no_universal_shapley_folkman_bound` (recipe executed). +33 LOC (306 → 339), +1 theorem (6 → 7), 0 sorries / axioms; Docker build clean (231s, 7744/7744).** |

**Next action.** S2-B₁ ACT: paste session §3.1 verbatim into
`proofs/Proofs/ShapleyFolkmanOQ01.lean` immediately before
`end ShapleyFolkmanOQ01` (line 306, after `exists_tight_decomposition`),
run `./proofs/scripts/docker-build.sh Proofs.ShapleyFolkmanOQ01`,
apply §3.4 fallbacks if any sub-step misfires (low risk; the body is a
three-tactic body). Or pivot to gallery entry creation (enricher scope).

## Session 17 — S2-A ACT-4 ACT: paste-ready recipe executed (researcher-1, 2026-06-04)

**Mode.** ACT (Lean code change; documentation update; PR create).

**Outcome.** Executed the Session 16 (S2-A ACT-4 PREP, researcher-1,
2026-06-04) paste-ready Lean recipe verbatim, completing the S2-A line
of the OQ01 work. The parent `shapley_folkman` upper bound
`card ≤ Module.finrank ℝ E` is now demonstrated to be **both**:

* **unavoidable** — via `tight_excess_count` (S2-A ACT-2, every
  decomposition of the tightness midpoint achieves `card = N`);
* **achievable** — via this new `exists_tight_decomposition`
  (Σ-witnessed by the explicit `midpointDecomp` construction).

The existence form closes the S2-A ACT-3 sharpness corollary's
"Next-step register" entry from Session 15. No new Mathlib gaps; the
recipe uses only the five v4.26.0 bearers pinned in Session 16 §2.

**File delta** (`proofs/Proofs/ShapleyFolkmanOQ01.lean`):

| | Before | After | Delta |
|---|---|---|---|
| LOC | 228 | 306 | +78 (incl. ~46 LOC docstrings) |
| theorems | 4 | 6 | +2 (`midpoint_mem_convexHull_pair_zero_basis`, `exists_tight_decomposition`) |
| noncomputable defs | 0 | 1 | +1 (`midpointDecomp`) |
| local sorries | 0 | 0 | 0 |
| local axioms | 0 | 0 | 0 |
| inherited axioms | 5 | 5 | 0 |

**Build status.** PR CI will verify. The researcher worktree `.lake`
symlink loop prevents local docker build — same trap documented in
Session 16 §1 and in many prior sessions. If any of the four
fallback-flagged subproofs (Session 16 §5: simp on set-literal
membership, `Finset.smul_sum` binder mismatch, `absurd` elaboration,
`noncomputable` propagation) fails in CI, a follow-up doctor PR
applies the appropriate fallback verbatim.

**Risk assessment.** Moderate. The recipe is detailed and citation-pinned
to v4.26.0 lake SHA, but the three named results have more moving parts
than the previous trivial cases on other slugs. Failure modes are pre-
documented with fallback paths.

## Session 16 — S2-A ACT-4 PREP: `exists_tight_decomposition` paste-ready Lean recipe (researcher-1, 2026-06-04)

**Mode.** PREP (doc-only; no `.lean` / no meta.json edits).

## Session 16 — S2-A ACT-4 PREP: `exists_tight_decomposition` paste-ready Lean recipe (researcher-1, 2026-06-04)

**Mode.** PREP (doc-only; no `.lean` / no meta.json edits).

**Outcome.** Materialised the long-flagged S2-A ACT-4 follow-up
(Session 15's §13 line 132–136 Next-step register and JSON
`currentState.nextAction`) into a citation-pinned 32-LOC Lean recipe ready
to drop into `proofs/Proofs/ShapleyFolkmanOQ01.lean` immediately before
`end ShapleyFolkmanOQ01`.

**Why a PREP this iteration.** Docker daemon unavailable at session start
(`docker images` → `Cannot connect to the Docker daemon`). Project safety
policy (CLAUDE.md §DANGER) forbids direct `lake build`, so a Lean ACT pass
that adds new theorems without build verification would risk introducing
silent typeclass / elaboration errors. PREP is the safe move when docker
is down. See session §1 for the build-vs-block reasoning.

**Three named results scoped** (full Lean bodies in session §3):

1. **Helper lemma `midpoint_mem_convexHull_pair_zero_basis`** (~23 LOC).
   `(1/2) • e_i ∈ convexHull ℝ {0, e_i}`. Uses the same
   `convex_convexHull` + `subset_convexHull` chain as the existing
   `mem_convexHull_finset_sum` (line 118–123 of the OQ01 file).

2. **Definition `midpointDecomp`** (~14 LOC; `noncomputable def`).
   The natural midpoint decomposition with `point i = (1/2) • e_i`, four
   structure fields filled. The `sum_eq` field uses `← Finset.smul_sum`
   (verified at `Mathlib/Algebra/BigOperators/GroupWithZero/Action.lean:57–59`).
   The `point_eq_zero` field is vacuous (`absurd (Finset.mem_univ i) hi`).

3. **Theorem `exists_tight_decomposition`** (~12 LOC).
   Anonymous constructor `⟨midpointDecomp N, tight_excess_eq_finrank N (midpointDecomp N)⟩`.
   Combines the existence witness with the parameterised sharpness
   corollary (S2-A ACT-3, line 216 of OQ01) to give the existence form
   `∃ D, card = Module.finrank ℝ E`.

**Mathlib v4.26.0 bearer re-verification** at lake SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| Bearer | Module | Line |
|---|---|---|
| `Finset.smul_sum` | `Algebra/BigOperators/GroupWithZero/Action.lean` | 57–59 |
| `convexHull_pair` | `Analysis/Convex/Hull.lean` | 124 |
| `convex_convexHull` | `Analysis/Convex/Hull.lean` | 53 |
| `subset_convexHull` | `Analysis/Convex/Hull.lean` | 50–51 |
| `finrank_euclideanSpace_fin` | `Analysis/InnerProductSpace/PiL2.lean` | 193–194 |

All five bearers source-verified by direct read of the lake-pinned Mathlib
clone at `proofs/.lake/packages/mathlib/`. No new bearers required beyond
those already used in the OQ01 file.

**Fallbacks documented** (session §5):
1. `subset_convexHull ℝ _ (by simp)` failure → explicit
   `Set.mem_insert _ _` / `Set.mem_insert_of_mem _ rfl`.
2. `rw [← Finset.smul_sum]` binder mismatch → `simp only [← Finset.smul_sum]`
   or explicit `conv_lhs` rewrite.
3. `absurd` elaboration failure → `(hi (Finset.mem_univ i)).elim`.
4. `noncomputable` rejection → remove `noncomputable`.

**Risks identified**: none material. The §3 recipe uses only bearers
that the existing OQ01 file already uses (`subset_convexHull`,
`convex_convexHull`, `EuclideanSpace.single`, parent `Decomposition`),
with one new bearer (`Finset.smul_sum`) that's a standard Mathlib lemma
in a stable location.

**Estimated ACT-time profile** (next docker-available iteration):
~5–10 min total wall-clock (paste 50 LOC → ~30s docker build on warm
cache → confirm clean → commit + push + PR).

**Race-safety log.**
* Pre-claim probe (this session):
  `gh pr list --search "shapley-folkman-oq-01 in:title" --state open` → 0 open PRs.
* Pre-edit probe: OQ01 `.lean` unchanged on `origin/main` since
  2026-06-01T02:20Z (S2-A ACT-3 PR #21747 merge).
* Bearer pin probe: lake SHA still
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

**Files modified.**
* `research/problems/shapley-folkman-oq-01/sessions/2026-06-04-s2a-act-4-prep-existence-form-recipe.md` (CREATE) — full PREP document, §1–§13.
* `research/problems/shapley-folkman-oq-01/state.md` (this file) — this entry + header bump (iteration 15 → 16, phase ACT → PREP, last-updated 2026-05-31 → 2026-06-04).
* `src/data/research/problems/shapley-folkman-oq-01.json` — iter 15 → 16, `currentState.phase` ACT → PREP, `currentState.focus` updated to reflect S2-A ACT-4 PREP backing, `currentState.nextAction` updated, `knowledge.nextSteps` refreshed, top `updatedAt` 2026-05-31 → 2026-06-04.

**No `.lean` source changes**, no meta.json edits, no `problem.md` /
`knowledge.md` / `approaches/` edits. The strategic-level S2-A ACT-4 plan
in `knowledge.md` already covered the existence form; this session adds
only the tactical Lean-recipe layer.

**Iteration history update** (extends Session 15's table).

| Iter | Phase | Mode | PR | Description |
|------|-------|------|----|--|
| 15 | ACT | `.lean` | #21747 | S2-A ACT-3: sharpness corollary `tight_excess_eq_finrank`. |
| **16** | **PREP** | **doc** | **(this)** | **S2-A ACT-4 PREP: `exists_tight_decomposition` paste-ready Lean recipe (32 LOC across 3 named results) + Mathlib v4.26.0 bearer audit (5 bearers re-verified at lake SHA). Doc-only; no `.lean` change, no meta.json change. Docker unavailable; ACT deferred to next iteration.** |

**Next action.** S2-A ACT-4 ACT pass: paste session §3.1–§3.3 verbatim into
`proofs/Proofs/ShapleyFolkmanOQ01.lean` immediately before
`end ShapleyFolkmanOQ01` (line 228), run
`./proofs/scripts/docker-build.sh Proofs.ShapleyFolkmanOQ01`, apply §5
fallbacks if any subproof misfires (low risk; all three are routine
constructions). Or pivot to gallery entry creation (enricher scope).

## Session 15 — S2-A ACT-3: sharpness corollary `tight_excess_eq_finrank` (researcher-1, 2026-05-31)

**Mode.** Lean ACT (build verified).

**Outcome.** `proofs/Proofs/ShapleyFolkmanOQ01.lean` now declares
`tight_excess_eq_finrank`, the long-flagged S2-A ACT-3 corollary from
S5 PREP §10 / state.md Iter 14 Next-Action: given any decomposition of
the tightness example, its excess count equals
`Module.finrank ℝ (EuclideanSpace ℝ (Fin N))`. Two-line proof: rewrite
via `tight_excess_count` (`card = N`) and `finrank_euclideanSpace_fin`
(`N = Module.finrank ℝ (EuclideanSpace ℝ (Fin N))`).

**File delta**: 204 → 228 LOC (+24); theorems 3 → 4 (+1); axioms 0 → 0;
sorries 0 → 0.

**Docker build verified**: `✔ [7744/7744] Built Proofs.ShapleyFolkmanOQ01 (23s)`
on warm cache.  Pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

**Mathematical significance.** The corollary translates S2-A ACT-2's
`tight_excess_count = N` into the parent's `Module.finrank ℝ E` vocabulary,
making the sharpness claim directly comparable to the parent
`shapley_folkman` upper bound `card ≤ Module.finrank ℝ E`. Existence of
such a decomposition (via the natural midpoint construction
`point i = (1/2) • e_i`) is **not** established here — left as S2-A ACT-4
follow-up. The parameterised form is mathematically meaningful in its own
right (any decomposition achieves the dimension count).

See `sessions/2026-05-31-s2a-act-3-sharpness-corollary.md` for the recipe,
bearer pins, build log, and follow-up register.

**Next action**: S2-A ACT-4 (existence form, ~15-25 LOC, midpoint
decomposition construction via `Convex.midpoint_mem` or `convexHull_pair`).
Or pivot to gallery entry creation (enricher scope:
`src/data/proofs/shapley-folkman-oq-01/meta.json` with `status: axiomatized`,
5 inherited axioms, `theoremCount: 4`).

## Session 13 — S2-A ACT-2: discharge both `ShapleyFolkmanOQ01.lean` sorries (researcher-8, 2026-05-16)

**Mode.** Lean ACT (build verified).

**Outcome.** `proofs/Proofs/ShapleyFolkmanOQ01.lean` now compiles with
zero sorries (was 2) and zero local axioms (5 inherited from
`Proofs.ShapleyFolkman` remain). +74 LOC (file 130 → 204).

**Recipes used.**
* `mem_convexHull_finset_sum` (lines 87–123, was 87–93 sorry):
  S5 PREP §3 (#18929) 5-step skeleton — verbatim except §3.1 fix
  below.
* `tight_excess_count` (lines 149–202, was 119–128 sorry):
  S7 PREP §5 (#19276) 48-LOC body — verbatim except §3.2 + §3.3
  fixes below.

**Three ACT-time elaboration fixes** (full detail in
`sessions/2026-05-16-s2a-act-2-discharge-both-sorries.md`):

1. **S5 §3 Step 1**: `(fun i _ => by exact Set.mem_insert _ _)` →
   `(fun i _ => by simp)`. The S5 PREP closer's metavariable
   inference confuses `Set.mem_insert` (expected `0 ∈ insert 0 _`
   becomes `0 ∈ insert (∑ i, 0) _`). `by simp` discharges via the
   default simp set unfolding `Set.mem_insert_iff`.

2. **S7 §5 Step 4** (linarith breakthrough): swap
   `EuclideanSpace.single_apply` → `Pi.single_apply`, add
   `mul_ite, mul_one, mul_zero`. The kernel form retained
   `Pi.single x 1 j` after `EuclideanSpace.single_apply`'s unfolding
   level; `Pi.single_apply` exposes the `if x = j then 1 else 0`
   form so `mul_ite` collapses the summand and `Finset.sum_ite_eq'`
   (turned out unused after the simp) is no longer needed.

3. **S7 §5 Step 5** (both case branches): drop the two
   `norm_num at hcoord` lines (lines 195, 198 in the recipe). The
   prior `simp [PiLp.smul_apply, EuclideanSpace.single_apply]
   at hcoord` derives `False` from `(1/2 : ℝ) = 0` (and `= 1` in
   the second branch) via the simp normalisation, closing the
   case goal in-place. S7 PREP §4's Bug 3 documented the worst
   case; the actual elaboration is friendlier.

**S7 PREP §7 informational concerns resolved.**
1. `convexHull_pair_zero_basis_extract` helper (5-line tactic body
   from S2-A ACT-1) builds cleanly at the pin — no fallback needed.
2. `D.mem_convexHull` field access works directly on the parent
   `ShapleyFolkman.Decomposition` structure — no re-projection.

**Build log.** Single Docker pass after revisions (~47s on warm cache):
```
$ ./proofs/scripts/docker-build.sh Proofs.ShapleyFolkmanOQ01
✔ [7744/7744] Built Proofs.ShapleyFolkmanOQ01 (47s)
Build completed successfully (7744 jobs).
=== Build succeeded ===
```

**Race log (historical, now resolved).** PR #19361 (S10 STATE-SYNC
by researcher-1, opened 2026-05-16T01:32Z) was the only other open
PR on this slug at S2-A ACT-2 session start. The race resolved
cleanly: S2-A ACT-2 (#19399) merged first at 2026-05-16T03:52:04Z,
S10 STATE-SYNC (#19361) merged second at 2026-05-16T04:45:00Z, no
state.md/JSON conflict (S10 only added a new sessions/ file). See
the S2-A ACT-2 session doc §7 for the resolution policy, and S14
STATE-SYNC §3 for the post-merge reconciliation.

**Iteration history.**
| Iter | Phase | Mode | PR | Description |
|------|-------|------|----|--|
| 1 | OBSERVE | doc | #18345 | S1: literal extension fails; Aumann/Lyapunov analogs. |
| 2 | OBSERVE | doc | #18414 | S1b: Aumann/Lyapunov Mathlib prereq audit. |
| 3 | PREP | doc | #18397 | S2: Approach C `ℓ²` counter-example design (342 LOC). |
| 4 | PREP | doc | #18452 | S2b: numeric verification at N=1..4. |
| 5 | PREP | doc | #18491 | S3: pair convex-hull extraction recipe. |
| 6 | PREP | doc | #18556 | S3b: Mathlib v4.26.0 citation audit; 3 phantom corrections. |
| 7 | PREP | doc | #18649 | S4: parent `ShapleyFolkman.lean` source audit + decidability. |
| 8 | ACT | `.lean` | #18854 | S2-A ACT-1: scaffold + helper + 2 sorries. |
| 9 | PREP | doc | #18929 | S5: `mem_convexHull_finset_sum` 5-step Lean skeleton. |
| 9.5 | STATE-SYNC | doc | #19003 | Record iter 9 in state.md + JSON. |
| 10 | PREP | doc | #19202 | S6: `tight_excess_count` 45-LOC drop-in recipe. |
| 11 | PREP | doc | #19276 | S7: sibling-audit of S6 §4, 3 bugs corrected, 48-LOC body. |
| 12 | STATE-SYNC | doc | #19361 | S10: absorb S6+S7 PREP merges + ACT-2 readiness gate via new sessions/ file (no state.md/JSON edit). MERGED 2026-05-16T04:45:00Z. |
| 13 | ACT | `.lean` | #19399 | S2-A ACT-2: discharge both sorries (`mem_convexHull_finset_sum` via S5 PREP §3 5-step skeleton + `tight_excess_count` via S7 PREP §5 48-LOC body, with 3 ACT-time elaboration fixes); build verified `✔ [7744/7744] (47s)`. File 130 → 204 LOC, sorries 2 → 0, 5 inherited axioms. MERGED 2026-05-16T03:52:04Z. |
| **14** | **STATE-SYNC** | **doc** | **(this)** | **S14: housekeeping — correct iter-history `(OPEN)` / `(this)` placeholders post-#19361 merge, refresh Race Log, append sessions/ note; no Lean / meta.json / Next Action changes (S2-A ACT-3 still the recommended next claim).** |

**Next Action.** See §9 of the session doc. Mechanic-grade follow-on:
S2-A ACT-3 (sharpness corollary, ~15 LOC, combining `tight_excess_count`
with parent `shapley_folkman` + `finrank_euclideanSpace_fin`).
Enricher scope: gallery entry creation in
`src/data/proofs/shapley-folkman-oq-01/`.



## Session 9 — S5 PREP STATE-SYNC: record merged S5 PREP recipe; ACT-2 path now backed by verbatim Lean skeletons for both sorries (researcher-12, 2026-05-14)

**Mode.** STATE-SYNC (doc-only).

**Reason.** PR #18929 (S5 PREP, merged 2026-05-13T23:06 UTC, researcher-4)
landed the verbatim 5-step Lean recipe for the first surviving sorry
(`mem_convexHull_finset_sum` at `proofs/Proofs/ShapleyFolkmanOQ01.lean:87-93`)
and explicitly scoped itself doc-only: "No edits to `problem.md`, `state.md`,
`knowledge.md`, ... `.json`". So state.md and the JSON lagged by one merged
PREP. This session ships the catch-up entry within the 2-per-session
STATE-SYNC cap, without touching the Lean source or the S5 PREP session file.

**What S5 PREP supplied** (`sessions/2026-05-13-s5-prep-mem-convexhull-finset-sum-discharge-recipe.md`,
+526 LOC, doc-only):

1. **§2 — Mathlib v4.26.0 lemma inventory** with verbatim source citations,
   verified at the lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:
   * `Set.finset_sum_mem_finset_sum` (n-ary additive Minkowski membership;
     `Mathlib/Algebra/Group/Pointwise/Set/BigOperators.lean:142` — multiplicative
     statement with `@[to_additive]`).
   * `subset_convexHull` (`Mathlib/Analysis/Convex/Hull.lean:50`).
   * `convex_convexHull` (`Mathlib/Analysis/Convex/Hull.lean:53`).
   * `Convex` / `StarConvex` two-point unfolding
     (`Mathlib/Analysis/Convex/Basic.lean:49` +
     `Mathlib/Analysis/Convex/Star.lean:76`).

2. **§3 — 5-step Lean skeleton** (~18 LOC, mid-proof variables
   `h0`, `hsum`, `hmid` for `0 ∈ ∑ S_i`, `∑ e_i ∈ ∑ S_i`, midpoint
   rewrite) closing on `(convex_convexHull ℝ _) (subset_convexHull ℝ _ h0)
   (subset_convexHull ℝ _ hsum) ...` with three `norm_num` side
   conditions. (Note: Session 8 §4 "Next Action" §2 had named
   `Set.add_mem_finset_sum`; S5 PREP §2 supersedes that with the actual
   Mathlib v4.26.0 name `Set.finset_sum_mem_finset_sum`.)

3. **§4 step-by-step justification**, **§5 failure modes + fallbacks**
   (segment-route at §5.3 as backup if `convex_convexHull` two-point combo
   misfires), **§6 decision tree**, **§7** rationale for primary route,
   **§8 anti-targets** (do NOT prove `convexHull ℝ (∑ S_i) = [0, 1]^N`;
   do NOT use `centerMass`).

**Effect on ACT-2 readiness.** Combined with the merged S3 PREP §4 + S4
PREP §3 recipe for the sibling sorry `tight_excess_count` (coordinate-eval
via `EuclideanSpace.single_apply`), **both surviving sorries in
`ShapleyFolkmanOQ01.lean` now have verbatim Lean recipes ready for an
ACT-2 docker-build pass**. The remaining ACT-2 uncertainty is build-side
(does `rw [convexHull_pair]` succeed on the helper lemma at line 58?
S3 PREP §3.2 segment-route fallback is documented).

**Files modified this session.**
* `research/problems/shapley-folkman-oq-01/state.md` — this entry +
  header bump (iteration 8 → 9, last-updated 2026-05-13 → 2026-05-14).
* `src/data/research/problems/shapley-folkman-oq-01.json` —
  `currentState.iteration` 8 → 9, `currentState.focus` extends to note
  S5 PREP recipe availability, `currentState.nextAction` tightens to
  reference S5 PREP §3 verbatim (replacing the `Set.add_mem_finset_sum`
  guess with `Set.finset_sum_mem_finset_sum`), `knowledge.progressSummary`
  extends, `knowledge.nextSteps` populated, `currentState.attemptCounts.total`
  8 → 9, top `updatedAt` 2026-05-13 → 2026-05-14.

**No Lean source changes**, no S5 PREP session file edits, no
`problem.md` / `knowledge.md` / `approaches/` / `lean/` / `literature/`
edits. STATE-SYNC #1 of 2 for this researcher-12 session.

## Session 8 — S2-A ACT-1: file scaffold + helper lemma + main theorem signatures (researcher-1, 2026-05-13)

**Mode.** Lean ACT (build pending).

**Outcome.** First `.lean` discharge after 7 doc-only PREP sessions
(S1, S1b, S2, S2b, S3, S3b, S4). Landed
`proofs/Proofs/ShapleyFolkmanOQ01.lean` (~130 LOC, 0 axioms) with:

1. **Scaffold**: imports (`Proofs.ShapleyFolkman` + targeted Mathlib
   imports per S4 PREP §7.1), namespace `ShapleyFolkmanOQ01`,
   `attribute [local instance] Classical.propDecidable` per S4 PREP
   §3.1 / §7.3, `proofs/Proofs.lean` registration (alphabetical
   between `ShapleyFolkmanAristotle` and `ShapleyFolkmanOQ03`).

2. **`convexHull_pair_zero_basis_extract`** helper lemma
   (S3 PREP §3.1 verbatim + S3b PREP §3.3 corrections): from
   `y ∈ convexHull ℝ {0, e_i}` extract `t ∈ [0, 1]` with
   `y = t • e_i`. Tactic body **attempted** (5 lines: `rw
   [convexHull_pair]`, `rcases`, `refine`, `linarith`,
   `rw [smul_zero, zero_add]`). Build pending.

3. **`mem_convexHull_finset_sum`** (membership claim,
   `sorry`-stubbed): `(1/2) • ∑ e_i ∈ convexHull ℝ (∑ S_i)`.
   Proof skeleton in S2b PREP §2 (midpoint of `0 ∈ ∑ S_i` and
   `∑ e_i ∈ ∑ S_i`); deferred to S2-A ACT-2.

4. **`tight_excess_count`** (main tightness theorem,
   `sorry`-stubbed): `∀ D : Decomposition, D.excessIndices.card = N`.
   Proof skeleton in S3 PREP §4 + S4 PREP §3 (coordinate-eval
   route via `EuclideanSpace.single_apply`); deferred to
   S2-A ACT-2.

**Files modified.**
* `proofs/Proofs/ShapleyFolkmanOQ01.lean` — new file, 130 LOC,
  3 named results (1 with attempted proof, 2 `sorry`-stubbed),
  0 axioms.
* `proofs/Proofs.lean` — added `import Proofs.ShapleyFolkmanOQ01`
  (alphabetical position, manual edit; the generator script
  `.lean/scripts/generate-proofs-imports.sh` would re-sort identically).
* `research/problems/shapley-folkman-oq-01/state.md` — this entry +
  Iteration / Phase / Last Updated bump.
* `src/data/research/problems/shapley-folkman-oq-01.json` — phase
  ACT, iteration 8, knowledge.builtItems += `.lean` file,
  knowledge.progressSummary += S2-A ACT-1 note.

**Build status.** Not attempted in this session per Docker-build
risk policy (10+ min Mathlib clone, 30-min daemon respawn risk per
`feedback_researcher_lake_symlink_loop_and_wipe.md`). Helper lemma
tactic body is paper-correct per S3 PREP §3.1 + S3b PREP §3.3
audit; build verification deferred to doctor or next researcher.

**Iteration history.**
| Iter | Phase | Mode | PR | Description |
|------|-------|------|----|--|
| 1 | OBSERVE | doc | #18345 | S1: literal extension fails; Aumann/Lyapunov analogs. |
| 2 | OBSERVE | doc | #18414 | S1b: Aumann/Lyapunov Mathlib prereq audit. |
| 3 | PREP | doc | #18397 | S2: Approach C `ℓ²` counter-example design (342 LOC). |
| 4 | PREP | doc | #18452 | S2b: numeric verification at N=1..4. |
| 5 | PREP | doc | #18491 | S3: pair convex-hull extraction recipe. |
| 6 | PREP | doc | #18556 | S3b: Mathlib v4.26.0 citation audit; 3 phantom corrections. |
| 7 | PREP | doc | #18649 | S4: parent `ShapleyFolkman.lean` source audit + decidability. |
| 8 | **ACT** | **`.lean`** | #18854 | **S2-A ACT-1: scaffold + helper + 2 stubs.** |
| 9 | PREP | doc | #18929 | **S5: `mem_convexHull_finset_sum` 5-step Lean skeleton (18 LOC, named Mathlib lemmas).** |
| 9.5 | STATE-SYNC | doc | (this) | Record iter 9 in state.md + JSON. |

## Session 1 — S1 OBSERVE: literal extension fails; Aumann/Lyapunov are the correct infinite-dim analogs (researcher-1, 2026-05-12)

## Session 1 — S1 OBSERVE: literal extension fails; Aumann/Lyapunov are the correct infinite-dim analogs (researcher-1, 2026-05-12)

**Mode.** Doc-only (no `.lean` changes).

**Outcome.** Filled the seeker-init template. The seeker note
suggested "finrank → suitable dimension"; this session establishes
that **no drop-in replacement exists**, and that the correct
infinite-dim analogs are Aumann's set-valued integral (1965) and
Lyapunov's convexity theorem (1940) — neither of which is in
Mathlib.

**Key findings:**

1. **`Module.finrank ℝ ℓ² = 0` collapses the bound.**
   In Lean's convention, `Module.finrank` of any non-finite-dim
   module is `0`. The literal extension `at most finrank ℝ E
   excess indices` becomes `at most 0 excess indices`, which is
   vacuously false for any Minkowski sum with non-convex
   summands.

2. **The Carathéodory step inside `shapley_folkman` is genuinely
   finite-dim.** The proof at `ShapleyFolkman.lean:151–199`
   uses `excess_vertices_affine_dependent` which depends
   essentially on `Module.finrank ℝ E + 1 < n ⟹ AffineDependent`.
   In infinite-dim, `AffineIndependent` can hold for arbitrarily
   large index sets, so the affine-dependent extraction step
   has no analog.

3. **The CORRECT infinite-dim analog is Aumann's theorem
   (1965)**:
   For an atomless measure space `(Ω, μ)` and a measurable
   set-valued map `F : Ω → Set H` (`H` separable Hilbert /
   Banach), the integral `∫ F dμ` is convex. The proof goes via
   **Lyapunov's convexity theorem (1940)**: the range of an
   atomless ℝⁿ-valued vector measure is convex and compact.

4. **Mathlib status of the upstream theorems:**
   - `MeasureTheory.Measure.IsAtom` is present.
   - Vector-valued integration into Banach spaces is present
     (`MeasureTheory.integral` for Banach codomains).
   - **`Lyapunov`-named theorem** is NOT present
     (`grep -rn 'Lyapunov\|lyapunov' mathlib_path/Mathlib/` returns
     zero hits inside `Mathlib.MeasureTheory.*`).
   - **`Aumann`-named theorem on set-valued integrals** is NOT
     present.

5. **Approach C — explicit `ℓ²` counter-example.** A concrete
   construction `S : ℕ → Set ℓ²` with `S i = {0, eᵢ}` and the
   point `x = (1/2) ∑ᵢ eᵢ ∈ convexHull ℝ (∑ᵢ Sᵢ)` requires
   **every** index `i` to contribute non-trivially (since each
   `e i` axis is non-overlapping). This refutes any bounded
   excess-index count and is the narrowest formalization of
   the negative result.

**Files modified.**
* `research/problems/shapley-folkman-oq-01/problem.md` — full
  problem statement, three approaches, references.
* `research/problems/shapley-folkman-oq-01/state.md` — this entry.
* `research/problems/shapley-folkman-oq-01/knowledge.md` —
  Mathlib API map (present + missing), three viable approaches.
* `research/problems/shapley-folkman-oq-01/sessions/2026-05-12-s01-observe.md` —
  full S1 OBSERVE report: vacuity argument for `finrank=0`,
  Aumann/Lyapunov chain, concrete `ℓ²` counter-example sketch.

**Build status.** No `.lean` changes; no build attempted.

## Current Focus
S1 OBSERVE doc-only deliverable complete. Approach C
(`ℓ²` counter-example) is the narrowest viable S2 ACT target.
Approaches A/B require formalizing Lyapunov's theorem first
(8+ sessions of upstream work, deferred).

## Active Approach
**Approach C — explicit `ℓ²` counter-example** as the narrowest
S2 ACT seed. Formalize `shapley_folkman_fails_in_infinite_dim`
with `E = EuclideanSpace ℝ ℕ` (separable Hilbert; in Mathlib
as `EuclideanSpace`) or `lp.PiLp 2` if that is more ergonomic.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (Approach A/B/C all considered; C selected)

## Blockers
None for Approach C. Approaches A/B are blocked on
Lyapunov's convexity theorem (multi-session prerequisite,
not in Mathlib).

## Next Action

**Updated by Session 18 (S2-B PREP, researcher-1, 2026-06-09).** The
S2-A line is complete (Sessions 8, 13, 15, 17 — `.lean` ACTs; Sessions
9, 10, 11, 16 — PREP chains). The next paste-ready ACT target is:

**S2-B₁ ACT — `no_universal_shapley_folkman_bound`** (~15 LOC body +
~20 LOC docstring; file 306 → ~340 LOC):

1. Paste session §3.1 of
   `sessions/2026-06-09-s2b-prep-truncation-lift-no-universal-bound.md`
   verbatim into `proofs/Proofs/ShapleyFolkmanOQ01.lean` immediately
   before `end ShapleyFolkmanOQ01` (line 306, after the
   `exists_tight_decomposition` theorem).
2. Run `./proofs/scripts/docker-build.sh Proofs.ShapleyFolkmanOQ01` —
   expected ~25-30s on warm cache. (Researcher worktrees may need the
   doctor or CI to do this step due to `.lake` symlink loops.)
3. Apply §3.4 fallbacks if any sub-step misfires (low risk; the body is
   `refine ⟨midpointDecomp (K + 1), ?_⟩` + `rw [tight_excess_count …]` +
   `exact Nat.lt_succ_self K`).
4. Commit + push + open PR.

After S2-B₁ complete:
- **S2-B₂ PREP/ACT (multi-session, deferred to S2-C PREP)**: lift the
  finite-dim tightness to a genuine `lp (fun _ : ℕ => ℝ) 2` failure
  result via a linear-isometric embedding `EuclideanSpace ℝ (Fin N)
  →ₗᵢ lp …` and a `Decomposition.map` transport. ~150-250 LOC,
  3-5 sessions. Bearer pins for `lp.single` / `lp.lsingle` /
  `lp.isometry_single` / `lp.singleContinuousLinearMap` recorded in
  Session 18 §4.4; `AffineMap.image_convexHull` location still to pin.
- **S3 ACT (deferred)**: Aumann set-valued integral *statement*-only.
  Blocks on Mathlib not having `MeasureTheory.set_valued_integral`.
- **S4 ACT (multi-session, deferred)**: Lyapunov convexity upstream.
  ~200-300 LOC of new Mathlib measure theory; out of scope for this
  research slug.

Enricher-scope (parallel, when S2-B₁ lands): gallery entry creation in
`src/data/proofs/shapley-folkman-oq-01/` with `status: axiomatized`,
`badge: axiom`, `theoremCount: 7` (post-S2-B₁), `defCount: 1`,
`sorryCount: 0`, `inheritedAxioms: 5`.
