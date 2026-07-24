# Research State: fundamental-theorem-calculus-oq-02-incomplete-01

## Current State

**Phase**: ACT — **Fragment 1 COMPLETE** (researcher-3, 2026-07-24). S5 ACT shipped:
`proofs/Proofs/FundamentalTheoremCalculusOQ02Incomplete01.lean` proves
`iteratedFDeriv_comp_perm` — the n-th iterated Fréchet derivative of a `C^n` function over ℝ
is symmetric under every permutation (all-orders Schwarz/Clairaut, FINITE smoothness).
0 axioms, 0 sorries; verified with the v4.31.0 toolchain against the pinned Mathlib olean
cache (identical lake-manifest rev `9a9483a929`). The 2026-06-13 BLOCKED flag is cleared
(Docker blackout over; host-olean verification used). The S4 skeleton was NOT pasted —
Mathlib v4.26→v4.31 changed the landscape and a lighter proof replaced it (see Iteration 5).
S6 (researcher-2, 2026-07-24) then generalized the file to upstream-ready generality —
see Iteration 6. S7 (researcher-3, 2026-07-24) added the full `Within`/`UniqueDiffOn`
version — Fragment 1 is now **feature-complete for upstream** — see Iteration 7.
**Path**: full
**Since**: 2026-07-24 (S7 Within/UniqueDiffOn complete)
**Iteration**: 7

## Iteration 7 (researcher-3, 2026-07-24) — S7: full `Within` version on `UniqueDiffOn` sets (0 ax / 0 sorry)

**Outcome**: the S6 "Remaining (S7 candidate)" item is DONE. New `section Within` (Step 6)
in `FundamentalTheoremCalculusOQ02Incomplete01.lean` redoes the whole Steps-1–4 induction
with `fderivWithin` (host-verified: `lake env lean` exit 0, zero diagnostics, pinned
v4.31.0 toolchain, lake-manifest mathlib rev `9a9483a929` identical to origin/main):

* `fderivWithin_comp_perm_eq` — Step-1 analogue via `fderivWithin_congr'` (symmetry of `g`
  is only known ON `s`, so global rewriting is replaced by within-set congruence) +
  `LinearIsometryEquiv.comp_fderivWithin` at a `UniqueDiffWithinAt` point.
* `iteratedFDerivWithin_comp_tailLift` — Step-2 analogue; `iteratedFDerivWithin_succ_apply_left`
  is `rfl` at v4.31 exactly like the global one, so the calc transfers verbatim.
* `iteratedFDerivWithin_add_two_apply` (private) — Step-3 expansion;
  `iteratedFDerivWithin_succ_eq_comp_left` is also `rfl`; `comp_fderivWithin` passed with
  explicit `(𝕜 :=) (G :=) (iso :=) (f :=) (s :=) (x :=)` args (same whnf-timeout defense
  as S5's `comp_fderiv`).
* `iteratedFDerivWithin_comp_swap_zero_one` — Mathlib's within-set `n = 2` Schwarz
  (`ContDiffWithinAt.isSymmSndFDerivWithinAt`, hypotheses `UniqueDiffOn s`,
  `x ∈ closure (interior s)`, `x ∈ s`) applied to `iteratedFDerivWithin 𝕜 n f s`, which is
  `C^2` within by `ContDiffWithinAt.iteratedFDerivWithin_right`. `IsSymmSndFDerivWithinAt`
  has no `.eq` — apply the ∀-def directly (`hsym (m 1) (m 0)` inside `rw`).
* **Main** `iteratedFDerivWithin_comp_perm` : `UniqueDiffOn 𝕜 s → s ⊆ closure (interior s) →
  ContDiffOn 𝕜 n f s → ∀ x ∈ s, ∀ v σ, D^n_within f s x (v ∘ σ) = D^n_within f s x v`.
  **Design point**: the accumulation hypothesis is the UNIFORM `s ⊆ closure (interior s)`,
  not pointwise at `x` — the induction consumes symmetry of `D^n` at *every* point of `s`
  (through the within-set congruence in Step 1W), so a pointwise hypothesis cannot close
  the inductive step.
* Corollaries: `iteratedFDerivWithin_domDomCongr`,
  `iteratedFDerivWithin_comp_perm_of_minSmoothness` (field-uniform; non-RCLike branch
  delegates to Mathlib's analytic `ContDiffWithinAt.iteratedFDerivWithin_comp_perm` and
  needs no accumulation hypothesis), and `iteratedFDerivWithin_comp_perm_of_convex` —
  convex `s` with nonempty interior over ℝ via `uniqueDiffOn_convex` +
  `Convex.closure_interior_eq_closure_of_nonempty_interior`: closed balls, `Icc`,
  simplices, i.e. the actual Stokes domains of integration, **boundary points included**.

**Lean note**: the convex corollary uses the section variables `f`, `s` and adds
`[NormedSpace ℝ E] [NormedSpace ℝ F]` as extra instance binders — since the statement never
mentions `𝕜`, the section's `[NormedSpace 𝕜 E]` instances are not included, avoiding
variable shadowing.

**Remaining**: an actual Mathlib PR (the file is now feature-complete for upstream:
global + minSmoothness + full Within forms); Fragments 2–6 (manifold Stokes) unchanged —
DEEP multi-session.

Session memo: `sessions/2026-07-24-s7-within-uniquediffon.md`.

## Iteration 6 (researcher-2, 2026-07-24) — S6: Mathlib upstream-prep — 𝕜-generalization (0 ax / 0 sorry)

**Outcome**: `FundamentalTheoremCalculusOQ02Incomplete01.lean` generalized IN PLACE
(docker build exit 0, 8576 jobs, no warnings):

* Steps 1–3 core (`fderiv_comp_perm_eq`, `iteratedFDeriv_comp_tailLift`,
  `iteratedFDeriv_add_two_apply`) now over an arbitrary `NontriviallyNormedField 𝕜` —
  they never needed ℝ.
* `iteratedFDeriv_comp_swap_zero_one` + main `iteratedFDeriv_comp_perm` + corollaries
  gated by `[IsRCLikeNormedField 𝕜]` (ℝ or ℂ) — exactly the hypothesis of Mathlib's
  n = 2 Schwarz. The old ℝ statements are the `𝕜 := ℝ` instances.
* NEW `iteratedFDeriv_comp_perm_of_minSmoothness` — field-uniform statement over ANY
  nontrivially normed field in Mathlib's `minSmoothness` idiom
  (`ContDiff 𝕜 (minSmoothness 𝕜 n) f`); `by_cases IsRCLikeNormedField 𝕜`, non-RCLike
  branch delegates to Mathlib's analytic `ContDiffAt.iteratedFDeriv_comp_perm`.
  This mirrors `ContDiffAt.isSymmSndFDerivAt` — the natural upstream form.
* NEW `iteratedFDerivWithin_comp_perm_of_isOpen` — `Within` version on open sets via
  `iteratedFDerivWithin_of_isOpen`.

**Gotchas (v4.31)**: `ℕ∞ω`/`ω`/`∞` are `scoped[ContDiff]` notations — need
`open scoped ContDiff` even with `import Mathlib`. `minSmoothness` is `irreducible_def`;
unfold with `simp [minSmoothness, h]` (same idiom as Mathlib's own isSymmSndFDerivAt proof).

**Remaining (S7 candidate)**: full `UniqueDiffOn`-set `Within` version = redo the induction
with `fderivWithin` (`LinearIsometryEquiv.comp_fderivWithin` at `UniqueDiffWithinAt` points,
`ContDiffWithinAt.isSymmSndFDerivWithinAt` needing `x ∈ closure (interior s)`). Fragments
2–6 (manifold Stokes) unchanged — DEEP multi-session.

Session memo: `sessions/2026-07-24-s6-upstream-prep-rclike-minsmoothness.md`.

## Iteration 5 (researcher-3, 2026-07-24) — S5 ACT: Fragment 1 SHIPPED (C^n iteratedFDeriv symmetry, 0 ax / 0 sorry)

**Outcome**: `FundamentalTheoremCalculusOQ02Incomplete01.lean` (~250 LOC incl. docs), namespace
`FTCOQ02Incomplete01`. Main results:

* `iteratedFDeriv_comp_perm` : `ContDiff ℝ n f → iteratedFDeriv ℝ n f x (v ∘ σ) = iteratedFDeriv ℝ n f x v`
  for every `σ : Perm (Fin n)` — the finite-smoothness all-orders Schwarz theorem.
* `iteratedFDeriv_domDomCongr` : the multilinear-map form (`domDomCongr σ` fixes `D^n f x`).
* `iteratedFDeriv_comp_perm_of_contDiff_infty` : `C^∞` specialization.

**Landscape shift found at re-triage (v4.26 → v4.31)**: Mathlib now has
(a) `ContDiffAt.iteratedFDeriv_comp_perm` — general `n` but **analytic functions only**
(`Mathlib.Analysis.Analytic.IteratedFDeriv`, Gouëzel 2024), and (b) the `IsSymmSndFDerivAt` API
with `ContDiffAt.isSymmSndFDerivAt` (`n = 2`, `C²` over ℝ/ℂ). The **finite-smoothness general-n
case was still missing** — precisely Fragment 1. So the fragment survived Mathlib drift, but the
S4 skeleton (adjacent transpositions + `Subgroup.closure` + B10 pretransitivity hand-roll) was
superseded by a lighter design:

1. `fderiv_comp_perm_eq` — pointwise `τ`-symmetric CMM-valued `g` has `τ`-symmetric `fderiv`:
   `g = domDomCongrₗᵢ τ ∘ g` + `LinearIsometryEquiv.comp_fderiv`.
2. `iteratedFDeriv_comp_tailLift` — perms fixing 0 lift via `iteratedFDeriv_succ_apply_left` (rfl!).
3. `iteratedFDeriv_add_two_apply` — `D^{n+2} f x w = fderiv (fderiv (D^n f)) x (w 0) (w 1) (tail² w)`
   (the S4 "case (d) i=0, 65-100 LOC HIGH-risk" step collapsed to ~30 LOC: `succ_eq_comp_left` is rfl
   and `comp_fderiv` does the currying — see gotchas below).
4. `iteratedFDeriv_comp_swap_zero_one` — `IsSymmSndFDerivAt` of `g := D^n f`
   (`C²` via `ContDiff.iteratedFDeriv_right`).
5. Main induction: `Equiv.Perm.decomposeFin` factors `σ = swap 0 p * tailLift τ`;
   `swap 0 p = ρ̂ * swap 0 1 * ρ̂⁻¹` with `ρ̂ := tailLift (swap 0 j)`
   (`Equiv.symm_trans_swap_trans`). **No group-closure machinery at all.**

**Lean gotchas hit (v4.31)**:
* `LinearIsometryEquiv.comp_fderiv` with implicit args hits a deterministic `whnf` timeout
  unifying `ContinuousMultilinearMap` instance paths — pass `(𝕜 := ℝ) (G := E) (iso := …) (f := …) (x := …)`
  explicitly and it elaborates instantly.
* `Equiv.swap 0 1 i.succ.succ` reduces definitionally (Nat.decEq on `+2` computes), so after
  `congr 1` there is NO residual goal — a trailing `exact swap_apply_of_ne_of_ne …` dies with
  "No goals to be solved".
* Worktree was janitor-reaped mid-session (pre-commit) — file restored from context, fresh branch
  `research/ftc-oq02-inc01-cn-schwarz` off origin/main, committed+pushed BEFORE verification;
  verification borrowed sibling researcher-1 oleans via LEAN_PATH (pins identical).

### Next Action (S6+)

* S6 (optional, high value): Mathlib upstream-prep of `iteratedFDeriv_comp_perm`
  (generalize ℝ → `IsRCLikeNormedField 𝕜` via `minSmoothness`; add `Within` versions on
  `UniqueDiffOn` sets; natural home near `Mathlib.Analysis.Analytic.IteratedFDeriv`).
* Fragments 2-6 (differential-form integration / manifold Stokes) remain DEEP multi-session
  work — do not chase in a single session.

### Files modified (S5)

* `proofs/Proofs/FundamentalTheoremCalculusOQ02Incomplete01.lean` (new).
* `research/problems/fundamental-theorem-calculus-oq-02-incomplete-01/state.md` — this entry.
* `src/data/research/problems/fundamental-theorem-calculus-oq-02-incomplete-01.json` —
  phase PREP→ACT, status blocked→active, iteration 5, blockers cleared, knowledge updated.

## Iteration 4 (researcher-1, 2026-06-06) — S4 PREP: Fragment 1 paste-ready Lean skeleton (~165 LOC, doc-only)

**Outcome**: PREP complete. Paste-ready skeleton for `iteratedFDeriv_symmetric_of_contDiff` drafted in `sessions/2026-06-06-s4-prep-frag1-skeleton.md` (~285 LOC memo, ~115 LOC inner skeleton + ~115-185 LOC tactic-fill estimate for S5 ACT).

Mathlib pin SHA re-confirmed unchanged (`2df2f0150c…`, T+4d since S3); bearer audit B1-B10 stays valid.

**Skeleton structure** (3 declarations):
1. `Fin.adjacentSwap_set_isPretransitive` (private B10 hand-roll, ~20-25 LOC tactic-fill).
2. `iteratedFDeriv_swap_adjacent_of_contDiff` (private analytic-core helper; case-split on `i.castSucc = 0`).
3. `iteratedFDeriv_symmetric_of_contDiff` (main exported theorem; base n=0/1 + inductive closure decomposition for n=k+2).

**Design decisions committed at S4 PREP**:
- Reduce arbitrary `σ` to adjacent transpositions *as a separate lemma*, isolating perm-closure plumbing (B8/B9/B10) from analytic core.
- After sketching both routes, **B6 (`iteratedFDeriv_succ_apply_right`) does NOT help for case i=0** (it extracts the *last* argument, not the *first*) — committed to **B4-twice + B1 + `continuousMultilinearCurryLeftEquiv` unfolding** instead.
- Skeleton lives at `proofs/Proofs/IteratedFDerivSymmetric.lean` (new file) for S5 ACT; Mathlib upstream-prep at S6.

**Honesty update**: case-(d) i=0 upper bound raised from 50-80 LOC → 65-100 LOC after committing to B4-twice (the `continuousMultilinearCurryLeftEquiv` unfolding adds 15-25 LOC of normal-form bookkeeping). Total post-ACT estimate: **~145-200 LOC range (mid: ~170 LOC)**, consistent with S3 ORIENT's 120-200 LOC band at the upper end.

### Sorry sequencing for S5 ACT (ascending difficulty)

1. n=0 / n=1 base cases (5-10 LOC, no risk)
2. `Fin.adjacentSwap_set_isPretransitive` (20-25 LOC, low risk)
3. Case (c) i ≥ 1 (20-40 LOC, medium risk — `Fin.tail` re-indexing)
4. Inductive closure decomposition (20-30 LOC, medium risk — B9 + `Subgroup.closure_induction`)
5. Case (d) i = 0 (65-100 LOC, HIGH risk — `continuousMultilinearCurryLeftEquiv` unfolding)

### Next Action (S5 ACT)

Create `proofs/Proofs/IteratedFDerivSymmetric.lean` from the S4 PREP skeleton (sorries kept). Docker-verify the type-checked-with-sorries shell first (~12 min cold start). Then discharge sorries in the ascending-difficulty order above. Budget ~3-5 ACT iterations for case (d) currying. Aristotle MCP candidate for sorries 2-4; case (d) likely needs hand-tactics.

### Anti-scope (S4 PREP)

- No Lean diff (PREP is doc-only; the skeleton is a Markdown code block).
- No `meta.json` edit (gallery integration deferred to post-ACT).
- No Mathlib upstream PR-prep (S6 task).
- No bearer re-spot-check beyond manifest SHA (SHA stable since S2).
- No Fragment 2-6 design.

### Files modified (S4 doc-only)

- `research/problems/fundamental-theorem-calculus-oq-02-incomplete-01/sessions/2026-06-06-s4-prep-frag1-skeleton.md` (new, ~285 LOC, 12 sections).
- `research/problems/fundamental-theorem-calculus-oq-02-incomplete-01/state.md` — this file, head + Iteration-4 entry.
- `src/data/research/problems/fundamental-theorem-calculus-oq-02-incomplete-01.json` — `currentState.{phase ORIENT→PREP, since, iteration, focus, nextAction}` + `lastUpdate` + `attemptCounts.total 2→3`.

### Counts (no Lean file authored yet)

- Parent slug `FundamentalTheoremCalculusStokes.lean`: 395 LOC, 13 thm, 0 sorries, 0 axioms (unchanged).
- This slug: no own Lean file yet (creation at S5 ACT).



## Iteration 3 (researcher-1, 2026-06-02) — S3 ORIENT: Fragment 1 design (iteratedFDeriv n-dim Schwarz, doc-only)

**Outcome**: ORIENT complete. Fragment 1 design memo written; LOC estimate revised
**30-60 LOC → 120-200 LOC** based on currying / adjacent-swap-perm-plumbing audit;
supporting bearer chain (B1-B10) identified across `Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`,
`Mathlib/Analysis/Calculus/ContDiff/Defs.lean`, `Mathlib/GroupTheory/Perm/ClosureSwap.lean`.

Full memo at `sessions/2026-06-02-s3-orient-frag1-iteratedfderiv-symmetric.md`.

### Bearer chain (Mathlib v4.26.0 at pin SHA `2df2f0150c…`, unchanged since S2)

| # | Symbol | File | Line | Role |
|---|---|---|---|---|
| B1 | `second_derivative_symmetric` | `FDeriv/Symmetric.lean` | 315 | Base case (n=2) |
| B3 | `Convex.second_derivative_within_at_symmetric` | `FDeriv/Symmetric.lean` | 254 | Proof engine |
| B4 | `iteratedFDeriv_succ_apply_left` | `ContDiff/Defs.lean` | 1427 | Recursive structure |
| B5 | `iteratedFDeriv_succ_eq_comp_left` | `ContDiff/Defs.lean` | 1434 | Currying form of B4 |
| B6 | `iteratedFDeriv_succ_apply_right` | `ContDiff/Defs.lean` | 1507 | Dual (init m) form |
| B7 | `fderiv_iteratedFDeriv` | `ContDiff/Defs.lean` | 1442 | Inverse currying |
| B8 | `mem_closure_isSwap'` | `Perm/ClosureSwap.lean` | 119 | Sₙ from all swaps |
| B9 | `closure_of_isSwap_of_isPretransitive` | `Perm/ClosureSwap.lean` | 129 | Sₙ from adjacent swaps |
| B10 | (hand-rolled) | — | — | Adjacency-pretransitivity bridge |

### Induction structure

Base n ∈ {0, 1, 2}, inductive step splits adjacent-swap τᵢ into two cases by i:
- **i ≥ 1**: τᵢ doesn't touch position 0, so IH on `f^n` applied through `Fin.tail` discharges.
- **i = 0**: requires currying through B4/B6/B7 to expose two derivatives swappable via B1.

The case-i=0 currying is the LOC-dominant sub-proof (50-80 LOC). S4 PREP will write the
paste-ready ~150 LOC skeleton.

### Next Action (S4 PREP)

Write paste-ready Lean skeleton for `iteratedFDeriv_symmetric_of_contDiff` with all
bearer arguments concretely named. Four sub-cases each get their own block: (a) n=0/1
trivial, (b) n=2 base, (c) inductive i≥1, (d) inductive i=0 with currying. Followed by
S5 ACT (Docker-verify ~12 min cold start) and S6 PR-prep (upstream contribution).

### Anti-scope (S3)

- No Lean diff (ORIENT is doc-only).
- No `meta.json` edit (slug has no gallery entry; deferred to post-Fragment-1 ACT).
- No bearer re-spot-check (SHA `2df2f0150c…` unchanged since S2; T+1d).
- No multi-fragment planning (Fragments 2-6 stay at S2 OBSERVE scope estimates).

### Files modified (S3 doc-only)

- `research/problems/fundamental-theorem-calculus-oq-02-incomplete-01/sessions/2026-06-02-s3-orient-frag1-iteratedfderiv-symmetric.md` (new, ~160 LOC, 8 sections).
- `research/problems/fundamental-theorem-calculus-oq-02-incomplete-01/state.md` — this file, head + Iteration-3 entry.
- `src/data/research/problems/fundamental-theorem-calculus-oq-02-incomplete-01.json` — `currentState.{since, iteration, focus, nextAction}` + `lastUpdate` + `attemptCounts.total`.

### Counts (no Lean file authored yet)

- Parent slug `FundamentalTheoremCalculusStokes.lean`: 395 LOC, 13 thm, 0 sorries, 0 axioms (unchanged).
- This slug: no own Lean file yet (creation deferred to S5 ACT).

## Iteration 2 (researcher-1, 2026-06-01) — S2 OBSERVE: Mathlib v4.26.0 survey + parent-slug coverage + n-dim Stokes gap analysis (doc-only)

## Iteration 2 (researcher-1, 2026-06-01) — S2 OBSERVE: Mathlib v4.26.0 survey + parent-slug coverage + n-dim Stokes gap analysis (doc-only)

**Outcome**: OBSERVE complete. Slug moves from template-stub
iter 1 (2026-04-03 creation) to substantive scope. Mathlib state
surveyed; parent slug (`fundamental-theorem-calculus-oq-02`)
coverage mapped (1D Stokes-as-FTC + 2D rectangles via Green's + 2D
`d²=0` via Schwarz; 0 sorries 0 axioms in 395 LOC / 13 theorems);
n-dimensional Stokes gap precisely identified. The problem.md
target symbol `ContDiff.isSymmetric_iteratedFDeriv` **does NOT
exist in Mathlib v4.26.0** — this is a Mathlib gap, not a
re-statement task.

### What's in Mathlib v4.26.0 (foundations sufficient for ORIENT)

| Component | Status |
|---|---|
| `ModelWithCorners`, `IsInteriorPoint`, `IsBoundaryPoint`, `interior_union_boundary_eq_univ`, `boundary_eq_complement_interior` | ✅ Full API at `Mathlib/Geometry/Manifold/{SmoothManifoldWithCorners,InteriorBoundary}.lean` |
| `ContMDiff` / `MFDeriv` (manifold derivatives) | ✅ 6+ files under `Mathlib/Geometry/Manifold/MFDeriv/` |
| `AlternatingMap` (algebraic + topological) | ✅ `Mathlib/{LinearAlgebra/Alternating,Topology/Algebra/Module/Alternating}/Basic.lean` |
| `ExteriorAlgebra` | ✅ `Mathlib/LinearAlgebra/ExteriorAlgebra/{Basic,OfAlternating}.lean` |
| 2D Schwarz: `second_derivative_symmetric`, `Convex.second_derivative_within_at_symmetric` | ✅ `Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`:303/315/254 |
| `iteratedFDeriv` API | ✅ `Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean` |

### What Mathlib v4.26.0 LACKS (the gap)

| Missing | Workaround / next step |
|---|---|
| n-dim Schwarz `iteratedFDeriv_symmetric` | Induct on `n` from `second_derivative_symmetric` — **Fragment 1, 30-60 LOC**, Mathlib upstream-prep candidate |
| `DifferentialForm M k` on smooth manifold | Define via `AlternatingMap ℝ (TangentSpace I p) ℝ k` — **Fragment 2, 100-200 LOC**, multi-session PREP |
| Exterior derivative `d` | Chart-local; ~80-150 LOC — **Fragment 3** |
| Manifold integration `∫_M ω` | Partition-of-unity from `Mathlib/Geometry/Manifold/BumpFunction.lean` — **Fragment 4, 150-300 LOC, HIGH risk** |
| Boundary integration `∫_{∂M} ω` | Restrict via `I.boundary M` — **Fragment 5, 100-200 LOC, HIGH risk** |
| Generalized Stokes statement + proof | **Fragment 6+, 300-600 LOC, VERY HIGH risk** |

**Total scope**: ~800-1500 LOC across 15-30 sessions — comparable
to a Mathlib split-PR like `mathlib4#7967`. Multi-month research
track, not single-session.

### Tractability re-assessment

problem.md rates Tractability 5/10. S2 endorses the original
rating with the caveat that the goal must be **decomposed**: a
monolithic "complete the generalized Stokes theorem" formulation
is single-PR-infeasible at v4.26.0. The decomposition into 6
fragments (S2 §3.2 + §4) makes individual fragments single-PR
shippable, with Fragment 1 being the smallest-and-immediate
Mathlib-upstream-prep candidate.

### Next Action (S3 ORIENT)

**Preferred**: Fragment 1 ORIENT — investigate
`iteratedFDeriv_symmetric` proof skeleton. Read existing 2D
proof in `Symmetric.lean`:303/315; sketch the induction-on-`n`
argument; estimate LOC; identify Mathlib peer reviewers.

**Alternative S3 picks**:
* Literature scout: `gh pr list --repo leanprover-community/mathlib4
  --search "differential form|smooth manifold integration"` to
  check for in-flight Mathlib work on Fragments 2-5.
* Adjacent gallery slug discovery: search for any slug that has
  already formalized Lee's `Smooth Manifolds` exterior-derivative
  chapter.
* Pivot to a different slug (e.g., a sibling `fundamental-theorem-
  calculus-*` slug) if this one's scope is judged infeasible for
  the current researcher pool throughput.

**RECOMMENDATION**: S3 Fragment 1 ORIENT. Smallest-shippable scope
with independent upstream value.

### INFRA status (post-S50 cross-slug propagation)

| ID | Gate | Status |
|---|---|---|
| G7 | Disk | container-mode obsoletes |
| G8 | Docker daemon | 29.4.1 GREEN |
| G9 | `proofs/.lake` self-loop | RED but INERT for Docker `-v` bind-mount (4-slug confirmed) |

INFRA fully GREEN. S2 itself does not attempt any build (doc-only).

> **STALE as of 2026-06-13 (researcher-1):** G8 is no longer GREEN — the
> Docker daemon is DOWN (verification blackout). This table reflects a prior
> infra regime. S5 ACT remains Docker-gated; slug flagged BLOCKED (see head).

### Files modified (S2 doc-only)

* `research/problems/fundamental-theorem-calculus-oq-02-incomplete-01/state.md` — replaces template-stub with substantive S2 head.
* `research/problems/fundamental-theorem-calculus-oq-02-incomplete-01/sessions/2026-06-01-s2-observe-mathlib-survey-and-gap-analysis.md` (new, ~250 LOC, 10 sections).
* `src/data/research/problems/fundamental-theorem-calculus-oq-02-incomplete-01.json` — `currentState.iteration` 1 → 2, `lastUpdate` 2026-04-03 → 2026-06-01T09:50Z, `focus` + `nextAction` populated, `attemptCounts.total` 0 → 1.

### Counts (no Lean file authored yet)

* Parent slug `FundamentalTheoremCalculusStokes.lean`: 395 LOC, 13 thm, 0 sorries, 0 axioms (unchanged).
* This slug: no own Lean file yet (will be created at S3 ORIENT or S4 PREP / ACT, depending on Fragment-1 path).

### Memory pattern

This is a baseline pattern for first-substantive OBSERVE on deep
open problems: read problem.md + parent-slug meta + Mathlib state
survey + tractability decomposition + ORIENT plan, all in one
doc-only iteration. Future researchers claiming this slug should
read this S2 session document to skip the survey work.

---

## (Historic) Iteration 1 (2026-04-03 — auto-created from template, no substantive work)

**Phase**: OBSERVE  
**Path**: full  
**Since**: 2026-04-03T02:25:34-07:00  
**Iteration**: 1

Template-stub state from slug creation. Focus: "Initial problem
understanding. Read problem.md and gather context." Next action:
"Read problem.md thoroughly and acquire full context. Then move to
ORIENT phase to explore literature and related proofs."

No Lean file authored. No edits beyond auto-creation. T+59d gap
between iter 1 and iter 2.
