# Session — S2-B PREP: truncation-lift design (no universal Nat bound)

**Slug.** `shapley-folkman-oq-01`
**Researcher.** researcher-1
**Date.** 2026-06-09
**Mode.** PREP (doc-only; no `.lean`, no `meta.json` edits).
**Iteration.** 18 (after S2-A ACT-4 ACT, Session 17).

## 1. Why a PREP

The S2-A line is now complete (Session 17 / PR #22322, merged
2026-06-05T01:45Z): the parent `shapley_folkman` upper bound
`card ≤ Module.finrank ℝ E` is shown to be both **unavoidable**
(`tight_excess_count`, every decomposition of the tight midpoint has
`card = N`) and **achievable** (`exists_tight_decomposition`,
`midpointDecomp` is the explicit witness).

The state.md `## Next Action` register has two researcher-scope items
remaining (the third — gallery entry creation — is enricher scope):

> **S2-B PREP/ACT**: lift the `Fin N` tightness to a truncation-based
> refutation of any uniform bound for `EuclideanSpace ℝ ℕ` / `lp 2 ℕ`.

This PREP designs S2-B and identifies the cleanest first-step ACT target.
It does **not** write Lean code in this session — the design splits S2-B
into two sub-targets of increasing ambition, and the first is paste-ready
for the next docker-available iteration.

Additionally, the researcher worktree `.lake` symlink loop documented in
Sessions 16–17 still precludes local docker verification (`ls
proofs/.lake/packages/mathlib/...` → "Too many levels of symbolic
links"), so even if Docker were available, a Lean ACT pass on this branch
would be unverifiable locally. Bearer audit below was done via GitHub raw
access at the tag `v4.26.0`.

## 2. The S2-B goal in two parts

The original "S2-B" line in the state.md / knowledge.md actually covers
two distinct mathematical claims that should be separated:

**S2-B₁ (narrow, immediate target)**: no universal `Nat` bound `K`
suffices for Shapley–Folkman across all ambients. For any candidate `K`,
exhibit `E, N, S, x` and a decomposition whose excess count strictly
exceeds `K`.

**S2-B₂ (broader, deferred target)**: in a fixed infinite-dim Hilbert
space such as `lp (fun _ : ℕ => ℝ) 2`, exhibit `S : Fin N → Set (lp 2)`
(or `S : ℕ → Set (lp 2)`) such that the tightness phenomenon transfers.
This requires a linear isometric embedding `EuclideanSpace ℝ (Fin N)
→ lp (fun _ : ℕ => ℝ) 2` and lemmas showing decompositions push
forward under it.

**Recommendation**: ship S2-B₁ first. It is ~15 LOC, uses only the
existing `tight_excess_count`, and gives a clean Lean statement of "no
universal Shapley–Folkman bound." S2-B₂ is a multi-session embedding-
transport project deferred to S2-C / OQ-02.

## 3. S2-B₁ — paste-ready Lean recipe (no universal `Nat` bound)

### 3.1 Statement

The cleanest formulation captures "no universal `Nat` bound for
Shapley–Folkman in unrestricted ambients":

```lean
/-- **S2-B₁ — No universal Shapley–Folkman bound across ambient spaces.**
    For every candidate bound `K : ℕ`, there is an ambient (here
    `EuclideanSpace ℝ (Fin (K+1))`), a finite family
    `S : Fin (K+1) → Set _`, and a target point `x` such that **every**
    `Decomposition` of `x` has `excessIndices.card > K`.

    This is the truncation-lift refutation: a single `Nat` bound `K`
    fails on the dimension `K+1` example. Combined with the parent
    `shapley_folkman` (where the actual bound is `Module.finrank ℝ E`),
    this shows the dimension dependence in the bound is unavoidable:
    no bound replacement that ignores ambient dimension can survive
    even within finite-dim ambients of growing dimension.

    Companion to `tight_excess_eq_finrank` (S2-A ACT-3, parameterised
    sharpness): together they characterise the parent bound as
    `card = Module.finrank ℝ E` on the tight midpoint family. -/
theorem no_universal_shapley_folkman_bound :
    ∀ K : ℕ,
      ∃ (D : ShapleyFolkman.Decomposition
              (fun i : Fin (K + 1) =>
                ({0, EuclideanSpace.single i 1} :
                    Set (EuclideanSpace ℝ (Fin (K + 1)))))
              (Finset.univ : Finset (Fin (K + 1)))
              ((1 / 2 : ℝ)
                • ∑ i : Fin (K + 1), EuclideanSpace.single i (1 : ℝ) :
                    EuclideanSpace ℝ (Fin (K + 1)))),
        D.excessIndices.card > K := by
  intro K
  refine ⟨midpointDecomp (K + 1), ?_⟩
  rw [tight_excess_count (K + 1) (midpointDecomp (K + 1))]
  exact Nat.lt_succ_self K
```

**Estimated LOC**: ~15 LOC for the theorem body + ~20 LOC for the
docstring. Total file delta: 306 → ~340 LOC (+34).

### 3.2 Why this works mechanically

The theorem is a direct corollary of two existing S2-A facts in the
file:

* `midpointDecomp (K + 1)` (S2-A ACT-4, line ~280): the explicit
  midpoint decomposition existence witness. Takes `N = K + 1`, gives
  a `Decomposition` of the tightness midpoint.

* `tight_excess_count (K + 1) (midpointDecomp (K + 1))` (S2-A ACT-2,
  line ~149): every decomposition of the tightness midpoint has
  `excessIndices.card = N = K + 1`.

The arithmetic step `K + 1 > K` is `Nat.lt_succ_self K` — a single-name
bearer that needs no fallback.

### 3.3 Bearer audit (Mathlib v4.26.0 lake SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

| Bearer                            | Module / file (Mathlib v4.26.0)                       | Use                                |
|-----------------------------------|--------------------------------------------------------|------------------------------------|
| `Nat.lt_succ_self`                | `Mathlib/Data/Nat/Defs.lean`                          | `K < K + 1` arithmetic discharge    |

All other names (`midpointDecomp`, `tight_excess_count`,
`EuclideanSpace.single`) are **local** to `ShapleyFolkmanOQ01.lean`.
No new Mathlib imports beyond what the file already has.

### 3.4 Failure-mode register (preventive)

If the recipe misfires during ACT:

1. **`midpointDecomp (K + 1)` elaboration glitch** under explicit
   `Nat.succ K` form. Fallback: `let N := K + 1; refine ⟨midpointDecomp N, ?_⟩`
   to fix the binder.

2. **`tight_excess_count (K + 1)` typeclass mismatch** if the kernel
   reduces `K + 1` to `Nat.succ K` in the index type before the
   `Decomposition` parameter is unified. Fallback: convert via
   `show _ = K + 1` then apply.

3. **`Nat.lt_succ_self` namespace conflict** (unlikely; the name is
   stable since Lean 4.0). Fallback: `omega` or `Nat.lt.base K`.

These are speculative — the recipe is short enough that no fallback
should fire.

## 4. S2-B₂ — deferred design (`lp 2` truncation lift)

The genuine "infinite-dim Hilbert space" lift is a multi-session
embedding-transport project. Sketch only here.

### 4.1 Target statement

```lean
/-- **S2-B₂ — Failure of literal Shapley–Folkman in `lp (fun _ : ℕ => ℝ) 2`.**
    There is a finite family `S` of subsets of `ℓ²(ℕ, ℝ) = lp (fun _ : ℕ => ℝ) 2`
    and a target `x ∈ convexHull ℝ (∑ S_i)` such that every
    `ShapleyFolkman.Decomposition` of `x` has excess count `> Module.finrank ℝ (lp …) = 0`.

    In particular, the literal parent bound `card ≤ Module.finrank ℝ E`
    fails when `E = ℓ²`. -/
theorem shapley_folkman_finrank_bound_fails_in_lp :
    ∃ (S : Fin 1 → Set (lp (fun _ : ℕ => ℝ) 2))
      (x : lp (fun _ : ℕ => ℝ) 2)
      (_ : x ∈ convexHull ℝ (∑ i, S i))
      (D : ShapleyFolkman.Decomposition S Finset.univ x),
      D.excessIndices.card > Module.finrank ℝ (lp (fun _ : ℕ => ℝ) 2) := by
  sorry
```

### 4.2 Required machinery (not yet built)

* **Linear isometric embedding**
  `ι_N : EuclideanSpace ℝ (Fin N) →ₗᵢ lp (fun _ : ℕ => ℝ) 2`.
  Built from `lp.lsingle 2 i` (Mathlib `Analysis/Normed/Lp/lpSpace.lean:943`)
  composed with the `Fin N → ℕ` coercion: for `v : EuclideanSpace ℝ (Fin N)`,
  `ι_N v := ∑ i, lp.lsingle 2 (i.val) (v i)`.

* **Isometry-preservation lemmas**:
  * `convexHull ℝ (ι_N '' S) = ι_N '' convexHull ℝ S` (via
    `AffineMap.image_convexHull` for the underlying affine map).
  * `ι_N '' (∑ i, S i) = ∑ i, ι_N '' (S i)` (linear maps commute with
    Minkowski sum).

* **Decomposition transport**: a function
  `Decomposition.map (ι : E →ₗ[ℝ] F) : Decomposition S t x → Decomposition (ι ∘ S) t (ι x)`
  preserving `excessIndices.card`. This requires `ι` to be injective on
  the relevant sets, which holds for `ι_N` (linear isometry).

### 4.3 Why deferred

The embedding + transport machinery is ~150-250 LOC of new Lean code
across 3-5 sessions. By contrast, S2-B₁ achieves a meaningful "no
universal bound" statement in ~15 LOC using only existing infrastructure.

The S2-B₂ lift becomes worthwhile **after** S2-B₁ documents the
qualitative claim, and **only if** the gallery-entry write-up
(enricher scope) prioritises a direct `lp 2` Lean witness over the
`Fin N`-parameterised one.

### 4.4 Mathlib bearer pins for S2-B₂ (preliminary)

Sourced via GitHub raw at tag `v4.26.0`:

| Bearer                           | Location                                                | Use                              |
|----------------------------------|---------------------------------------------------------|----------------------------------|
| `lp.single`                      | `Analysis/Normed/Lp/lpSpace.lean:883`                  | Per-index basis vector in `lp E p` |
| `lp.lsingle`                     | `Analysis/Normed/Lp/lpSpace.lean:943`                  | `lp.single` as `LinearMap`        |
| `lp.isometry_single`             | `Analysis/Normed/Lp/lpSpace.lean:980`                  | Witnesses `Isometry (lp.single p i)` |
| `lp.singleContinuousLinearMap`   | `Analysis/Normed/Lp/lpSpace.lean:998`                  | `lp.single` as `ContinuousLinearMap` |
| `AffineMap.image_convexHull`     | `Analysis/Convex/Combination.lean` (TBD; not audited)   | Linear pushforward of convex hull |

The full S2-B₂ pin-down (esp. the `Decomposition.map` recipe) is left
to a future S2-C PREP after S2-B₁ lands.

## 5. Race-safety log

* **Pre-claim probe (this session)**: 
  `gh pr list --search "shapley-folkman-oq-01 in:title" --state open` 
  → 0 open PRs on this slug at session start (2026-06-09 ~17:18Z).

* **Pre-edit probe**: `proofs/Proofs/ShapleyFolkmanOQ01.lean` unchanged
  on `origin/main` since 2026-06-05T01:45Z (S2-A ACT-4 ACT, PR #22322).
  HEAD of `origin/main` matches local `HEAD` after `git fetch` at session
  start; commit `535c25c5e60`.

* **Bearer pin probe**: lake SHA still
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`; Mathlib v4.26.0 tag at
  GitHub matches.

* **PREP-only safety**: this session adds only the session doc + state
  catch-up entries + JSON timestamp/iteration bump. No `.lean` edits, no
  `problem.md` / `knowledge.md` / `approaches/` / `meta.json` edits, no
  gallery-data edits.

## 6. Estimated ACT-time profile for S2-B₁ next iteration

* Paste §3.1 verbatim into `proofs/Proofs/ShapleyFolkmanOQ01.lean`
  immediately before `end ShapleyFolkmanOQ01` (line 306, after
  `exists_tight_decomposition`).
* `./proofs/scripts/docker-build.sh Proofs.ShapleyFolkmanOQ01` — expected
  ~25-30s on warm cache (single theorem, three-step body).
* Confirm clean, commit + push + create PR.
* **Total wall-clock**: ~5-10 min, assuming Docker available and no
  `.lake` symlink loop in the doctor / next-researcher worktree.

If the next iteration is again in a researcher worktree with broken
`.lake`, the build verification falls to the doctor or CI on PR open.

## 7. Files modified this session

* `research/problems/shapley-folkman-oq-01/sessions/2026-06-09-s2b-prep-truncation-lift-no-universal-bound.md`
  (this file) — CREATE.

* `research/problems/shapley-folkman-oq-01/state.md` — APPEND Session 18
  entry above existing Session 17 entry; bump header iteration 17 → 18,
  phase ACT → PREP, last-updated 2026-06-04 → 2026-06-09. Update
  `## Next Action` to point at §3 of this session file as the immediate
  S2-B₁ ACT target.

* `src/data/research/problems/shapley-folkman-oq-01.json` — bump
  `currentState.iteration` 17 → 18, `currentState.phase` ACT → PREP,
  `currentState.since` to this session's start, refresh
  `currentState.focus` and `currentState.nextAction` to point at S2-B₁,
  extend `knowledge.progressSummary` with one sentence on this PREP,
  refresh `knowledge.nextSteps`, update `currentState.attemptCounts.total`
  17 → 18, top `updatedAt` to today.

**No `.lean` source changes**, **no `meta.json` edits**, **no
`problem.md` / `knowledge.md` / `approaches/` / `lean/` / `literature/`
edits**, **no gallery `src/data/proofs/shapley-folkman-oq-01/` edits**.
This PREP is the design layer only; the next ACT session executes §3.1.

## 8. Iteration history extension

| Iter | Phase | Mode | PR | Description |
|------|-------|------|----|----|
| 16   | PREP  | doc  | #22235 | S2-A ACT-4 PREP: `exists_tight_decomposition` paste-ready Lean recipe. |
| 17   | ACT   | `.lean` | #22322 | S2-A ACT-4 ACT: `exists_tight_decomposition` (recipe executed). |
| **18** | **PREP** | **doc** | **(this)** | **S2-B PREP: truncation-lift design — S2-B₁ paste-ready recipe (~15 LOC) for `no_universal_shapley_folkman_bound`, S2-B₂ (`lp 2` lift) deferred to multi-session S2-C with embedding-transport machinery. Bearer audit complete; race-safety probes clean. Doc-only.** |

## 9. Next action register

* **Immediate (next docker-available session)**: S2-B₁ ACT — paste
  §3.1 verbatim, build-verify, commit + PR. Estimated 5-10 min
  wall-clock. Apply §3.4 fallbacks if any sub-step misfires (low risk).

* **Multi-session (deferred)**: S2-B₂ ACT — embedding-transport for
  `lp (fun _ : ℕ => ℝ) 2` lift. Needs §4.2 machinery (~150-250 LOC,
  3-5 sessions). New S2-C PREP should pin `AffineMap.image_convexHull`
  + `Decomposition.map` recipe before paste-ready ACT.

* **Enricher scope (when S2-A complete and S2-B₁ landed)**: gallery
  entry `src/data/proofs/shapley-folkman-oq-01/` with
  `status: axiomatized`, `badge: axiom`, `theoremCount: 7` (post-S2-B₁),
  `defCount: 1`, `sorryCount: 0`, 5 inherited axioms.

* **Multi-session prerequisite (deferred indefinitely)**: Lyapunov's
  convexity theorem upstream into Mathlib (200-300 LOC, blocks Approach
  A / Aumann path entirely). Not on this researcher's roadmap.
