# Session — S2-B₁ ACT: `no_universal_shapley_folkman_bound`

**Slug.** `shapley-folkman-oq-01`
**Researcher.** researcher-10
**Date.** 2026-06-10
**Mode.** ACT (`.lean` + JSON edits).
**Iteration.** 19 (after S2-B PREP, Session 18).

## 1. Summary

Executed Session 18 §3.1 paste-ready recipe verbatim. Landed
`no_universal_shapley_folkman_bound` in
`proofs/Proofs/ShapleyFolkmanOQ01.lean`, a direct corollary of the existing
S2-A facts (`midpointDecomp` + `tight_excess_count`).

- File delta: 306 → 339 LOC (+33).
- Theorem count: 6 → 7 (added `no_universal_shapley_folkman_bound`).
- 0 new sorries, 0 new axioms.
- Docker build clean (`./proofs/scripts/docker-build.sh
  Proofs.ShapleyFolkmanOQ01`): `✔ [7744/7744] Built
  Proofs.ShapleyFolkmanOQ01 (231s)`.
- No fallbacks from Session 18 §3.4 fired.

## 2. Mathematical content

For every `K : ℕ`, exhibit `E = EuclideanSpace ℝ (Fin (K+1))`, the
midpoint family `S i = {0, e_i}` and target `x = (1/2) • ∑ e_i`, and
return `midpointDecomp (K+1)` whose `excessIndices.card` equals `K+1`
by `tight_excess_count` and so strictly exceeds `K`.

Combined with the parent `shapley_folkman` (whose bound is
`Module.finrank ℝ E`), this rules out any universal `Nat`-valued bound
that ignores ambient dimension — even within finite-dim ambients of
growing dimension. The dimension dependence in the parent bound is
unavoidable.

S2-A line (sharpness corollary): `tight_excess_eq_finrank`,
`exists_tight_decomposition`. S2-B₁ line (this session): no universal
ambient-free bound.

## 3. The shipped proof body

```lean
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

The three-step body unifies cleanly without rewrite or elaboration
hints; the `Nat.lt_succ_self K` discharge takes the goal
`K + 1 > K` directly.

## 4. Race-safety log

- **Pre-claim probe**: `gh pr list --search "shapley-folkman in:title"
  --state open` → 0 open PRs at claim (2026-06-10 ~09:00Z).
- **Pre-edit probe**: `proofs/Proofs/ShapleyFolkmanOQ01.lean` unchanged
  on `origin/main` since `f586eeaf627` (PR #22322, 2026-06-05T01:45Z).
- **Branch rebase**: claimed branch `feature/researcher-10` was at
  `ee18b40b57d3`; reset to `origin/main` (`98d1689ec26c`) and branched
  to `research/shapley-folkman-oq-01-s2b1-act` for the work.

## 5. Files modified this session

- `proofs/Proofs/ShapleyFolkmanOQ01.lean` — APPEND the `no_universal_
  shapley_folkman_bound` theorem (+33 LOC) immediately before
  `end ShapleyFolkmanOQ01`.
- `src/data/research/problems/shapley-folkman-oq-01.json`:
  - `currentState.phase` PREP → ACT; `since` to this session start;
    `iteration` 18 → 19; refreshed `focus` + `nextAction`.
  - `leanFiles[0]`: `lineCount` 306 → 339; `theoremCount` 6 → 7.
  - `knowledge.progressSummary` extended with Session 19 entry.
  - `knowledge.nextSteps` pruned of the now-shipped S2-B₁ ACT step;
    elevated gallery-entry creation to "immediate" enricher scope.
  - `updatedAt` → 2026-06-10T09:00:00Z.
- `research/problems/shapley-folkman-oq-01/sessions/2026-06-10-s2b1-act-no-universal-bound.md`
  (this file) — CREATE.

No `meta.json` / gallery-data edits this session; gallery-entry
creation is enricher scope.

## 6. Next action register

- **Multi-session (deferred)**: S2-B₂ ACT — embedding-transport for
  `lp (fun _ : ℕ => ℝ) 2` lift. Needs Session 18 §4.2 machinery
  (~150-250 LOC, 3-5 sessions). New S2-C PREP should pin
  `AffineMap.image_convexHull` + `Decomposition.map` recipe before
  paste-ready ACT.
- **Enricher scope (immediate)**: gallery entry
  `src/data/proofs/shapley-folkman-oq-01/` with `status:
  axiomatized`, `badge: axiom`, `theoremCount: 7`, `defCount: 1`,
  `sorryCount: 0`, 5 inherited axioms.
- **Multi-session prerequisite (deferred indefinitely)**: Lyapunov's
  convexity theorem upstream into Mathlib (200-300 LOC, blocks
  Approach A / Aumann path entirely).

## 7. Iteration history extension

| Iter | Phase | Mode | PR | Description |
|------|-------|------|----|----|
| 17   | ACT   | `.lean` | #22322 | S2-A ACT-4 ACT: `exists_tight_decomposition` (recipe executed). |
| 18   | PREP  | doc  | #22542 | S2-B PREP: truncation-lift design — S2-B₁ paste-ready recipe. |
| **19** | **ACT** | **`.lean`** | **(this PR)** | **S2-B₁ ACT: `no_universal_shapley_folkman_bound` (recipe executed). +33 LOC, 0 sorries, 0 axioms; Docker build clean (231s, 7744/7744).** |
