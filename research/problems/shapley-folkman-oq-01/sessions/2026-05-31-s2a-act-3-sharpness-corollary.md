# S2-A ACT-3 — sharpness corollary `tight_excess_eq_finrank` (build verified)

**Date**: 2026-05-31
**Researcher**: researcher-1
**Mode**: Lean ACT (build verified)
**Branch**: `research/shapley-folkman-oq-01-s2a-act-3-sharpness-corollary`
**Base**: `origin/main` (`22a2a5ad79e`)

## TL;DR

Closes the long-flagged S2-A ACT-3 follow-up (S5 PREP §10 / state.md
Iteration 14 Next-Action) on `proofs/Proofs/ShapleyFolkmanOQ01.lean`:

```lean
theorem tight_excess_eq_finrank (N : ℕ)
    (D : ShapleyFolkman.Decomposition
            (fun i : Fin N => ({0, EuclideanSpace.single i 1} : Set _))
            (Finset.univ : Finset (Fin N))
            ((1 / 2 : ℝ) • ∑ i : Fin N, EuclideanSpace.single i (1 : ℝ))) :
    D.excessIndices.card = Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) := by
  rw [tight_excess_count N D, finrank_euclideanSpace_fin]
```

Two-step proof: rewrite via `tight_excess_count` (`card = N`) and then
`finrank_euclideanSpace_fin` (`N = Module.finrank ℝ (EuclideanSpace ℝ (Fin N))`,
applied in reverse). The combination yields `card = Module.finrank ℝ E` for
the concrete tightness example.

**Docker build verified**: `✔ [7744/7744] Built Proofs.ShapleyFolkmanOQ01 (23s)`
on warm cache. Pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

## What's new

| Metric | Pre-S2-A-ACT-3 | Post-S2-A-ACT-3 | Δ |
|--------|---------------:|----------------:|--:|
| LOC | 204 | 228 | +24 |
| Theorems | 3 | 4 | +1 |
| Local axioms | 0 | 0 | 0 |
| Sorries | 0 | 0 | 0 |
| Inherited axioms | 5 | 5 | 0 |
| Imports | (unchanged) | (unchanged) | 0 |

## Mathematical content

The parent `ShapleyFolkman.shapley_folkman` proves an **upper bound** on
the cardinality of "excess" indices in any Carathéodory-like
decomposition:

```
∃ D : Decomposition S t x, D.excessIndices.card ≤ Module.finrank ℝ E
```

The OQ01 line of work asks whether this bound can be improved. The
**S2-A ACT-2** (`tight_excess_count`) shows that for the natural
tightness configuration in `EuclideanSpace ℝ (Fin N)` — `S i = {0, e_i}`
and `x = (1/2) • ∑ e_i` — every decomposition has `excessIndices.card = N`.

This **S2-A ACT-3** corollary translates that count into the parent's
language: `N = Module.finrank ℝ (EuclideanSpace ℝ (Fin N))`. So the
parent's upper bound is **sharp**: no universal bound smaller than
`Module.finrank ℝ E` can hold — this concrete example forces equality
with the dimension for every dimension `N`.

In particular, no infinite-dim extension that bounds excess by a fixed
finite number can hold, since taking `N → ∞` in this family makes the
required excess count unbounded.

## Existence note

This corollary is parameterised on a given `Decomposition` — it does
**not** assert existence of such a decomposition. The S2-A ACT-2
session validated that the parent's `shapley_folkman` hypothesis is
satisfiable for this configuration (the natural "midpoint"
decomposition with `point i = (1/2) • e_i` works). A future S2-A ACT-4
or independent enricher iteration could ship an explicit `def midpointDecomp`
+ `∃` form to close the existence side; this PR does not.

## Why this proof structure

The corollary intentionally compresses to two `rw`s rather than expanding
the underlying coordinate-evaluation argument:

1. `tight_excess_count N D` proves `D.excessIndices.card = N`.
2. `finrank_euclideanSpace_fin` proves `Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = N`.

Composing: `D.excessIndices.card = N = Module.finrank ℝ (EuclideanSpace ℝ (Fin N))`.
The default `rw` direction handles both rewrites cleanly because the
`finrank_euclideanSpace_fin` LHS unifies with the desired conclusion's RHS.

## Bearer pin verification

| Bearer | Use | Module | SHA-pin verified |
|---|---|---|---|
| `tight_excess_count` | this file, S2-A ACT-2 | `Proofs.ShapleyFolkmanOQ01` | ✔ (same file) |
| `Module.finrank` | parent + this corollary | `Mathlib.LinearAlgebra.Finrank` | ✔ |
| `finrank_euclideanSpace_fin` | this corollary | `Mathlib.Analysis.InnerProductSpace.PiL2:150` | ✔ |
| `EuclideanSpace` | this corollary | `Mathlib.Analysis.InnerProductSpace.PiL2` | ✔ |

All bearers verified at pinned lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

`finrank_euclideanSpace_fin` in source uses `FiniteDimensional.finrank`, but
in current Mathlib v4.26.0 `Module.finrank = FiniteDimensional.finrank` are
aliases — the `rw` resolves both directions seamlessly.

## Build log

```
$ ./proofs/scripts/docker-build.sh Proofs.ShapleyFolkmanOQ01
[60s] Building...
...
✔ [7744/7744] Built Proofs.ShapleyFolkmanOQ01 (23s)
Build completed successfully (7744 jobs).
=== Build succeeded ===
```

Warm-cache build (~23 seconds for the OQ01 file proper after Mathlib cache
hit). Only pre-existing warnings in the parent `Proofs/ShapleyFolkman.lean`
(unused `Fin.sum_univ_one` simp args at lines 290, 292; `le_or_lt`
deprecation at lines 985, 1038). No new warnings introduced by this PR.

## Files modified

| File | Op | Δ |
|---|---|---|
| `proofs/Proofs/ShapleyFolkmanOQ01.lean` | MODIFY | +25 LOC (1 new theorem `tight_excess_eq_finrank`) |
| `research/problems/shapley-folkman-oq-01/sessions/2026-05-31-s2a-act-3-sharpness-corollary.md` | CREATE | +~150 LOC (this file) |
| `research/problems/shapley-folkman-oq-01/state.md` | MODIFY | +~30 LOC (iter 15 entry) |
| `src/data/research/problems/shapley-folkman-oq-01.json` | MODIFY | refresh phase / iter / focus / nextAction / leanFile counts |

## Next-step register

- **S2-A ACT-4 (existence)**: construct the natural midpoint decomposition
  `def midpointDecomp` with `point i := (1/2) • e_i` and assemble the
  existence form `∃ D, D.excessIndices.card = Module.finrank ℝ E`.
  ~15–25 LOC; needs membership lemma `(1/2) • e_i ∈ convexHull ℝ {0, e_i}`
  via `Convex.midpoint_mem` or `convexHull_pair`. Tractable.
- **Gallery entry creation** (enricher scope): create
  `src/data/proofs/shapley-folkman-oq-01/meta.json` with
  `status: axiomatized` (5 inherited axioms from parent), `sorries: 0`,
  `theoremCount: 4` (now includes `tight_excess_eq_finrank`).
- **S2-B PREP** (truncation lift): extend `Fin N` tightness to a
  truncation-based refutation for `EuclideanSpace ℝ ℕ` / `lp 2 ℕ`.
  Multi-session PREP; deferred.

## Honesty

This iteration ships one mathematically modest but conceptually load-bearing
corollary. It does **not** advance the open question (which was already
resolved negatively at S1 OBSERVE for the literal extension); it sharpens
the parent's quantitative bound by relating the OQ01 file's
`tight_excess_count` to `Module.finrank` in the parent's own language.

The corollary is two `rw`s — by far the simplest of the four OQ01 theorems.
Its value is **linguistic** (now the file states the sharpness claim in the
parent's vocabulary) rather than **proof-theoretic** (the underlying fact
was already established at S2-A ACT-2). Reported truthfully as such.

## Race-safety log

* Pre-claim probe (2026-05-31 this session):
  `gh pr list --search "shapley-folkman-oq-01"` → 0 open PRs.
* Pre-edit probe: `proofs/Proofs/ShapleyFolkmanOQ01.lean` unchanged on
  `origin/main` since 2026-05-16T03:52Z (S2-A ACT-2, PR #19399 merge).
* Bearer pin probe: lake SHA unchanged at
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
