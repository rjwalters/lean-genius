# S5 ACT — Sibling-style accessor theorems + no-edge sanity theorems

**Researcher**: researcher-1
**Date**: 2026-06-04
**Phase**: ACT (iteration 5, S4 ACT's "trivial closure lemma" S5 candidate executed)
**PR**: (this PR)

## Summary

Added **7 small theorems** to `proofs/Proofs/KonigsbergOQ03.lean` in two
groups:

1. **Three sibling-parity accessors** (`InfiniteWalk.step_is_adj`,
   `IsEulerWalk.covers`, `IsEulerWalk.injective`) — mirrors the
   `KonigsbergOQ03OQ02.lean` API so callers can use either file
   interchangeably for the one-way infinite case. Pure projections.

2. **Four no-edge sanity theorems** — for an `InfiniteGraph` with no
   adjacencies (`∀ u v, ¬ G.adj u v`):
   * `InfiniteWalk.isEmpty_of_no_edges` — `IsEmpty (InfiniteWalk G)`.
   * `BiInfiniteWalk.isEmpty_of_no_edges` — `IsEmpty (BiInfiniteWalk G)`.
   * `not_hasOneWayEulerPath_of_no_edges` — `¬ HasOneWayEulerPath G`.
   * `not_hasInfiniteEulerPath_of_no_edges` — `¬ HasInfiniteEulerPath G`.

Each no-edge theorem is a 2-line `rintro ⟨w, _⟩; exact h _ _ (w.step_adj 0)`
that uses the `step_adj` field of the walk structure to derive a
contradiction with the no-edge hypothesis.

## Net file deltas

| Metric | Before (S4 ACT, `origin/main`) | After (this S5 ACT) | Δ |
|--------|--------------------------------|---------------------|---|
| LOC | 202 | 256 | +54 |
| theorems | 2 | 9 | +7 |
| defs+structures | 14 | 14 | 0 |
| `:= True` placeholders | 0 | 0 | 0 |
| sorries | 0 | 0 | 0 |
| axioms | 0 | 0 | 0 |

## Why this is the right S5 work

The S4 ACT memo's S5 candidate menu listed five options:

1. **(trivial closure lemma)** — smallest non-trivial Eulerian fact.
2. **(EGW statement)** — state the theorem as `theorem ... := by sorry`.
3. **(sibling DRY refactor — cross-slug)** — separate claim.
4. **(EGW proof — multi-week)** — too large for one session.
5. **(skip)** — move on.

This PR executes option **(1)** with a small addition: the "trivial
closure lemma" is the **no-edge sanity theorems**, which confirm the
S4-discharged predicates `HasOneWayEulerPath` / `HasInfiniteEulerPath`
are non-degenerate — they do not hold for every graph.

I deliberately did **not** go with option (1)'s original suggestion of
*"constant `InfiniteWalk` as a (vacuous) `IsEulerWalk`"* because:

* `InfiniteGraph.loopless` forbids `G.adj v v`, so the constant walk
  `v, v, v, …` violates `step_adj : ∀ n, G.adj (vertex n) (vertex (n+1))`.
* No constant `InfiniteWalk` exists for any graph at all; the suggested
  lemma was simply wrong.

The no-edge variant is the correct dual: it shows that when there are
no edges, *no* `InfiniteWalk` can exist (the type is `IsEmpty`), so the
Eulerian existentials are `False`. This is the smallest concrete claim
that exercises both the walk types and the Eulerian existentials.

The sibling-parity accessors `step_is_adj` / `covers` / `injective` are
pure projections that mirror the sibling file's `Part 4: Basic
Properties` section. They are useful because callers writing
`hEuler.covers u v hadj` reads more naturally than `hEuler.1 u v hadj`,
and matches the API style already established in the gallery.

I considered option (2) (EGW statement as `sorry`-target) but deferred
it because:

* Stating EGW correctly requires a `Connected` predicate on
  `InfiniteGraph`, which we don't have yet — committing to a definition
  is itself a non-trivial design choice (path-connectivity? Closure
  under finite walks?).
* The non-locally-finite regime needs a finite-edge-cut even-cardinality
  condition that requires further infrastructure.
* Premature `sorry`-targets can lock in a bad statement shape.

A dedicated S6 (or later) session can take that on once a `Connected`
def is committed.

## Implementation walkthrough

### Group 1: Sibling-parity accessors

#### `InfiniteWalk.step_is_adj`

Pure restatement of `step_adj` field of the structure, scoped under
`namespace InfiniteWalk`:

```lean
theorem step_is_adj {V : Type*} {G : InfiniteGraph V}
    (w : InfiniteWalk G) (n : ℕ) : G.adj (w.vertex n) (w.vertex (n + 1)) :=
  w.step_adj n
```

Mirrors `KonigsbergOQ03OQ02.InfiniteWalk.step_is_adj` exactly.

#### `IsEulerWalk.covers` and `IsEulerWalk.injective`

These required wrapping the two `theorem`s in a new `namespace IsEulerWalk`
block (the parent file did not previously have one). The accessors are
projections of the `And` in `IsEulerWalk`:

```lean
namespace IsEulerWalk

theorem covers {V : Type*} {G : InfiniteGraph V} {w : InfiniteWalk G}
    (hEuler : IsEulerWalk G w) (u v : V) (hadj : G.adj u v) :
    w.CoversEdge u v :=
  hEuler.1 u v hadj

theorem injective {V : Type*} {G : InfiniteGraph V} {w : InfiniteWalk G}
    (hEuler : IsEulerWalk G w) : w.IsEdgeInjective :=
  hEuler.2

end IsEulerWalk
```

Mirrors the sibling file's lines 134–142 exactly.

### Group 2: No-edge sanity theorems

```lean
theorem InfiniteWalk.isEmpty_of_no_edges {V : Type*} {G : InfiniteGraph V}
    (h : ∀ u v, ¬ G.adj u v) : IsEmpty (InfiniteWalk G) :=
  ⟨fun w => h _ _ (w.step_adj 0)⟩
```

The constructor of `IsEmpty α` takes `α → False`. Given a candidate walk
`w`, its `step_adj 0` field is a proof of `G.adj (w.vertex 0) (w.vertex 1)`,
which directly contradicts `h _ _`. Same shape for `BiInfiniteWalk`.

For the non-existence corollaries:

```lean
theorem not_hasOneWayEulerPath_of_no_edges {V : Type*} {G : InfiniteGraph V}
    (h : ∀ u v, ¬ G.adj u v) : ¬ HasOneWayEulerPath G := by
  rintro ⟨w, _⟩
  exact h _ _ (w.step_adj 0)
```

The `rintro` destructures `HasOneWayEulerPath G = ∃ w : InfiniteWalk G,
IsEulerWalk G w` into `w` (discarding the `IsEulerWalk` proof since the
contradiction comes from the walk type itself). Same shape for
`HasInfiniteEulerPath` (with `BiInfiniteWalk`).

We could have proved these as `IsEmpty.elim` applications of the first
two theorems, but the direct `step_adj 0` proof is 1 line and avoids
introducing an `IsEmpty.false` unfolding.

## Build status — NOT verified locally

Docker daemon on this host is still broken as of 2026-06-04 (same
containerd content-store I/O issue noted in the S4 session memo —
`docker ps` returns "Cannot connect to the Docker daemon"). Build
verification deferred to CI / next-auditor pass. Confidence in the code
grounded in:

* **Pattern equivalence**: `step_is_adj`, `covers`, `injective` are
  line-for-line ports of sibling-file theorems that build cleanly under
  the same `Mathlib v4.26.0` pin.
* **Trivial term proofs**: `step_is_adj` is `w.step_adj n` (structure
  projection); `covers` is `hEuler.1 u v hadj` (And-left + apply);
  `injective` is `hEuler.2` (And-right). No tactic state to go wrong.
* **No-edge proofs**: use only `rintro`, `exact`, and field projections
  — all built-in. The `IsEmpty` constructor takes `α → False` directly;
  the `step_adj 0` field is a proof of `G.adj (w.vertex 0) (w.vertex 1)`
  whose application against the no-edge hypothesis is type-checked
  syntactically.
* **No new imports**: file already has `import Mathlib`; all new
  symbols (`IsEmpty`, `rintro`, structure field projection) are
  Mathlib-resident.

## Meta sync

`src/data/proofs/konigsberg-oq-03/meta.json`:

* `lineCount` 202 → 256.
* `theoremCount` 2 → 9 (both at top-level `leanFile` block and the
  nested `meta` block).

Other meta fields unchanged. `assumptions` text still accurate (the no-edge
theorems are about *what is not Eulerian*, not new placeholders).
`originalContributions` left as is — these are small accessor/sanity
theorems, not new mathematical content worth listing.

## Iteration outcome

Slug remains `placeholder-free` with **9 theorems** about the infinite-walk
infrastructure (up from 2). Two distinct API styles now coexist:
the sibling `KonigsbergOQ03OQ02` and this parent file both expose
`step_is_adj` / `covers` / `injective` on their respective `InfiniteWalk`
/ `IsEulerWalk` types.

The no-edge sanity theorems are the smallest **non-trivial** Eulerian facts
about `InfiniteGraph` — they're not vacuous because they apply to a
non-trivial subclass of graphs (the empty ones), and they confirm the
S4-discharged predicates have non-trivial content.

## Next Action (S6 candidate menu)

* **(EGW statement)** — state EGW as a `theorem ... := by sorry` once a
  `Connected` predicate is committed for `InfiniteGraph`. ~5 LOC + def.
* **(one-edge graph Euler walk)** — for an `InfiniteGraph` with exactly
  one edge `{u, v}`, prove `¬ HasInfiniteEulerPath G` (a single edge
  cannot support a non-repeating bi-infinite walk). Smaller than EGW,
  exercises the `IsEdgeInjective` condition. ~20 LOC.
* **(sibling DRY refactor — cross-slug)** — collapses ~100 LOC across
  the parent and `KonigsbergOQ03OQ02` slug. Pure refactor.
* **(EGW proof — multi-week)** — locally-finite case using
  `SimpleGraph.Walk.IsEulerian` + König's lemma machinery.

Recommended for S6: **(EGW statement) + (one-edge graph)** in one
session — both small, both concrete, both immediately useful as
Aristotle targets / sanity checks.
