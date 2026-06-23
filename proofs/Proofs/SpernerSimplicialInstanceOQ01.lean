/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Proofs.SpernerSimplicialInstance
import Mathlib.Data.Fin.VecNotation

/-!
# Standard 2-Simplex Triangulation at Resolution 2 (OQ-01, Candidate C seed)

The parent `Proofs.SpernerSimplicialInstance` provides the abstract
`Triangulation V n` structure, a fully-proved 1-dimensional
`intervalTriangulation m`, and a single-cell 2-dimensional
`trivialTriangle : Triangulation ℕ 2` smoke test.

This file answers the *smallest genuinely subdivided* case of
**sperner-simplicial-instance-oq-01**: the standard regular
triangulation of the 2-simplex `Δ²` at resolution `m = 2`, as a
concrete `Triangulation (Fin 6) 2` instance with all four
`Triangulation` axioms machine-checked (0 sorries, 0 axioms).

## Geometry

The resolution-2 subdivision of `Δ²` has 6 lattice points
`(i, j)` with `i, j ≥ 0` and `i + j ≤ 2`, indexed by `Fin 6`:

```
        v5 (0,2)
        |  \
        v3--v4         v3=(0,1) v4=(1,1)
        |  \ | \
        v0--v1--v2     v0=(0,0) v1=(1,0) v2=(2,0)
```

and `m² = 4` triangular cells: three *up*-triangles and one
central *down*-triangle.

| cell | type | ordered vertices              | lattice points          |
|------|------|-------------------------------|-------------------------|
| `c0` | up   | `v0, v1, v3`                  | `(0,0),(1,0),(0,1)`     |
| `c1` | up   | `v1, v2, v4`                  | `(1,0),(2,0),(1,1)`     |
| `c2` | up   | `v3, v4, v5`                  | `(0,1),(1,1),(0,2)`     |
| `c3` | down | `v1, v3, v4`                  | `(1,0),(0,1),(1,1)`     |

The down-triangle `c3` is entirely interior: each of its three
edges is shared with one up-triangle. Each up-triangle has exactly
one interior edge (shared with `c3`) and two boundary edges. This
is the defining feature that distinguishes the m=2 instance from
the single-cell `trivialTriangle`: it exhibits *real* 2-dimensional
pseudomanifold adjacency.

## Adjacency

`adj s k = some (s', k')` means the edge of `s` opposite vertex `k`
coincides with the edge of `s'` opposite vertex `k'`.

| edge        | in `s` (opposite) | in `s'` (opposite) | pair               |
|-------------|-------------------|--------------------|--------------------|
| `{v1, v3}`  | `c0`, pos 0       | `c3`, pos 2        | `c0 0 ↔ c3 2`      |
| `{v1, v4}`  | `c1`, pos 1       | `c3`, pos 1        | `c1 1 ↔ c3 1`      |
| `{v3, v4}`  | `c2`, pos 2       | `c3`, pos 0        | `c2 2 ↔ c3 0`      |

All other faces are boundary (`none`).

## Scope and honesty

- This is the **resolution-2** case only, not the general `m`
  construction. The general `standardTriangleTriangulation m hm`
  (an inductive `TriCell m` with `T(m)` up + `T(m-1)` down cells
  and a case-table adjacency) remains the open core of OQ-01.
- Because both the cell type (`Fin 4`) and the vertex type
  (`Fin 6`) are finite with decidable equality, **all four axioms
  are discharged by `decide`** — no hand proofs are required at
  this resolution. The general-`m` axioms cannot use `decide`
  (the domains are `m`-parametric) and are the genuine difficulty.

## Tags

combinatorics, topology, sperner, triangulation, 2-simplex, oq-01
-/

namespace Triangulation
namespace StandardTriangle2

/-- Ordered vertices of each of the 4 cells, as a map
`Fin 4 → Fin 3 → Fin 6`. Rows are cells `c0..c3`; columns are the
local vertex positions `0,1,2`. Defined by a `Nat`-literal match
(rather than `![…]` vector notation) so that `decide` reduces it
without triggering the `Lean.Expr.appArg!` reduction panic. -/
def tvtx (s : Fin 4) (k : Fin 3) : Fin 6 :=
  match s.val, k.val with
  | 0, 0 => 0 | 0, 1 => 1 | 0, _ => 3
  | 1, 0 => 1 | 1, 1 => 2 | 1, _ => 4
  | 2, 0 => 3 | 2, 1 => 4 | 2, _ => 5
  | _, 0 => 1 | _, 1 => 3 | _, _ => 4

/-- Pseudomanifold adjacency table `Fin 4 → Fin 3 → Option (Fin 4 × Fin 3)`.
Entry `(s, k)` is the neighbour across the edge of cell `s` opposite
local vertex `k`, or `none` on the boundary. -/
def tadj (s : Fin 4) (k : Fin 3) : Option (Fin 4 × Fin 3) :=
  match s.val, k.val with
  | 0, 0 => some (3, 2)
  | 1, 1 => some (3, 1)
  | 2, 2 => some (3, 0)
  | 3, 0 => some (2, 2)
  | 3, 1 => some (1, 1)
  | 3, 2 => some (0, 0)
  | _, _ => none

/-- The standard regular triangulation of `Δ²` at resolution `m = 2`:
3 up-triangles + 1 central down-triangle, with all four
`Triangulation` axioms machine-checked by `decide`. -/
def standardTriangle2 : Triangulation (Fin 6) 2 where
  Cell := Fin 4
  cellDecEq := inferInstance
  cellFintype := inferInstance
  vertex := tvtx
  vertex_injective := by
    intro s a b hab
    fin_cases s <;> fin_cases a <;> fin_cases b <;> revert hab <;> decide
  adj := tadj
  adj_symm := by decide
  adj_vertex := by decide
  adj_ne := by decide

end StandardTriangle2

open StandardTriangle2

/-- **2-d Sperner's lemma, resolution-2 instance**: if the boundary
doors of the standard `Δ²` triangulation at resolution 2 are odd
under a coloring `c`, then some cell is panchromatic. A direct
specialisation of the abstract `Triangulation.sperner`, the 2-d
analogue of `interval_sperner`. -/
theorem standardTriangle2_sperner
    (c : Fin 6 → Fin 3)
    (hbdry : Odd (Finset.univ.filter
      (fun p : Fin 4 × Fin 3 =>
        CellComplex.IsDoor c standardTriangle2.toCellComplex p.1 p.2 ∧
        standardTriangle2.adj p.1 p.2 = none)).card) :
    ∃ s : Fin 4,
      CellComplex.IsPanchromatic c standardTriangle2.toCellComplex s :=
  Triangulation.sperner standardTriangle2 c hbdry

end Triangulation
