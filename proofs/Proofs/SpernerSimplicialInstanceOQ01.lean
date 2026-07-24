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

/-!
## Candidate C data layer: `LatticePoint m` and `TriCell m` (S3 ACT)

The general-`m` construction (S3 ACT, per PREPs #18625/#18654/#18719):
the vertex carrier `LatticePoint m` (lattice points of Δ² at resolution
`m`) and the cell type `TriCell m` (`T(m)` up-triangles + `T(m-1)`
down-triangles = `m²` cells), with `DecidableEq` and `Fintype` instances —
the data prerequisites for the eventual
`Triangulation (LatticePoint m) 2` instance. The vertex map (`triVtx`,
S4), the adjacency table, and the four `Triangulation` axioms are the
S4+ continuation; they are the genuine open core of OQ-01 (the
`decide`-based discharge used by `standardTriangle2` above cannot work
`m`-parametrically).
-/

section Triangle

/-- A lattice point in the size-`m` standard 2-simplex Δ²: `(i, j)` with
`i + j ≤ m`. Carried by `Fin (m+1) × Fin (m+1)` so `DecidableEq` and
`Fintype` synthesize for free (`Subtype.instDecidableEq`,
`Subtype.fintype`); the subtype predicate `p.1 + p.2 ≤ m` is the only
load-bearing constraint. `#(LatticePoint m) = (m+1)(m+2)/2`. -/
abbrev LatticePoint (m : ℕ) : Type :=
  {p : Fin (m + 1) × Fin (m + 1) // p.1.val + p.2.val ≤ m}

/-- A cell in the standard subdivision of Δ² at resolution `m`.

`up i j h` is the up-triangle with lower-left corner `(i, j)`; its
vertices are `(i, j)`, `(i+1, j)`, `(i, j+1)`. Requires `i + j < m`.

`down i j h` is the down-triangle with hypotenuse on `x + y = i + j + 1`;
its vertices are `(i+1, j)`, `(i, j+1)`, `(i+1, j+1)`. Requires
`i + j + 1 < m`.

Cardinality: `T(m)` up-cells + `T(m-1)` down-cells = `m²` total. -/
inductive TriCell (m : ℕ) : Type
  | up (i j : ℕ) (h : i + j < m) : TriCell m
  | down (i j : ℕ) (h : i + j + 1 < m) : TriCell m
  deriving DecidableEq

namespace TriCell

/-- `TriCell m` is a `Fintype`: up-cells and down-cells are enumerated
from `Fin m × Fin m` via `Finset.filterMap` (the strict bounds
`i + j < m` and `i + j + 1 < m` each force `i < m` and `j < m`, so the
square carrier covers all cells). -/
instance instFintype (m : ℕ) : Fintype (TriCell m) where
  elems :=
    (Finset.univ : Finset (Fin m × Fin m)).filterMap
      (fun ij =>
        if h : (ij.1 : ℕ) + (ij.2 : ℕ) < m then
          some (TriCell.up ij.1.val ij.2.val h)
        else none)
      (by
        rintro ⟨i, j⟩ ⟨i', j'⟩ b hb hb'
        simp only [Option.mem_def] at hb hb'
        by_cases hij : (i : ℕ) + (j : ℕ) < m
        · rw [dif_pos hij] at hb
          by_cases hij' : (i' : ℕ) + (j' : ℕ) < m
          · rw [dif_pos hij'] at hb'
            rw [Option.some.injEq] at hb hb'
            obtain rfl := hb
            injection hb'.symm with hi hj
            obtain rfl : i = i' := Fin.val_injective hi
            obtain rfl : j = j' := Fin.val_injective hj
            rfl
          · rw [dif_neg hij'] at hb'
            cases hb'
        · rw [dif_neg hij] at hb
          cases hb)
    ∪
    (Finset.univ : Finset (Fin m × Fin m)).filterMap
      (fun ij =>
        if h : (ij.1 : ℕ) + (ij.2 : ℕ) + 1 < m then
          some (TriCell.down ij.1.val ij.2.val h)
        else none)
      (by
        rintro ⟨i, j⟩ ⟨i', j'⟩ b hb hb'
        simp only [Option.mem_def] at hb hb'
        by_cases hij : (i : ℕ) + (j : ℕ) + 1 < m
        · rw [dif_pos hij] at hb
          by_cases hij' : (i' : ℕ) + (j' : ℕ) + 1 < m
          · rw [dif_pos hij'] at hb'
            rw [Option.some.injEq] at hb hb'
            obtain rfl := hb
            injection hb'.symm with hi hj
            obtain rfl : i = i' := Fin.val_injective hi
            obtain rfl : j = j' := Fin.val_injective hj
            rfl
          · rw [dif_neg hij'] at hb'
            cases hb'
        · rw [dif_neg hij] at hb
          cases hb)
  complete := fun c => by
    rcases c with ⟨i, j, h⟩ | ⟨i, j, h⟩
    · apply Finset.mem_union_left
      rw [Finset.mem_filterMap]
      refine ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), Finset.mem_univ _, ?_⟩
      simp [h]
    · apply Finset.mem_union_right
      rw [Finset.mem_filterMap]
      refine ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), Finset.mem_univ _, ?_⟩
      simp [h]

end TriCell

end Triangle

end Triangulation
