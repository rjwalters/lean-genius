/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Mathlib

/-
# Barycentric Lattice Points on the Subdivided d-Simplex

This is the clean, self-contained foundation of barycentric lattice points
`BaryPoint d N` on the standard `d`-simplex with subdivision parameter `N`:
functions `Fin (d+1) → ℕ` whose coordinates sum to `N`.

It is extracted verbatim from `SpernerGrid.lean` (SECTION II) into its own
module for two reasons:

* `SpernerGrid.lean` bundles `BaryPoint` together with the *oriented*
  `GridSimplex`/`gridAdj` machinery, which is known-incomplete (its
  `boundary_doors_odd` is *false* as stated — see the design note in that
  file and `sperner-ndim-oq-02`) and does not currently compile.
* The Option-C resolution of `sperner-ndim-oq-02` reuses the complete
  abstract `SpernerNDim` framework over an *unoriented* Freudenthal grid.
  Both the `BaryPoint ≃ Vertex` coordinate bridge (`SpernerNDimOQ02.lean`)
  and the future unoriented triangulation instance build on this clean
  `BaryPoint` API, with no dependence on the abandoned oriented machinery.

Only `Mathlib` is imported. There are no axioms and no sorries. The namespace
is kept as `SpernerGrid` so downstream references read identically to the
original; the module is import-disjoint from `SpernerGrid.lean`, so no file
sees both definitions of `SpernerGrid.BaryPoint` simultaneously.
-/

set_option maxHeartbeats 400000

open Finset

namespace SpernerGrid

-- ============================================================
-- Barycentric Lattice Points
-- ============================================================

/-- A barycentric lattice point on the standard d-simplex with
subdivision parameter N: coordinates (b₀, ..., b_d) with
b_i ≥ 0 and ∑ b_i = N. -/
@[ext]
structure BaryPoint (d N : ℕ) where
  coords : Fin (d + 1) → ℕ
  sum_eq : ∑ i, coords i = N

instance (d N : ℕ) : DecidableEq (BaryPoint d N) := by
  intro a b
  by_cases h : a.coords = b.coords
  · exact isTrue (BaryPoint.ext h)
  · exact isFalse (fun hab =>
      h (congr_arg BaryPoint.coords hab))

instance baryPointFintype (d N : ℕ) :
    Fintype (BaryPoint d N) := by
  have equiv : BaryPoint d N ≃
      { f : Fin (d + 1) → Fin (N + 1) //
        ∑ i, (f i).val = N } :=
    { toFun := fun p =>
        ⟨fun i => ⟨p.coords i, by
          have h1 := Finset.single_le_sum
            (f := p.coords) (fun j _ => Nat.zero_le _)
            (Finset.mem_univ i)
          have h2 := p.sum_eq
          omega⟩,
         by simp [p.sum_eq]⟩
      invFun := fun ⟨f, hf⟩ =>
        ⟨fun i => (f i).val, by simpa using hf⟩
      left_inv := fun p => by ext i; simp
      right_inv := fun ⟨f, hf⟩ => by
        ext i; simp }
  exact Fintype.ofEquiv _ equiv.symm

/-- A vertex lies on face k: its k-th barycentric coordinate
is zero. -/
def BaryPoint.onFace {d N : ℕ} (v : BaryPoint d N)
    (k : Fin (d + 1)) : Prop :=
  v.coords k = 0

instance {d N : ℕ} (v : BaryPoint d N)
    (k : Fin (d + 1)) :
    Decidable (v.onFace k) :=
  inferInstanceAs (Decidable (_ = _))

/-- Sperner condition: on face k (where b_k = 0), color k is
forbidden. -/
def IsSperner {d N : ℕ}
    (c : BaryPoint d N → Fin (d + 1)) : Prop :=
  ∀ (v : BaryPoint d N) (k : Fin (d + 1)),
    v.onFace k → c v ≠ k

end SpernerGrid
