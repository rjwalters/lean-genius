import Proofs.SpernerGridBase

/-
# sperner-ndim-oq-02: self-contained unoriented Freudenthal cell machinery

This module is a clean extraction of the `GridSimplex` cell structure and its
chain-coordinate lemmas from `SpernerGrid.lean`'s SECTIONS III–V (plus the
`BaryPoint.transfer` helper of SECTION VI). The parent `SpernerGrid.lean`
additionally bundles the *oriented* `gridAdj` machinery (lines ~600–1556) whose
`boundary_doors_odd` is **false** as stated — the motivating defect of this
problem — and which does not currently compile. Everything reproduced here lives
strictly *before* that broken block and depends only on the clean `BaryPoint`
API from `Proofs.SpernerGridBase` (`import Mathlib` only).

Reproducing it on the compiling foundation makes the cell geometry — the
`d+1`-vertex mass-transfer chain, its `verts_injective`, the `miss`-coordinate
tracking, and the `incDir` complement surjection — available to the "Option C"
*unoriented* `SpernerTriangulation` instance (`sperner-ndim-oq-02`) without
importing the broken file. `GridSimplex` is an **oriented chain** encoding; the
Phase-1 instance quotients out that orientation with the canonicality predicate
`SpernerGrid.IsCanon` from `SpernerGridBase` (see the canonical-cell subtype
`CanonCell` in `SpernerNDimOQ02Cell.lean` and the parallel `CanonSimplex`
development in `SpernerNDimOQ02.lean`).

Namespace is kept as `SpernerGrid` (import-disjoint from the broken file, so no
module ever sees two `SpernerGrid.GridSimplex`). No new axioms or sorries.
-/

open Finset

namespace SpernerGrid

-- v4.31 compat (#38065): SECTIONS III-V (GridSimplex cell machinery) were
-- duplicated into Proofs.SpernerGridBase (imported above) and are removed
-- here to avoid duplicate declarations; only the BaryPoint.transfer helpers
-- (SECTION VI) remain.

-- ============================================================
-- SECTION VI: Adjacency
-- ============================================================

/-- Helper: construct a new BaryPoint by transferring one
unit from coordinate `dec` to coordinate `inc`. -/
noncomputable def BaryPoint.transfer {d N : ℕ}
    (v : BaryPoint d N) (inc dec : Fin (d + 1))
    (h_ne : inc ≠ dec) (h_pos : 0 < v.coords dec) :
    BaryPoint d N where
  coords := fun j =>
    if j = inc then v.coords j + 1
    else if j = dec then v.coords j - 1
    else v.coords j
  sum_eq := by
    have hv := v.sum_eq
    have hkey : ∀ (j : Fin (d + 1)), j ∈ Finset.univ →
      (if j = inc then v.coords j + 1
        else if j = dec then v.coords j - 1
        else v.coords j) + (if j = dec then 1 else 0) =
        v.coords j + (if j = inc then 1 else 0) := by
      intro j _; split_ifs <;> simp_all <;> omega
    have hsums := Finset.sum_congr rfl hkey
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsums
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hsums
    omega

@[simp]
theorem BaryPoint.transfer_coords_inc {d N : ℕ}
    (v : BaryPoint d N) (inc dec : Fin (d + 1))
    (h_ne : inc ≠ dec) (h_pos : 0 < v.coords dec) :
    (v.transfer inc dec h_ne h_pos).coords inc =
    v.coords inc + 1 := by
  simp [BaryPoint.transfer]

@[simp]
theorem BaryPoint.transfer_coords_dec {d N : ℕ}
    (v : BaryPoint d N) (inc dec : Fin (d + 1))
    (h_ne : inc ≠ dec) (h_pos : 0 < v.coords dec) :
    (v.transfer inc dec h_ne h_pos).coords dec =
    v.coords dec - 1 := by
  simp [BaryPoint.transfer, Ne.symm h_ne]

@[simp]
theorem BaryPoint.transfer_coords_other {d N : ℕ}
    (v : BaryPoint d N) (inc dec : Fin (d + 1))
    (h_ne : inc ≠ dec) (h_pos : 0 < v.coords dec)
    (j : Fin (d + 1)) (hj_inc : j ≠ inc)
    (hj_dec : j ≠ dec) :
    (v.transfer inc dec h_ne h_pos).coords j =
    v.coords j := by
  simp [BaryPoint.transfer, hj_inc, hj_dec]

end SpernerGrid
