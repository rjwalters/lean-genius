/-
# Erdős Problem #634 (OQ-02) — Each medial piece is a half-scale homothetic copy

Source: Erdős Problem #634 (erdosproblems.com/634), open question
`erdos-634-medial-congruence-oq-02`. Companion to the covering / interior-
disjointness line of work (`Erdos634MedialCoveringOQ02`,
`Erdos634MedialDisjointOQ02`, `Erdos634MedialCentralEdgeOQ03`,
`Erdos634MedialInteriorDisjointOQ02`).

## What this adds

The covering and disjointness files describe *how the four medial pieces fit
together* (they cover `A B C` and their relative interiors are pairwise
disjoint). This file supplies the complementary *shape* statement — the
geometric substance behind the parent entry's **congruence** claim — namely that
each of the four medial pieces is literally the whole triangle `A B C` shrunk by
the factor `½` through an explicit homothety (a scaling map). With
`mAB = midpoint A B`, `mBC = midpoint B C`, `mCA = midpoint C A`:

* `pieceA_eq_homothety` — the corner piece `tri A mAB mCA` is the image of the
  whole triangle under `x ↦ midpoint A x`, the homothety centred at `A` with
  ratio `½`.
* `pieceB_eq_homothety`, `pieceC_eq_homothety` — the same at `B` and `C`.
* `pieceCentral_eq_homothety` — the central piece `tri mBC mCA mAB` is the image
  of the whole under `x ↦ ½•(A+B+C) − ½•x`, the point reflection through the
  centroid followed by the `½` scaling (equivalently the homothety of ratio
  `−½` centred at the centroid).

Because each piece is a homothetic image of `A B C` with ratio `±½`, every piece
is directly exhibited as a half-scale copy of the original — which is exactly the
"four congruent half-scale medial triangles" content of the parent entry, now
tied to the concrete pieces of the tiling. Homotheties of the same absolute ratio
are isometry-congruent, so this also re-derives the mutual congruence of the four
pieces from a single uniform description.

Each statement is a set equality between `triHull` (the barycentric solid
triangle of `Erdos634MedialCoveringOQ02`) and a `Set.image`; via
`triHull_eq_convexHull` the corollaries `piece*_eq_homothety_convexHull` phrase
the same facts with Mathlib's `convexHull`.

## How it is proved

A point of the corner piece at `A` with barycentric coordinates `(a,b,c)` in
`A, mAB, mCA` and a point of the whole triangle with the *same* coordinates
`(a,b,c)` in `A, B, C` are related by `x ↦ midpoint A x`: both expand (using
`a+b+c = 1`) to `(a + b/2 + c/2)•A + (b/2)•B + (c/2)•C`. The coordinate tuple is
carried across unchanged, so the two inclusions are witnessed by the identical
triple and closed by `match_scalars <;> linarith` on the midpoint expansion
(exactly the arithmetic used for the covering inclusions). The central piece is
identical with the reflection map in place of the corner homothety.

Everything is unconditional and axiom-free — no non-degeneracy hypothesis is
needed, since these are equalities of parametrised images, not disjointness
facts.

Tags: geometry, erdos, dissection, tiling, homothety, congruence, barycentric
-/

import Mathlib
import Proofs.Erdos634MedialCoveringOQ02

set_option linter.unusedSectionVars false

namespace Erdos634MedialHomothetyOQ02

open Erdos634MedialCoveringOQ02

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-
## The four medial homotheties

Each corner piece is the image of the whole triangle under the half-scale
homothety centred at that corner (`x ↦ midpoint corner x`). The central piece is
the image under the `−½`-homothety centred at the centroid, written concretely as
`x ↦ ½•(A+B+C) − ½•x`.
-/

/-- **Corner piece at `A` is a half-homothety of the whole.** The corner medial
triangle `tri A mAB mCA` is exactly the image of `A B C` under `x ↦ midpoint A x`,
the homothety centred at `A` with ratio `½`. -/
theorem pieceA_eq_homothety (A B C : V) :
    triHull A (midpoint ℝ A B) (midpoint ℝ C A)
      = (fun x => midpoint ℝ A x) '' triHull A B C := by
  apply Set.Subset.antisymm
  · rintro x ⟨a, b, c, ha, hb, hc, hs, rfl⟩
    refine ⟨a • A + b • B + c • C, ⟨a, b, c, ha, hb, hc, hs, rfl⟩, ?_⟩
    simp only [midpoint_eq_smul_add, invOf_eq_inv]; match_scalars <;> linarith
  · rintro x ⟨y, ⟨a, b, c, ha, hb, hc, hs, rfl⟩, rfl⟩
    refine ⟨a, b, c, ha, hb, hc, hs, ?_⟩
    simp only [midpoint_eq_smul_add, invOf_eq_inv]; match_scalars <;> linarith

/-- **Corner piece at `B` is a half-homothety of the whole.** The corner medial
triangle `tri mAB B mBC` is the image of `A B C` under `x ↦ midpoint B x`. -/
theorem pieceB_eq_homothety (A B C : V) :
    triHull (midpoint ℝ A B) B (midpoint ℝ B C)
      = (fun x => midpoint ℝ B x) '' triHull A B C := by
  apply Set.Subset.antisymm
  · rintro x ⟨a, b, c, ha, hb, hc, hs, rfl⟩
    refine ⟨a • A + b • B + c • C, ⟨a, b, c, ha, hb, hc, hs, rfl⟩, ?_⟩
    simp only [midpoint_eq_smul_add, invOf_eq_inv]; match_scalars <;> linarith
  · rintro x ⟨y, ⟨a, b, c, ha, hb, hc, hs, rfl⟩, rfl⟩
    refine ⟨a, b, c, ha, hb, hc, hs, ?_⟩
    simp only [midpoint_eq_smul_add, invOf_eq_inv]; match_scalars <;> linarith

/-- **Corner piece at `C` is a half-homothety of the whole.** The corner medial
triangle `tri mCA mBC C` is the image of `A B C` under `x ↦ midpoint C x`. -/
theorem pieceC_eq_homothety (A B C : V) :
    triHull (midpoint ℝ C A) (midpoint ℝ B C) C
      = (fun x => midpoint ℝ C x) '' triHull A B C := by
  apply Set.Subset.antisymm
  · rintro x ⟨a, b, c, ha, hb, hc, hs, rfl⟩
    refine ⟨a • A + b • B + c • C, ⟨a, b, c, ha, hb, hc, hs, rfl⟩, ?_⟩
    simp only [midpoint_eq_smul_add, invOf_eq_inv]; match_scalars <;> linarith
  · rintro x ⟨y, ⟨a, b, c, ha, hb, hc, hs, rfl⟩, rfl⟩
    refine ⟨a, b, c, ha, hb, hc, hs, ?_⟩
    simp only [midpoint_eq_smul_add, invOf_eq_inv]; match_scalars <;> linarith

/-- **Central piece is a `−½`-homothety of the whole.** The central medial
triangle `tri mBC mCA mAB` is the image of `A B C` under
`x ↦ ½•(A+B+C) − ½•x`, the homothety of ratio `−½` centred at the centroid
`(A+B+C)/3`. It carries `A ↦ mBC`, `B ↦ mCA`, `C ↦ mAB`. -/
theorem pieceCentral_eq_homothety (A B C : V) :
    triHull (midpoint ℝ B C) (midpoint ℝ C A) (midpoint ℝ A B)
      = (fun x => (2 : ℝ)⁻¹ • (A + B + C) - (2 : ℝ)⁻¹ • x) '' triHull A B C := by
  apply Set.Subset.antisymm
  · rintro x ⟨a, b, c, ha, hb, hc, hs, rfl⟩
    refine ⟨a • A + b • B + c • C, ⟨a, b, c, ha, hb, hc, hs, rfl⟩, ?_⟩
    simp only [midpoint_eq_smul_add, invOf_eq_inv]; match_scalars <;> linarith
  · rintro x ⟨y, ⟨a, b, c, ha, hb, hc, hs, rfl⟩, rfl⟩
    refine ⟨a, b, c, ha, hb, hc, hs, ?_⟩
    simp only [midpoint_eq_smul_add, invOf_eq_inv]; match_scalars <;> linarith

/-
## `convexHull`-phrased corollaries

The same four identities with Mathlib's `convexHull` in place of `triHull`, via
`triHull_eq_convexHull`.
-/

/-- Corner piece at `A` as a homothety image, phrased with `convexHull`. -/
theorem pieceA_eq_homothety_convexHull (A B C : V) :
    convexHull ℝ ({A, midpoint ℝ A B, midpoint ℝ C A} : Set V)
      = (fun x => midpoint ℝ A x) '' convexHull ℝ ({A, B, C} : Set V) := by
  rw [← triHull_eq_convexHull, ← triHull_eq_convexHull, pieceA_eq_homothety]

/-- Corner piece at `B` as a homothety image, phrased with `convexHull`. -/
theorem pieceB_eq_homothety_convexHull (A B C : V) :
    convexHull ℝ ({midpoint ℝ A B, B, midpoint ℝ B C} : Set V)
      = (fun x => midpoint ℝ B x) '' convexHull ℝ ({A, B, C} : Set V) := by
  rw [← triHull_eq_convexHull, ← triHull_eq_convexHull, pieceB_eq_homothety]

/-- Corner piece at `C` as a homothety image, phrased with `convexHull`. -/
theorem pieceC_eq_homothety_convexHull (A B C : V) :
    convexHull ℝ ({midpoint ℝ C A, midpoint ℝ B C, C} : Set V)
      = (fun x => midpoint ℝ C x) '' convexHull ℝ ({A, B, C} : Set V) := by
  rw [← triHull_eq_convexHull, ← triHull_eq_convexHull, pieceC_eq_homothety]

/-- Central piece as a homothety image, phrased with `convexHull`. -/
theorem pieceCentral_eq_homothety_convexHull (A B C : V) :
    convexHull ℝ ({midpoint ℝ B C, midpoint ℝ C A, midpoint ℝ A B} : Set V)
      = (fun x => (2 : ℝ)⁻¹ • (A + B + C) - (2 : ℝ)⁻¹ • x) ''
          convexHull ℝ ({A, B, C} : Set V) := by
  rw [← triHull_eq_convexHull, ← triHull_eq_convexHull, pieceCentral_eq_homothety]

/-
## The packaged statement
-/

/-- **The medial subdivision is four half-scale homothetic copies.** Every one of
the four medial pieces is the image of the whole triangle `A B C` under an
explicit homothety of ratio `±½`: the three corner pieces via the half-scale
homotheties centred at the respective vertices, and the central piece via the
`−½`-homothety centred at the centroid. This is the uniform "half-scale copy"
description of the pieces underlying the parent entry's congruence claim. -/
theorem medial_pieces_are_half_homotheties (A B C : V) :
    triHull A (midpoint ℝ A B) (midpoint ℝ C A)
        = (fun x => midpoint ℝ A x) '' triHull A B C ∧
    triHull (midpoint ℝ A B) B (midpoint ℝ B C)
        = (fun x => midpoint ℝ B x) '' triHull A B C ∧
    triHull (midpoint ℝ C A) (midpoint ℝ B C) C
        = (fun x => midpoint ℝ C x) '' triHull A B C ∧
    triHull (midpoint ℝ B C) (midpoint ℝ C A) (midpoint ℝ A B)
        = (fun x => (2 : ℝ)⁻¹ • (A + B + C) - (2 : ℝ)⁻¹ • x) '' triHull A B C :=
  ⟨pieceA_eq_homothety A B C, pieceB_eq_homothety A B C,
   pieceC_eq_homothety A B C, pieceCentral_eq_homothety A B C⟩

end Erdos634MedialHomothetyOQ02
