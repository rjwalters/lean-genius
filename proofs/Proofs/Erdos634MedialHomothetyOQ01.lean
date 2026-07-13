/-
# Erdős Problem #634 (OQ-01) — Each k²-subdivision cell is a `1/k`-scale homothetic copy

Source: Erdős Problem #634 (erdosproblems.com/634), open question
`erdos-634-medial-congruence-oq-01`, the general-`k` reptiling of the base entry
`Proofs.Erdos634MedialCongruence`. Companion to `Erdos634MedialCongruenceOQ01`
(the general-`k` *congruence* + `k²` count) and to `Erdos634MedialHomothetyOQ02`
(the `k = 2` *shape* / homothety statement).

## The gap this closes

`Erdos634MedialCongruenceOQ01` proves that the `k`-subdivision of a triangle
`A B C` — cutting each side into `k` equal parts and drawing the grid of
parallels — produces `k²` mutually **congruent** sub-triangles (`cong_U0_Up`,
`cong_U0_Down`, …), each congruent to the single base cell `U0`.

`Erdos634MedialHomothetyOQ02` supplies the complementary **shape** statement, but
only for the medial `k = 2` case: each of the four medial pieces is the image of
the *whole* triangle `A B C` under an explicit homothety of ratio `±½`.

This file lifts that shape statement to **all** `k`.  With the grid point
`P i j = A + (i/k)(B-A) + (j/k)(C-A)`:

* `Up_eq_homothety`   — the upward cell `(P i j, P (i+1) j, P i (j+1))` is exactly
  the image of `A B C` under the homothety `x ↦ P i j + (1/k)·(x − A)`, ratio
  `+1/k` (a `(1/k)`-scale copy of the *whole* triangle, translated into the grid);
* `Down_eq_homothety` — the downward cell `(P (i+1)(j+1), P i (j+1), P (i+1) j)`
  is the image of `A B C` under `x ↦ P (i+1)(j+1) − (1/k)·(x − A)`, the
  ratio `−1/k` homothety (a `180°`-rotated `(1/k)`-scale copy).

Together with `Erdos634MedialCongruenceOQ01.card_pieces` (there are exactly `k²`
cells) this exhibits the classical **square reptiling**: `A B C` is `k²` copies of
itself scaled by `1/k`.  This is the honest self-similarity content behind the
"`k²` is dissectable" positive result — every cell is literally the original
triangle shrunk by `1/k`, not merely congruent to some fixed sub-cell.

## How it is proved

A point of a cell with barycentric coordinates `(a,b,c)` in the cell's three
vertices, and the point of the whole triangle with the *same* coordinates
`(a,b,c)` in `A, B, C`, are related by the stated affine map.  Substituting
`c = 1 − a − b` (the barycentric constraint) turns each inclusion into a pure
module identity in `A, B, C` with scalar coefficients that are ring expressions
in `a, b, i, j, k⁻¹`, closed uniformly by `module`.  The `k = 0` degenerate case
is handled automatically: there `(k:ℝ)⁻¹ = 0` and every `P i j = A`, so both
sides collapse to `{A}` and the same identity still holds.

Everything is unconditional and axiom-free — no non-degeneracy hypothesis is
needed, since these are equalities of parametrised images, not disjointness
facts.  Via `triHull_eq_convexHull` the corollaries `*_eq_homothety_convexHull`
phrase the same facts with Mathlib's `convexHull`.

Tags: geometry, erdos, dissection, tiling, reptile, homothety, self-similar, barycentric
-/

import Mathlib
import Proofs.Erdos634MedialCoveringOQ02
import Proofs.Erdos634MedialCongruenceOQ01

set_option linter.unusedSectionVars false

namespace Erdos634MedialHomothetyOQ01

open Erdos634MedialCoveringOQ02 Erdos634MedialCongruenceOQ01

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ## The two families of grid homotheties -/

/-- **Upward cell as a `+1/k` homothety of the whole.** The upward sub-triangle
`(P i j, P (i+1) j, P i (j+1))` of the `k`-subdivision is exactly the image of the
whole triangle `A B C` under `x ↦ P i j + (1/k)·(x − A)`, the homothety of ratio
`+1/k` carrying `A ↦ P i j`, `B ↦ P (i+1) j`, `C ↦ P i (j+1)`. -/
theorem Up_eq_homothety (A B C : V) (k i j : ℕ) :
    triHull (P A B C k i j) (P A B C k (i + 1) j) (P A B C k i (j + 1))
      = (fun x => P A B C k i j + (k : ℝ)⁻¹ • (x - A)) '' triHull A B C := by
  apply Set.Subset.antisymm
  · rintro x ⟨a, b, c, ha, hb, hc, hs, rfl⟩
    refine ⟨a • A + b • B + c • C, ⟨a, b, c, ha, hb, hc, hs, rfl⟩, ?_⟩
    obtain rfl : c = 1 - a - b := by linarith
    simp only [P]; push_cast; module
  · rintro x ⟨y, ⟨a, b, c, ha, hb, hc, hs, rfl⟩, rfl⟩
    refine ⟨a, b, c, ha, hb, hc, hs, ?_⟩
    obtain rfl : c = 1 - a - b := by linarith
    simp only [P]; push_cast; module

/-- **Downward cell as a `−1/k` homothety of the whole.** The downward
sub-triangle `(P (i+1)(j+1), P i (j+1), P (i+1) j)` of the `k`-subdivision is the
image of `A B C` under `x ↦ P (i+1)(j+1) − (1/k)·(x − A)`, the homothety of ratio
`−1/k` (a `180°`-rotated `(1/k)`-scale copy) carrying `A ↦ P (i+1)(j+1)`,
`B ↦ P i (j+1)`, `C ↦ P (i+1) j`. -/
theorem Down_eq_homothety (A B C : V) (k i j : ℕ) :
    triHull (P A B C k (i + 1) (j + 1)) (P A B C k i (j + 1)) (P A B C k (i + 1) j)
      = (fun x => P A B C k (i + 1) (j + 1) - (k : ℝ)⁻¹ • (x - A)) '' triHull A B C := by
  apply Set.Subset.antisymm
  · rintro x ⟨a, b, c, ha, hb, hc, hs, rfl⟩
    refine ⟨a • A + b • B + c • C, ⟨a, b, c, ha, hb, hc, hs, rfl⟩, ?_⟩
    obtain rfl : c = 1 - a - b := by linarith
    simp only [P]; push_cast; module
  · rintro x ⟨y, ⟨a, b, c, ha, hb, hc, hs, rfl⟩, rfl⟩
    refine ⟨a, b, c, ha, hb, hc, hs, ?_⟩
    obtain rfl : c = 1 - a - b := by linarith
    simp only [P]; push_cast; module

/-! ## `convexHull`-phrased corollaries -/

/-- The upward cell as a homothety image, phrased with Mathlib's `convexHull`. -/
theorem Up_eq_homothety_convexHull (A B C : V) (k i j : ℕ) :
    convexHull ℝ ({P A B C k i j, P A B C k (i + 1) j, P A B C k i (j + 1)} : Set V)
      = (fun x => P A B C k i j + (k : ℝ)⁻¹ • (x - A)) '' convexHull ℝ ({A, B, C} : Set V) := by
  rw [← triHull_eq_convexHull, ← triHull_eq_convexHull, Up_eq_homothety]

/-- The downward cell as a homothety image, phrased with Mathlib's `convexHull`. -/
theorem Down_eq_homothety_convexHull (A B C : V) (k i j : ℕ) :
    convexHull ℝ
        ({P A B C k (i + 1) (j + 1), P A B C k i (j + 1), P A B C k (i + 1) j} : Set V)
      = (fun x => P A B C k (i + 1) (j + 1) - (k : ℝ)⁻¹ • (x - A)) ''
          convexHull ℝ ({A, B, C} : Set V) := by
  rw [← triHull_eq_convexHull, ← triHull_eq_convexHull, Down_eq_homothety]

/-! ## The base cell is the vertex-centred homothety -/

/-- **The base cell is the `1/k`-homothety centred at `A`.** The corner cell
`U0 = (P 0 0, P 1 0, P 0 1)` is the image of the whole triangle under
`x ↦ A + (1/k)·(x − A)`, i.e. the homothety of ratio `1/k` centred at the vertex
`A`.  (This is the `Up 0 0` instance, using `P 0 0 = A`.) -/
theorem U0_eq_homothety (A B C : V) (k : ℕ) :
    triHull (U0 A B C k).1 (U0 A B C k).2.1 (U0 A B C k).2.2
      = (fun x => A + (k : ℝ)⁻¹ • (x - A)) '' triHull A B C := by
  have hP0 : P A B C k 0 0 = A := by simp [P]
  simpa only [U0, hP0] using Up_eq_homothety A B C k 0 0

/-! ## The packaged statement -/

/-- **Every cell of the `k`-subdivision is a `(±1/k)`-scale homothetic copy of the
whole triangle.** Each upward cell is the image of `A B C` under the ratio `+1/k`
homothety `x ↦ P i j + (1/k)(x − A)`, and each downward cell under the ratio
`−1/k` homothety `x ↦ P (i+1)(j+1) − (1/k)(x − A)`.  Combined with
`Erdos634MedialCongruenceOQ01.card_pieces` (there are exactly `k²` cells) this is
the self-similar "square reptiling": `A B C` is `k²` copies of itself scaled by
`1/k`. -/
theorem reptile_cells_are_homotheties (A B C : V) (k i j : ℕ) :
    triHull (P A B C k i j) (P A B C k (i + 1) j) (P A B C k i (j + 1))
        = (fun x => P A B C k i j + (k : ℝ)⁻¹ • (x - A)) '' triHull A B C ∧
    triHull (P A B C k (i + 1) (j + 1)) (P A B C k i (j + 1)) (P A B C k (i + 1) j)
        = (fun x => P A B C k (i + 1) (j + 1) - (k : ℝ)⁻¹ • (x - A)) '' triHull A B C :=
  ⟨Up_eq_homothety A B C k i j, Down_eq_homothety A B C k i j⟩

end Erdos634MedialHomothetyOQ01
