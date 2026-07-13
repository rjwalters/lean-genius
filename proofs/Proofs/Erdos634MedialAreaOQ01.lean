/-
# Erdős #634 — quantitative area accounting for the `k`-subdivision reptile cells

Erdős problem #634 asks to classify the triples `(T, N)` such that a triangle `T`
can be dissected into `N` mutually congruent pieces ($25 prize; general
classification OPEN). The gallery entry `Erdos634Problem.lean` routes
dissectability through an abstract `axiom Tiles`, and a family of companion files
have built the concrete `k`-subdivision reptiling of an arbitrary triangle:

* `Erdos634MedialCongruenceOQ01` — the `k`-subdivision grid `P i j` and the `k²`
  upward/downward cells, all congruent to the base copy `U0`.
* `Erdos634MedialCoveringOQ02` / `…DisjointOQ02` / `…CentralDisjointOQ02` — the
  four `k = 2` (medial) cells cover the triangle with interior-disjoint pieces.
* `Erdos634MedialHomothetyOQ01` — each cell is the image of the *whole* triangle
  `A B C` under an explicit homothety of ratio `±1/k`
  (`Up_eq_homothety` / `Down_eq_homothety`).

The one qualitative gap flagged by every prior oq-02 session was the **measure /
area accounting**: covering + interior-disjointness is only a *quantitative*
tiling once we know each cell carries the expected fraction `1/k²` of the total
area. This file supplies exactly that, turning `Erdos634MedialHomothetyOQ01`'s
homothety descriptions into Lebesgue-measure statements.

The engine is Mathlib's `MeasureTheory.Measure.addHaar_image_homothety`: a
homothety of ratio `r` on a `d`-dimensional real space scales Haar measure by
`|r|^d`. Composing with translation invariance handles the off-centre cells, and
specialising to the Euclidean plane (`d = 2`) gives the area law

  `area(cell) = (1/k²) · area(triangle)`

for every one of the `k²` cells — upward and downward alike. For `k = 2` this is
the exact `area = ¼ · total` statement for the four medial pieces, the concrete
`n = 4` quantitative content behind `Erdos634MedialTilingOQ02.exists_congruentTiling_four`.

All results are axiom-free (only the ambient `propext / Classical.choice /
Quot.sound`); no `Tiles` axiom and no dimension/area *hypothesis* is used — the
plane's dimension is computed, not assumed.

Tags: geometry, erdos, dissection, tiling, reptile, area, measure, haar, homothety
-/
import Mathlib
import Proofs.Erdos634MedialCoveringOQ02
import Proofs.Erdos634MedialCongruenceOQ01
import Proofs.Erdos634MedialHomothetyOQ01

set_option linter.unusedSectionVars false

open MeasureTheory
open Erdos634MedialCoveringOQ02 Erdos634MedialCongruenceOQ01 Erdos634MedialHomothetyOQ01

namespace Erdos634MedialAreaOQ01

/-! ## Part I: Haar measure of a shifted homothety image (general dimension)

The cells of `Erdos634MedialHomothetyOQ01` are images of the whole triangle under
maps of the form `x ↦ v + r • (x - a)` — a homothety of ratio `r` centred at `a`,
then translated so the fixed point lands at `v`. On a finite-dimensional real
normed space carrying a Haar measure, such a map scales the measure by `|r|^d`. -/

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Shifted-homothety measure law.** The image of `s` under
`x ↦ v + r • (x - a)` has Haar measure `|r|^(dim) · μ s`. The map is
`AffineMap.homothety a r` post-composed with the translation by `v - a`; the
homothety scales by `|r|^dim` (`addHaar_image_homothety`) and translation is
measure-preserving. -/
theorem addHaar_shifted_homothety_image (v a : E) (r : ℝ) (s : Set E) :
    μ ((fun x => v + r • (x - a)) '' s)
      = ENNReal.ofReal |r ^ Module.finrank ℝ E| * μ s := by
  have hmap : (fun x => v + r • (x - a))
      = (fun y => y + (v - a)) ∘ (⇑(AffineMap.homothety a r)) := by
    funext x
    simp only [Function.comp_apply, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
    module
  rw [hmap, Set.image_comp, Set.image_add_right, measure_preimage_add_right,
    Measure.addHaar_image_homothety]

end General

/-! ## Part II: Area of the reptile cells in the Euclidean plane

Specialise to `EuclideanSpace ℝ (Fin 2)`, whose (2-dimensional) volume is the
usual planar area. We compute the area of each cell of the `k`-subdivision. -/

/-- The Euclidean plane, on which `volume` is planar area (2-dim Haar measure). -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Planar-area version of the shifted-homothety law: on the plane the exponent
`dim = 2` is computed, so `x ↦ v + r • (x - a)` scales area by `r²`. -/
theorem area_shifted_homothety_image (v a : Plane) (r : ℝ) (s : Set Plane) :
    volume ((fun x => v + r • (x - a)) '' s) = ENNReal.ofReal (r ^ 2) * volume s := by
  rw [addHaar_shifted_homothety_image,
    show Module.finrank ℝ Plane = 2 from finrank_euclideanSpace_fin,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 2)]

/-- The `−r` (`180°`-rotated) variant, matching `Down_eq_homothety`'s subtraction
form. Since `(−r)² = r²` the reflected cell scales area by the same `r²`. -/
theorem area_neg_shifted_homothety_image (v a : Plane) (r : ℝ) (s : Set Plane) :
    volume ((fun x => v - r • (x - a)) '' s) = ENNReal.ofReal (r ^ 2) * volume s := by
  have hmap : (fun x => v - r • (x - a)) = (fun x => v + (-r) • (x - a)) := by
    funext x; rw [neg_smul, sub_eq_add_neg]
  rw [hmap, area_shifted_homothety_image, show (-r) ^ 2 = r ^ 2 from by ring]

/-! ### Each cell of the `k`-subdivision has area `(1/k²) · (whole triangle)` -/

/-- **Upward cell area.** In the `k`-subdivision of the plane triangle `A B C`,
the upward cell with lower-left grid index `(i, j)` has area exactly
`(1/k)² · area(A B C)`. Immediate from `Up_eq_homothety` (the cell is the
ratio-`1/k` homothety image of the whole) and the planar-area law. -/
theorem area_Up_cell (A B C : Plane) (k i j : ℕ) :
    volume (triHull (P A B C k i j) (P A B C k (i + 1) j) (P A B C k i (j + 1)))
      = ENNReal.ofReal (((k : ℝ)⁻¹) ^ 2) * volume (triHull A B C) := by
  rw [Up_eq_homothety, area_shifted_homothety_image]

/-- **Downward cell area.** The downward cell of the `k`-subdivision (a
`180°`-rotated copy) also has area `(1/k)² · area(A B C)`. -/
theorem area_Down_cell (A B C : Plane) (k i j : ℕ) :
    volume (triHull (P A B C k (i + 1) (j + 1)) (P A B C k i (j + 1)) (P A B C k (i + 1) j))
      = ENNReal.ofReal (((k : ℝ)⁻¹) ^ 2) * volume (triHull A B C) := by
  rw [Down_eq_homothety, area_neg_shifted_homothety_image]

/-- **All cells are equal-area.** Upward and downward cells of the same
`k`-subdivision carry the same area, confirming the congruence-implied
equal-area at the measure level. -/
theorem area_Up_eq_area_Down (A B C : Plane) (k i j i' j' : ℕ) :
    volume (triHull (P A B C k i j) (P A B C k (i + 1) j) (P A B C k i (j + 1)))
      = volume (triHull (P A B C k (i' + 1) (j' + 1)) (P A B C k i' (j' + 1))
          (P A B C k (i' + 1) j')) := by
  rw [area_Up_cell, area_Down_cell]

/-! ### Consistency of the area accounting

The `k`-subdivision has `k²` cells (`k²` upward + `k(k-1)`… — combinatorially
`k²` total), each of area `(1/k²) · A`. The individual areas are therefore
consistent with an exact partition: multiplying the common cell area by the cell
count `k²` recovers the whole area. We record the scalar identity behind this
(for `k ≥ 1`); it is the arithmetic core of "the `k²` congruent cells tile
`A B C`". -/

/-- The `k²` cells, each of area `(1/k²)·A`, account for the full area `A`:
`k² · (1/k)² = 1`. -/
theorem cell_area_count_consistent {k : ℕ} (hk : k ≠ 0) :
    (k : ℝ) ^ 2 * ((k : ℝ)⁻¹) ^ 2 = 1 := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  field_simp

/-! ## Part III: The `k = 2` medial specialisation (`n = 4`)

For `k = 2` the four cells are the three corner pieces (`Up (0,0)`, `Up (1,0)`,
`Up (0,1)`) and the central piece (`Down (0,0)`), matching `medialPieces` of
`Erdos634MedialTilingOQ02`. Each has area exactly `¼` of the whole — the
quantitative content of the concrete `n = 4` tiling. -/

/-- **Medial corner cell = quarter area.** Each upward cell of the `k = 2`
(medial) subdivision has area exactly `¼ · area(A B C)`. The three corner pieces
`Up (0,0)`, `Up (1,0)`, `Up (0,1)` are the `(i,j)` instances. -/
theorem area_medial_Up_cell (A B C : Plane) (i j : ℕ) :
    volume (triHull (P A B C 2 i j) (P A B C 2 (i + 1) j) (P A B C 2 i (j + 1)))
      = ENNReal.ofReal (1 / 4) * volume (triHull A B C) := by
  rw [area_Up_cell, show ((2 : ℕ) : ℝ)⁻¹ ^ 2 = 1 / 4 from by norm_num]

/-- **Medial central cell = quarter area.** The central (downward) cell of the
medial subdivision, `Down (0,0)`, also has area exactly `¼ · area(A B C)`. -/
theorem area_medial_Down_cell (A B C : Plane) (i j : ℕ) :
    volume (triHull (P A B C 2 (i + 1) (j + 1)) (P A B C 2 i (j + 1)) (P A B C 2 (i + 1) j))
      = ENNReal.ofReal (1 / 4) * volume (triHull A B C) := by
  rw [area_Down_cell, show ((2 : ℕ) : ℝ)⁻¹ ^ 2 = 1 / 4 from by norm_num]

end Erdos634MedialAreaOQ01
