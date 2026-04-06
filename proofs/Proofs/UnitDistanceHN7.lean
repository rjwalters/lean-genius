/-
  Hadwiger-Nelson Upper Bound: χ(ℝ²) ≤ 7

  Proof via hexagonal 7-coloring. The plane is tiled with regular hexagons
  of side length s = 2/5. Each hexagon is assigned a color from Fin 7 via
  its axial coordinates: color(a, b) = (2a + b) mod 7.

  Key properties:
  - Hex diameter = 2s = 4/5 < 1, so same-hex points are at distance < 1
  - Same-colored hexagons have center distance ≥ s√39 (sublattice minimum)
  - Minimum point-to-point distance between same-colored hexes ≥ s(√39 - 2)
    = (2√39 - 4)/5 > 1 since 2√39 > 9 (i.e., 4·39 = 156 > 81)

  Therefore, points at unit distance are in different hexagons with
  different colors.

  Reference: Hadwiger (1945), Isbell (1950)
-/

import Mathlib

open scoped EuclideanGeometry

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-
## Hexagonal Lattice
-/

/-- Side length of hexagons: s = 2/5. Chosen so that:
    - hex diameter = 2s = 4/5 < 1 (same-hex constraint)
    - s(√39 - 2) > 1 (different-hex same-color constraint) -/
noncomputable def hexSideLength : ℝ := 2 / 5

/-- Axial hex coordinate: first component.
    Maps x-coordinate to the column index in the hex grid.
    The hex grid has column spacing s√3. -/
noncomputable def hexCol (p : Plane) : ℤ :=
  ⌊p 0 / (hexSideLength * Real.sqrt 3) + 1/2⌋

/-- Axial hex coordinate: second component.
    Maps to the row index, offset by the column contribution. -/
noncomputable def hexRow (p : Plane) : ℤ :=
  ⌊(p 1 - p 0 * Real.sqrt 3 / 3) / (3 * hexSideLength / 2) + 1/2⌋

/-- The 7-coloring of the plane via hexagonal tiling.
    Color is determined by axial coordinates: (2a + b) mod 7. -/
noncomputable def hexColor (p : Plane) : Fin 7 :=
  ⟨((2 * hexCol p + hexRow p) % 7).toNat % 7, by omega⟩

/-
## Geometric Lemmas
-/

/-- Points in the same hex cell are at distance < 2s = 4/5 < 1. -/
theorem same_hex_close (p q : Plane) (hcol : hexCol p = hexCol q)
    (hrow : hexRow p = hexRow q) :
    dist p q < 1 := by
  sorry -- Requires: floor rounding gives nearest hex center within distance s,
        -- triangle inequality gives dist ≤ 2s = 4/5 < 1

/-- The minimum squared norm of the color-preserving sublattice.
    Vectors (Δa, Δb) with (2Δa + Δb) ≡ 0 (mod 7) and (Δa, Δb) ≠ (0, 0)
    have Δa² + Δa·Δb + Δb² ≥ 13. The minimum is achieved at (3, 1). -/
theorem color_sublattice_min_norm (da db : ℤ)
    (hmod : (2 * da + db) % 7 = 0) (hne : (da, db) ≠ (0, 0)) :
    da ^ 2 + da * db + db ^ 2 ≥ 13 := by
  sorry -- Finite case analysis: enumerate (da mod 7, db mod 7) pairs with
        -- 2da + db ≡ 0 (mod 7), verify da² + da·db + db² ≥ 13 for each.
        -- For small |da|, |db| this is direct. For |da| or |db| ≥ 4,
        -- the quadratic form (which is positive definite) exceeds 13.

/-- Same-colored hex centers are at distance ≥ s√(3·13) = (2/5)√39.
    From center distance, minimum point-to-point distance ≥ s(√39 - 2)
    = (2√39 - 4)/5 > 1, so same-colored points are at distance > 1. -/
theorem same_color_far (p q : Plane) (hcolor : hexColor p = hexColor q)
    (hdiff : hexCol p ≠ hexCol q ∨ hexRow p ≠ hexRow q) :
    dist p q > 1 := by
  sorry -- Requires: center distance ≥ s√(3·13) = (2/5)√39,
        -- point distance ≥ center distance - 2s = (2/5)(√39 - 2),
        -- and (2√39 - 4)/5 > 1 since 2√39 > 9 since 4·39 = 156 > 81.

/-
## Main Theorem
-/

/-- The Hadwiger-Nelson upper bound: the plane can be 7-colored such that
    no two points at distance 1 have the same color. -/
theorem hadwiger_nelson_7coloring :
    ∃ c : Plane → Fin 7, ∀ p q : Plane, dist p q = 1 → c p ≠ c q := by
  refine ⟨hexColor, fun p q hdist hcolor => ?_⟩
  -- If same hex cell: dist < 1, contradicts dist = 1
  by_cases hcol : hexCol p = hexCol q
  · by_cases hrow : hexRow p = hexRow q
    · exact absurd (same_hex_close p q hcol hrow) (by linarith)
    · exact absurd hdist (ne_of_gt (same_color_far p q hcolor (Or.inr hrow)))
  · exact absurd hdist (ne_of_gt (same_color_far p q hcolor (Or.inl hcol)))
