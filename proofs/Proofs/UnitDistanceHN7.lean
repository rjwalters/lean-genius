/-
  Hadwiger-Nelson Upper Bound: χ(ℝ²) ≤ 7

  Proof via hexagonal 7-coloring. The plane is tiled with regular hexagons
  of side length s = 2/5. Each hexagon is assigned a color from Fin 7 via
  its axial coordinates: color(a, b) = (3a + b) mod 7.

  Key properties:
  - Hex diameter = 2s = 4/5 < 1, so same-hex points are at distance < 1
  - Same-colored hexagons have center distance ≥ s√21 (sublattice minimum Q=7)
  - Minimum point-to-point distance between same-colored hexes ≥ s(√21 - 2)
    = (2√21 - 4)/5 > 1 since (2√21-4)² = 100-16√21 > 25 (as 5625 > 5376)

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
    Color is determined by axial coordinates: (3a + b) mod 7.
    NOTE: The original formula (2a + b) mod 7 is WRONG — it has a color-preserving
    translation (1,-2) with Q = da²+da·db+db² = 3, giving same-colored hex centers
    at distance only 6/5, so same-colored points can be as close as 2/5 < 1.
    With (3a + b) mod 7, the minimum color-preserving Q is 7 (at (2,1)),
    giving center distance (2/5)√21 ≈ 1.83 and point distance ≥ 1.03 > 1. -/
noncomputable def hexColor (p : Plane) : Fin 7 :=
  ⟨((3 * hexCol p + hexRow p) % 7).toNat % 7, by omega⟩

/-
## Geometric Lemmas
-/

/-- Points in the same hex cell are at distance < 2s = 4/5 < 1.

    BUG (identified 2026-04-06): This theorem is FALSE with the current hexCol/hexRow
    definitions. Independent floor rounding of oblique coordinates produces PARALLELOGRAM
    cells (not hexagonal Voronoi cells). The parallelogram diagonal is √37·s/2 ≈ 1.22 > 1.
    Counterexample: p = (0.3, 0.453), q = (-0.3, -0.453), both in cell (0,0), dist ≈ 1.09.

    Fix needed: replace independent rounding with Voronoi rounding (nearest lattice center).
    The Voronoi cell circumradius is √(13/3)/5 ≈ 0.42, giving diameter ≈ 0.83 < 1. -/
theorem same_hex_close (p q : Plane) (hcol : hexCol p = hexCol q)
    (hrow : hexRow p = hexRow q) :
    dist p q < 1 := by
  sorry -- BLOCKED: theorem is false with current definitions (see docstring)

/-- The minimum squared norm of the color-preserving sublattice.
    Vectors (Δa, Δb) with (3Δa + Δb) ≡ 0 (mod 7) and (Δa, Δb) ≠ (0, 0)
    have Δa² + Δa·Δb + Δb² ≥ 7. The minimum is achieved at (2, 1) and (-1, 3).
    NOTE: Previous formula (2Δa + Δb) was wrong — it had Q=3 at (1,-2). -/
theorem color_sublattice_min_norm (da db : ℤ)
    (hmod : (3 * da + db) % 7 = 0) (hne : (da, db) ≠ (0, 0)) :
    da ^ 2 + da * db + db ^ 2 ≥ 7 := by
  -- From 3da + db ≡ 0 (mod 7): extract db = -3da + 7m
  obtain ⟨m, hm⟩ : ∃ m : ℤ, db = -3 * da + 7 * m := ⟨(3 * da + db) / 7, by omega⟩
  -- Substitute: Q(da,db) = 7·(da² - 5·da·m + 7·m²)
  have hQ : da ^ 2 + da * db + db ^ 2 = 7 * (da ^ 2 - 5 * da * m + 7 * m ^ 2) := by
    subst hm; ring
  rw [hQ]
  -- Suffices: da² - 5·da·m + 7·m² ≥ 1
  suffices h : da ^ 2 - 5 * da * m + 7 * m ^ 2 ≥ 1 by linarith
  -- Key identity: 4·(da² - 5dam + 7m²) = (2da - 5m)² + 3m²  (positive definite)
  have h4 : 4 * (da ^ 2 - 5 * da * m + 7 * m ^ 2) = (2 * da - 5 * m) ^ 2 + 3 * m ^ 2 := by ring
  by_cases hm0 : m = 0
  · -- m = 0: inner form = da², and da ≠ 0 (else (da,db) = (0,0))
    subst hm0
    have hda : da ≠ 0 := by intro h; apply hne; constructor <;> simp_all
    have : 0 < da ^ 2 := sq_pos_of_ne_zero da hda
    set Q' := da ^ 2 - 5 * da * 0 + 7 * 0 ^ 2
    omega
  · -- m ≠ 0: m² ≥ 1, so 4·(inner form) ≥ 3, hence inner form ≥ 1 (integer)
    have hm2 : m ^ 2 ≥ 1 := by
      have := sq_pos_of_ne_zero m hm0; omega
    set Q' := da ^ 2 - 5 * da * m + 7 * m ^ 2
    have : 4 * Q' ≥ 3 := by nlinarith [sq_nonneg (2 * da - 5 * m)]
    omega

/-- Same-colored hex centers are at distance ≥ s√(3·7) = (2/5)√21.
    From center distance, minimum point-to-point distance ≥ s(√21 - 2)
    = (2√21 - 4)/5 > 1, so same-colored points are at distance > 1.
    Verification: (2√21 - 4)² = 4·21 - 16√21 + 16 = 100 - 16√21.
    Need 100 - 16√21 > 25, i.e., 75 > 16√21, i.e., 5625 > 5376. ✓ -/
theorem same_color_far (p q : Plane) (hcolor : hexColor p = hexColor q)
    (hdiff : hexCol p ≠ hexCol q ∨ hexRow p ≠ hexRow q) :
    dist p q > 1 := by
  sorry -- Requires: center distance ≥ s√(3·7) = (2/5)√21 by color_sublattice_min_norm,
        -- point distance ≥ center distance - 2s = (2/5)(√21 - 2),
        -- and (2√21 - 4)/5 > 1 since 5625 > 5376 = 256·21.

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
