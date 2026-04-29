/-
  Hadwiger-Nelson Upper Bound: χ(ℝ²) ≤ 7

  Proof via hexagonal 7-coloring of the plane.

  The A₂ lattice with basis e₁ = (s√3, 0), e₂ = (s√3/2, 3s/2), s = 2/5,
  has hexagonal Voronoi cells of circumradius s = 2/5.
  Each cell is colored by (3q + r) mod 7 where (q, r) are lattice coordinates.

  Key properties:
  1. Covering radius = s: every point is within distance s of its Voronoi center.
  2. Same-colored centers have squared distance ≥ 3s²·7 = 21s²
     (color-sublattice minimum norm Q = 7 for formula (3q+r) mod 7).
  3. Point distance ≥ s√21 - 2s = s(√21 - 2) = (2√21 - 4)/5 > 1 since 84 > 81.

  References: Hadwiger (1945), Isbell (1950)
-/

import Mathlib

open scoped EuclideanGeometry

abbrev Plane := EuclideanSpace ℝ (Fin 2)

noncomputable section

-- ============================================================================
-- Part I: Lattice Definitions
-- ============================================================================

/-- Side length of hexagons: s = 2/5. -/
def hexSideLength : ℝ := 2 / 5

/-- Real-valued axial q-coordinate in the A₂ lattice basis.
    Basis: e₁ = (s√3, 0), e₂ = (s√3/2, 3s/2). Inverse gives:
      r = 2y/(3s),  q = x/(s√3) - y/(3s). -/
def axialQ (p : Plane) : ℝ :=
  p 0 / (hexSideLength * Real.sqrt 3) - p 1 / (3 * hexSideLength)

/-- Real-valued axial r-coordinate: r = 2y/(3s). -/
def axialR (p : Plane) : ℝ :=
  2 * p 1 / (3 * hexSideLength)

/-- Hex Voronoi rounding via cube coordinates.
    Cube coords: (x, y, z) = (q, -q-r, r) with x+y+z = 0.
    Round each independently; fix the coordinate with largest
    rounding error if they don't sum to 0. Returns axial (q, r). -/
def hexCoord (p : Plane) : ℤ × ℤ :=
  let q := axialQ p
  let r := axialR p
  let y := -q - r
  let rq := ⌊q + 1/2⌋
  let rr := ⌊r + 1/2⌋
  let ry := ⌊y + 1/2⌋
  if rq + ry + rr = 0 then (rq, rr)
  else
    let dq := |q - ↑rq|
    let dr := |r - ↑rr|
    let dy := |y - ↑ry|
    if dq ≥ dr ∧ dq ≥ dy then (-ry - rr, rr)
    else if dr ≥ dy then (rq, -rq - ry)
    else (rq, rr)

/-- The 7-coloring of the plane: color = (3q + r) mod 7. -/
def hexColor (p : Plane) : Fin 7 :=
  let (q, r) := hexCoord p
  ⟨((3 * q + r) % 7).toNat % 7, by omega⟩

/-- Center of the hex cell at lattice coordinates (a, b).
    center(a, b) = a·e₁ + b·e₂ = (s√3·(a + b/2), 3sb/2). -/
def hexCenter (a b : ℤ) : Plane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm
    ![hexSideLength * Real.sqrt 3 * ((a : ℝ) + (b : ℝ) / 2),
      3 * hexSideLength / 2 * (b : ℝ)]

-- ============================================================================
-- Part II: Color Sublattice Minimum Norm (PROVED)
-- ============================================================================

/-- For the color sublattice {(Δq,Δr) : 3Δq+Δr ≡ 0 mod 7},
    the minimum nonzero quadratic form value is Q = 7.
    Proof: Write db = -3da + 7m. Then Q = 7·(da² - 5da·m + 7m²).
    The inner form is positive-definite: 4·(inner) = (2da-5m)² + 3m² ≥ 1. -/
theorem color_sublattice_min_norm (da db : ℤ)
    (hmod : (3 * da + db) % 7 = 0) (hne : (da, db) ≠ (0, 0)) :
    da ^ 2 + da * db + db ^ 2 ≥ 7 := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, db = -3 * da + 7 * m := ⟨(3 * da + db) / 7, by omega⟩
  have hQ : da ^ 2 + da * db + db ^ 2 = 7 * (da ^ 2 - 5 * da * m + 7 * m ^ 2) := by
    subst hm; ring
  rw [hQ]
  suffices h : da ^ 2 - 5 * da * m + 7 * m ^ 2 ≥ 1 by linarith
  have h4 : 4 * (da ^ 2 - 5 * da * m + 7 * m ^ 2) =
      (2 * da - 5 * m) ^ 2 + 3 * m ^ 2 := by ring
  by_cases hm0 : m = 0
  · subst hm0
    have hda : da ≠ 0 := by intro h; apply hne; constructor <;> simp_all
    have : 0 < da ^ 2 := sq_pos_of_ne_zero da hda
    set Q' := da ^ 2 - 5 * da * 0 + 7 * 0 ^ 2
    omega
  · have hm2 : m ^ 2 ≥ 1 := by
      have := sq_pos_of_ne_zero m hm0; omega
    set Q' := da ^ 2 - 5 * da * m + 7 * m ^ 2
    have : 4 * Q' ≥ 3 := by nlinarith [sq_nonneg (2 * da - 5 * m)]
    omega

-- ============================================================================
-- Part III: Geometric Lemmas
-- ============================================================================

/-- Covering radius of the A₂ lattice with Voronoi rounding.
    Every point is within distance s of its hexCoord center.
    This is the circumradius of the hexagonal Voronoi cell. -/
theorem covering_radius (p : Plane) :
    dist p (hexCenter (hexCoord p).1 (hexCoord p).2) ≤ hexSideLength := by
  sorry
  -- The A₂ Voronoi cell is a regular hexagon with circumradius equal to the
  -- lattice shortest vector / √3 = s√3/√3 = s. The cube-coordinate rounding
  -- algorithm assigns each point to the nearest lattice center.

/-- Squared distance between hex centers equals 3s²·Q(Δa, Δb).
    ‖center(a₁,b₁) - center(a₂,b₂)‖² = 3s²·(Δa² + Δa·Δb + Δb²).
    Expand: Δx = s√3·(Δa + Δb/2), Δy = 3s/2·Δb. -/
theorem hexCenter_dist_sq (a₁ b₁ a₂ b₂ : ℤ) :
    dist (hexCenter a₁ b₁) (hexCenter a₂ b₂) ^ 2 =
    3 * hexSideLength ^ 2 *
      (((a₁ : ℝ) - a₂) ^ 2 + ((a₁ : ℝ) - a₂) * ((b₁ : ℝ) - b₂) +
       ((b₁ : ℝ) - b₂) ^ 2) := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp only [hexCenter, PiLp.continuousLinearEquiv_symm_apply, PiLp.toLp_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Real.dist_eq, sq_abs]
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 :=
    Real.mul_self_sqrt (by norm_num : (3:ℝ) ≥ 0)
  nlinarith [h3, sq_nonneg ((a₁ : ℝ) - a₂), sq_nonneg ((b₁ : ℝ) - b₂),
             sq_nonneg (((a₁ : ℝ) - a₂) + ((b₁ : ℝ) - b₂) / 2),
             sq_nonneg hexSideLength]

/-- √21 > 9/2. Proof: 21 > (9/2)² = 20.25, and √ is monotone. -/
theorem sqrt21_gt_nine_halves : Real.sqrt 21 > 9 / 2 := by
  calc Real.sqrt 21 > Real.sqrt (81/4) := by
        apply Real.sqrt_lt_sqrt (by positivity) (by norm_num) |>.mpr
        exact by norm_num
    _ = 9 / 2 := by
        rw [show (81:ℝ)/4 = (9/2)^2 from by norm_num,
            Real.sqrt_sq (by norm_num : (9:ℝ)/2 ≥ 0)]

/-- The key numerical bound: s(√21 - 2) > 1, where s = 2/5.
    Equivalently, 2√21 - 4 > 5, i.e., √21 > 9/2, i.e., 21 > 20.25. -/
theorem side_length_gap_bound : hexSideLength * (Real.sqrt 21 - 2) > 1 := by
  have h := sqrt21_gt_nine_halves
  simp only [hexSideLength]
  linarith

-- ============================================================================
-- Part IV: Core Distance Bounds
-- ============================================================================

/-- Points assigned to the same hex cell are at distance < 1.
    By triangle inequality: dist ≤ 2·(covering radius) = 2s = 4/5 < 1. -/
theorem same_hex_close (p q : Plane)
    (hsame : hexCoord p = hexCoord q) :
    dist p q < 1 := by
  have hp := covering_radius p
  have hq := covering_radius q
  have hsame1 : (hexCoord p).1 = (hexCoord q).1 := congr_arg Prod.fst hsame
  have hsame2 : (hexCoord p).2 = (hexCoord q).2 := congr_arg Prod.snd hsame
  calc dist p q
      ≤ dist p (hexCenter (hexCoord p).1 (hexCoord p).2) +
        dist (hexCenter (hexCoord p).1 (hexCoord p).2) q := dist_triangle _ _ _
    _ ≤ hexSideLength + hexSideLength := by
        have : dist (hexCenter (hexCoord p).1 (hexCoord p).2) q =
               dist q (hexCenter (hexCoord p).1 (hexCoord p).2) := dist_comm _ _
        linarith [show dist q (hexCenter (hexCoord p).1 (hexCoord p).2) ≤ hexSideLength by
          rw [hsame1, hsame2]; exact hq]
    _ = 4 / 5 := by simp [hexSideLength]; ring
    _ < 1 := by norm_num

/-- Same-colored points in different hex cells are at distance > 1.
    Center distance ≥ s√21, point distance ≥ s√21 - 2s = s(√21-2) > 1. -/
theorem same_color_far (p q : Plane)
    (hcolor : hexColor p = hexColor q)
    (hdiff : hexCoord p ≠ hexCoord q) :
    dist p q > 1 := by
  set a₁ := (hexCoord p).1
  set b₁ := (hexCoord p).2
  set a₂ := (hexCoord q).1
  set b₂ := (hexCoord q).2
  -- Step 1: Same color → sublattice condition (3Δa + Δb ≡ 0 mod 7)
  have hmod : (3 * (a₁ - a₂) + (b₁ - b₂)) % 7 = 0 := by
    -- hexColor equality means (3a₁+b₁) mod 7 = (3a₂+b₂) mod 7
    simp only [hexColor, Fin.mk.injEq] at hcolor
    have h₁_pos : 0 ≤ (3 * a₁ + b₁) % 7 := Int.emod_nonneg _ (by norm_num)
    have h₂_pos : 0 ≤ (3 * a₂ + b₂) % 7 := Int.emod_nonneg _ (by norm_num)
    have h₁_lt : (3 * a₁ + b₁) % 7 < 7 := Int.emod_lt_of_pos _ (by norm_num)
    have h₂_lt : (3 * a₂ + b₂) % 7 < 7 := Int.emod_lt_of_pos _ (by norm_num)
    omega
  -- Step 2: Different cells → (Δa, Δb) ≠ (0, 0)
  have hne : (a₁ - a₂, b₁ - b₂) ≠ (0, 0) := by
    intro h
    apply hdiff
    have h1 := congr_arg Prod.fst h
    have h2 := congr_arg Prod.snd h
    simp at h1 h2
    exact Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2)
  -- Step 3: Q(Δa, Δb) ≥ 7
  have hQ := color_sublattice_min_norm (a₁ - a₂) (b₁ - b₂) hmod hne
  -- Step 4: Center distance² ≥ 21s²
  have hcenter_sq : dist (hexCenter a₁ b₁) (hexCenter a₂ b₂) ^ 2 ≥
      21 * hexSideLength ^ 2 := by
    calc dist (hexCenter a₁ b₁) (hexCenter a₂ b₂) ^ 2
        = 3 * hexSideLength ^ 2 *
          (((a₁ : ℝ) - a₂) ^ 2 + ((a₁ : ℝ) - a₂) * ((b₁ : ℝ) - b₂) +
           ((b₁ : ℝ) - b₂) ^ 2) := hexCenter_dist_sq a₁ b₁ a₂ b₂
      _ ≥ 3 * hexSideLength ^ 2 * 7 := by
          have : ((a₁ : ℝ) - a₂) ^ 2 + ((a₁ : ℝ) - a₂) * ((b₁ : ℝ) - b₂) +
                 ((b₁ : ℝ) - b₂) ^ 2 ≥ 7 := by exact_mod_cast hQ
          nlinarith [sq_nonneg hexSideLength]
      _ = 21 * hexSideLength ^ 2 := by ring
  -- Step 5: Center distance ≥ s√21
  have hcenter : dist (hexCenter a₁ b₁) (hexCenter a₂ b₂) ≥
      hexSideLength * Real.sqrt 21 := by
    have hs_pos : hexSideLength > 0 := by simp [hexSideLength]; norm_num
    rw [← Real.sqrt_sq (le_of_lt hs_pos)]
    rw [← Real.sqrt_mul (sq_nonneg _)]
    apply Real.sqrt_le_sqrt
    calc hexSideLength ^ 2 * 21 = 21 * hexSideLength ^ 2 := by ring
      _ ≤ dist (hexCenter a₁ b₁) (hexCenter a₂ b₂) ^ 2 := hcenter_sq
  -- Step 6: Triangle inequality → point distance ≥ center distance - 2s
  have hp := covering_radius p
  have hq := covering_radius q
  have h_tri : dist (hexCenter a₁ b₁) (hexCenter a₂ b₂) ≤
      dist (hexCenter a₁ b₁) p + dist p q + dist q (hexCenter a₂ b₂) := by
    calc dist (hexCenter a₁ b₁) (hexCenter a₂ b₂)
        ≤ dist (hexCenter a₁ b₁) p + dist p (hexCenter a₂ b₂) :=
          dist_triangle _ _ _
      _ ≤ dist (hexCenter a₁ b₁) p + (dist p q + dist q (hexCenter a₂ b₂)) := by
          linarith [dist_triangle p q (hexCenter a₂ b₂)]
  have h_rearr : dist p q ≥
      dist (hexCenter a₁ b₁) (hexCenter a₂ b₂) -
      dist p (hexCenter a₁ b₁) - dist q (hexCenter a₂ b₂) := by
    have := dist_comm (hexCenter a₁ b₁) p
    linarith
  -- Step 7: Combine
  calc dist p q
      ≥ dist (hexCenter a₁ b₁) (hexCenter a₂ b₂) -
        dist p (hexCenter a₁ b₁) - dist q (hexCenter a₂ b₂) := h_rearr
    _ ≥ hexSideLength * Real.sqrt 21 - hexSideLength - hexSideLength := by
        linarith [dist_comm p (hexCenter a₁ b₁), dist_comm q (hexCenter a₂ b₂)]
    _ = hexSideLength * (Real.sqrt 21 - 2) := by ring
    _ > 1 := side_length_gap_bound

-- ============================================================================
-- Part V: Main Theorem
-- ============================================================================

/-- **Hadwiger-Nelson Upper Bound**: The plane can be 7-colored such that
    no two points at unit distance share a color. -/
theorem hadwiger_nelson_7coloring :
    ∃ c : Plane → Fin 7, ∀ p q : Plane, dist p q = 1 → c p ≠ c q := by
  refine ⟨hexColor, fun p q hdist hcolor => ?_⟩
  by_cases hsame : hexCoord p = hexCoord q
  · -- Same cell: dist < 4/5 < 1, contradicts dist = 1
    linarith [same_hex_close p q hsame]
  · -- Different cells, same color: dist > 1, contradicts dist = 1
    linarith [same_color_far p q hcolor hsame]

end

/-
  ## Summary

  Theorems proved:
  - color_sublattice_min_norm: Q(Δa,Δb) ≥ 7 on color sublattice (FULLY PROVED)
  - sqrt21_gt_nine_halves: √21 > 9/2 (FULLY PROVED)
  - side_length_gap_bound: s(√21 - 2) > 1 (FULLY PROVED)
  - hexCenter_dist_sq: ‖center(a₁,b₁) - center(a₂,b₂)‖² = 3s²·Q(Δa,Δb) (FULLY PROVED)
  - same_hex_close: same cell → dist < 1 (proved FROM covering_radius)
  - same_color_far: same color, different cell → dist > 1 (proved FROM covering_radius, hexCenter_dist_sq)
  - hadwiger_nelson_7coloring: main theorem (proved FROM same_hex_close, same_color_far)

  Remaining sorries: 1
  1. covering_radius — A₂ Voronoi cell circumradius ≤ s (geometric)
     The cube-coordinate rounding algorithm assigns each point to the nearest
     lattice center. This is the only remaining geometric obligation.
-/

#check hadwiger_nelson_7coloring
