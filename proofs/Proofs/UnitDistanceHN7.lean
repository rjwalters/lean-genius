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
    have hda : da ≠ 0 := by rintro rfl; exact hne (by simp_all)
    have : 0 < da ^ 2 := sq_pos_of_ne_zero hda
    set Q' := da ^ 2 - 5 * da * 0 + 7 * 0 ^ 2
    omega
  · have hm2 : m ^ 2 ≥ 1 := by
      have := sq_pos_of_ne_zero hm0; omega
    set Q' := da ^ 2 - 5 * da * m + 7 * m ^ 2
    have : 4 * Q' ≥ 3 := by nlinarith [sq_nonneg (2 * da - 5 * m)]
    omega

-- ============================================================================
-- Part III: Geometric Lemmas
-- ============================================================================

/-- Position in the plane with real axial coordinates `(q, r)`:
    `pos(q,r) = q·e₁ + r·e₂ = (s√3·(q + r/2), 3s/2·r)`.
    Generalizes `hexCenter` to real (non-integer) coordinates. -/
def hexPos (q r : ℝ) : Plane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm
    ![hexSideLength * Real.sqrt 3 * (q + r / 2),
      3 * hexSideLength / 2 * r]

/-- A point equals the `hexPos` of its own axial coordinates: the axial maps
    `axialQ, axialR` invert the basis map `hexPos`. -/
theorem hexPos_axial (p : Plane) : hexPos (axialQ p) (axialR p) = p := by
  have hs : (hexSideLength : ℝ) ≠ 0 :=
    (by norm_num [hexSideLength] : (0 : ℝ) < hexSideLength).ne'
  have h3 : Real.sqrt 3 ≠ 0 := (by positivity : (0 : ℝ) < Real.sqrt 3).ne'
  ext i
  fin_cases i
  · show hexSideLength * Real.sqrt 3 * (axialQ p + axialR p / 2) = p 0
    simp only [axialQ, axialR]
    field_simp
    ring
  · show 3 * hexSideLength / 2 * axialR p = p 1
    simp only [axialR]
    field_simp

/-- Squared distance between two `hexPos` points equals `3s²·Q(Δq, Δr)`
    where `Q(x,y) = x² + xy + y²` is the `A₂` quadratic form. -/
theorem hexPos_dist_sq (q₁ r₁ q₂ r₂ : ℝ) :
    dist (hexPos q₁ r₁) (hexPos q₂ r₂) ^ 2 =
    3 * hexSideLength ^ 2 *
      ((q₁ - q₂) ^ 2 + (q₁ - q₂) * (r₁ - r₂) + (r₁ - r₂) ^ 2) := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp only [hexPos, PiLp.continuousLinearEquiv_symm_apply, PiLp.toLp_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Real.dist_eq, sq_abs]
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 :=
    Real.mul_self_sqrt (by norm_num : (3 : ℝ) ≥ 0)
  nlinarith [h3, sq_nonneg (q₁ - q₂), sq_nonneg (r₁ - r₂),
             sq_nonneg ((q₁ - q₂) + (r₁ - r₂) / 2), sq_nonneg hexSideLength]

/-- Squared distance from a point `p` to the hex center at integer coordinates
    `(a, b)` equals `3s²·Q(axialQ p − a, axialR p − b)`. -/
theorem dist_p_center_sq (p : Plane) (a b : ℤ) :
    dist p (hexCenter a b) ^ 2 = 3 * hexSideLength ^ 2 *
      ((axialQ p - (a : ℝ)) ^ 2 + (axialQ p - (a : ℝ)) * (axialR p - (b : ℝ)) +
       (axialR p - (b : ℝ)) ^ 2) := by
  have hrec : p = hexPos (axialQ p) (axialR p) := (hexPos_axial p).symm
  conv_lhs => rw [hrec]
  rw [show hexCenter a b = hexPos (a : ℝ) (b : ℝ) from rfl, hexPos_dist_sq]

-- From here on, `axialQ`/`axialR` are treated as opaque reals: every downstream
-- defeq (the `hexCoord` unfolding and the Voronoi case analysis) reasons about
-- the rounding purely in axial coordinates, never expanding the EuclideanSpace
-- internals (which would blow up `whnf`). Their equational lemmas remain
-- available to `simp`, so earlier unfoldings are unaffected.
attribute [irreducible] axialQ axialR

/-- Arithmetic core (branch 0): on the hexagon `|a|,|b|,|a+b| ≤ 1/2`, the form
    `a²+ab+b²` is at most `1/3` (actually `≤ 1/4`).  Proof by sign cases with an
    explicit nonnegative-products certificate. -/
theorem quad_bound_A (a b : ℝ) (ha : -1/2 ≤ a) (ha' : a ≤ 1/2)
    (hb : -1/2 ≤ b) (hb' : b ≤ 1/2) (hab : -1/2 ≤ a + b) (hab' : a + b ≤ 1/2) :
    a ^ 2 + a * b + b ^ 2 ≤ 1 / 3 := by
  rcases le_total a 0 with hsa | hsa <;> rcases le_total b 0 with hsb | hsb
  · -- a ≤ 0, b ≤ 0 : same sign, ab ≥ 0, so a²+ab+b² = (a+b)² - (-ab) ≤ (a+b)² ≤ 1/4
    nlinarith [mul_nonneg (neg_nonneg.mpr hsa) (neg_nonneg.mpr hsb),
               mul_nonneg (by linarith : (0:ℝ) ≤ 1/2 - (a + b))
                          (by linarith : (0:ℝ) ≤ 1/2 + (a + b))]
  · -- a ≤ 0, b ≥ 0 : cert  (-a)(1/2+a) + b(1/2-b) + (1/2+a)(1/2-b)
    nlinarith [mul_nonneg (neg_nonneg.mpr hsa) (by linarith : (0:ℝ) ≤ 1/2 + a),
               mul_nonneg hsb (by linarith : (0:ℝ) ≤ 1/2 - b),
               mul_nonneg (by linarith : (0:ℝ) ≤ 1/2 + a) (by linarith : (0:ℝ) ≤ 1/2 - b)]
  · -- a ≥ 0, b ≤ 0 : cert  a(1/2-a) + (-b)(1/2+b) + (1/2-a)(1/2+b)
    nlinarith [mul_nonneg hsa (by linarith : (0:ℝ) ≤ 1/2 - a),
               mul_nonneg (neg_nonneg.mpr hsb) (by linarith : (0:ℝ) ≤ 1/2 + b),
               mul_nonneg (by linarith : (0:ℝ) ≤ 1/2 - a) (by linarith : (0:ℝ) ≤ 1/2 + b)]
  · -- a ≥ 0, b ≥ 0 : same sign, ab ≥ 0
    nlinarith [mul_nonneg hsa hsb,
               mul_nonneg (by linarith : (0:ℝ) ≤ 1/2 - (a + b))
                          (by linarith : (0:ℝ) ≤ 1/2 + (a + b))]

/-- Arithmetic core (correction branches): if `a,b,c ∈ [-1/2,1/2]` with
    `a+b+c = ±1` and `c` has the largest magnitude (`a² ≤ c²`, `b² ≤ c²`), then
    `a²+ab+b² ≤ 1/3`.  Tight: equality at `a=b=c=±1/3`.  Proof uses the identity
    `1/3 − Q = (p+r)(1−p−r)/3 + pr` with `p = 1−2a−b`, `r = 1−a−2b` (sign-flipped
    for the `−1` case). -/
theorem quad_bound_B (a b c : ℝ) (ha : -1/2 ≤ a) (ha' : a ≤ 1/2)
    (hb : -1/2 ≤ b) (hb' : b ≤ 1/2) (hc : -1/2 ≤ c) (hc' : c ≤ 1/2)
    (hsum : a + b + c = 1 ∨ a + b + c = -1)
    (hca : a ^ 2 ≤ c ^ 2) (hcb : b ^ 2 ≤ c ^ 2) :
    a ^ 2 + a * b + b ^ 2 ≤ 1 / 3 := by
  rcases hsum with h | h
  · -- c = 1 - a - b
    have hb1 : (0:ℝ) < 1 - b := by linarith
    have ha1 : (0:ℝ) < 1 - a := by linarith
    have key : (0:ℝ) ≤ (1 - 2*a - b) * (1 - b) := by nlinarith [hca]
    have key2 : (0:ℝ) ≤ (1 - a - 2*b) * (1 - a) := by nlinarith [hcb]
    have hp : (0:ℝ) ≤ 1 - 2*a - b := by nlinarith [key, hb1]
    have hr : (0:ℝ) ≤ 1 - a - 2*b := by nlinarith [key2, ha1]
    have hpr : (0:ℝ) ≤ (1 - 2*a - b) + (1 - a - 2*b) := add_nonneg hp hr
    have hc12 : (0:ℝ) ≤ 3*a + 3*b - 1 := by linarith
    nlinarith [mul_nonneg hp hr, mul_nonneg hpr hc12]
  · -- c = -1 - a - b
    have hb1 : (0:ℝ) < 1 + b := by linarith
    have ha1 : (0:ℝ) < 1 + a := by linarith
    have key : (0:ℝ) ≤ (1 + 2*a + b) * (1 + b) := by nlinarith [hca]
    have key2 : (0:ℝ) ≤ (1 + a + 2*b) * (1 + a) := by nlinarith [hcb]
    have hp : (0:ℝ) ≤ 1 + 2*a + b := by nlinarith [key, hb1]
    have hr : (0:ℝ) ≤ 1 + a + 2*b := by nlinarith [key2, ha1]
    have hpr : (0:ℝ) ≤ (1 + 2*a + b) + (1 + a + 2*b) := add_nonneg hp hr
    have hc12 : (0:ℝ) ≤ -1 - 3*a - 3*b := by linarith
    nlinarith [mul_nonneg hp hr, mul_nonneg hpr hc12]

/-- The cube-coordinate rounding used by `hexCoord`, on abstract axial coordinates.
    The body is identical to `hexCoord`'s, so `hexCoord p = hexRound (axialQ p) (axialR p)`
    holds definitionally.  This lets the covering-radius case analysis run on plain
    reals, never unfolding any EuclideanSpace internals (which would blow up `whnf`). -/
def hexRound (q r : ℝ) : ℤ × ℤ :=
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

set_option maxHeartbeats 800000 in
/-- `hexCoord` is `hexRound` applied to the axial coordinates of `p`. -/
theorem hexCoord_eq_round (p : Plane) :
    hexCoord p = hexRound (axialQ p) (axialR p) := rfl

set_option maxHeartbeats 800000 in
/-- The cube-rounding output keeps the point inside its Voronoi cell:
    `Q(q − a, r − b) ≤ 1/3` where `(a,b) = hexRound q r`.  Tight at the hexagon
    corners (`Q = 1/3`).  This is the covering-radius bound in `A₂` coordinates. -/
theorem hexRound_Q_bound (q r : ℝ) :
    (q - ((hexRound q r).1 : ℝ)) ^ 2 +
      (q - ((hexRound q r).1 : ℝ)) * (r - ((hexRound q r).2 : ℝ)) +
      (r - ((hexRound q r).2 : ℝ)) ^ 2 ≤ 1 / 3 := by
  -- floor bounds: each rounding error lies in [-1/2, 1/2)
  have ha1 : -1/2 ≤ q - (⌊q + 1/2⌋ : ℝ) := by
    have := Int.floor_le (q + 1/2); linarith
  have ha2 : q - (⌊q + 1/2⌋ : ℝ) < 1/2 := by
    have := Int.lt_floor_add_one (q + 1/2); push_cast at this ⊢; linarith
  have hb1 : -1/2 ≤ r - (⌊r + 1/2⌋ : ℝ) := by
    have := Int.floor_le (r + 1/2); linarith
  have hb2 : r - (⌊r + 1/2⌋ : ℝ) < 1/2 := by
    have := Int.lt_floor_add_one (r + 1/2); push_cast at this ⊢; linarith
  have hc1 : -1/2 ≤ (-q - r) - (⌊(-q - r) + 1/2⌋ : ℝ) := by
    have := Int.floor_le ((-q - r) + 1/2); linarith
  have hc2 : (-q - r) - (⌊(-q - r) + 1/2⌋ : ℝ) < 1/2 := by
    have := Int.lt_floor_add_one ((-q - r) + 1/2); push_cast at this ⊢; linarith
  simp only [hexRound]
  set rq := ⌊q + 1/2⌋ with hrqe
  set rr := ⌊r + 1/2⌋ with hrre
  set ry := ⌊(-q - r) + 1/2⌋ with hrye
  -- the integer sum lies in {-1, 0, 1}
  have hSint : rq + rr + ry = -1 ∨ rq + rr + ry = 0 ∨ rq + rr + ry = 1 := by
    have l1 : 2 * (rq + rr + ry) ≤ 3 := by
      have : ((2 * (rq + rr + ry) : ℤ) : ℝ) ≤ 3 := by push_cast; linarith
      exact_mod_cast this
    have l2 : (-3 : ℤ) ≤ 2 * (rq + rr + ry) := by
      have : (-3 : ℝ) ≤ ((2 * (rq + rr + ry) : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    omega
  split_ifs with h0 h1 h2
  · -- Branch 0: rq + ry + rr = 0, output (rq, rr).  Use quad_bound_A.
    show (q - (rq : ℝ)) ^ 2 + (q - (rq : ℝ)) * (r - (rr : ℝ)) + (r - (rr : ℝ)) ^ 2 ≤ 1 / 3
    have hzero : (q - (rq : ℝ)) + (r - (rr : ℝ)) + ((-q - r) - (ry : ℝ)) = 0 := by
      have : ((rq : ℝ) + rr + ry) = 0 := by
        have : (rq + rr + ry : ℤ) = 0 := by omega
        exact_mod_cast this
      linarith
    exact quad_bound_A (q - (rq : ℝ)) (r - (rr : ℝ))
      (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith)
  · -- Branch 1: q-error is largest, output (-ry-rr, rr).  Q = Q(er0, ey0).
    show (q - ((-ry - rr : ℤ) : ℝ)) ^ 2 +
         (q - ((-ry - rr : ℤ) : ℝ)) * (r - (rr : ℝ)) + (r - (rr : ℝ)) ^ 2 ≤ 1 / 3
    have hconv : (q - ((-ry - rr : ℤ) : ℝ)) ^ 2 +
        (q - ((-ry - rr : ℤ) : ℝ)) * (r - (rr : ℝ)) + (r - (rr : ℝ)) ^ 2 =
        (r - (rr : ℝ)) ^ 2 + (r - (rr : ℝ)) * ((-q - r) - (ry : ℝ)) +
          ((-q - r) - (ry : ℝ)) ^ 2 := by push_cast; ring
    rw [hconv]
    have hne0 : rq + rr + ry ≠ 0 := by intro h; exact h0 (by omega)
    have hsum1 : (r - (rr : ℝ)) + ((-q - r) - (ry : ℝ)) + (q - (rq : ℝ)) = 1 ∨
                 (r - (rr : ℝ)) + ((-q - r) - (ry : ℝ)) + (q - (rq : ℝ)) = -1 := by
      rcases hSint with h | h | h
      · left
        have : ((rq : ℝ) + rr + ry) = -1 := by exact_mod_cast (by exact_mod_cast h : (rq + rr + ry : ℤ) = -1)
        linarith
      · exact absurd h hne0
      · right
        have : ((rq : ℝ) + rr + ry) = 1 := by exact_mod_cast (by exact_mod_cast h : (rq + rr + ry : ℤ) = 1)
        linarith
    have hca : (r - (rr : ℝ)) ^ 2 ≤ (q - (rq : ℝ)) ^ 2 := by
      nlinarith [mul_self_le_mul_self (abs_nonneg (r - (rr : ℝ))) h1.1,
                 abs_mul_abs_self (r - (rr : ℝ)), abs_mul_abs_self (q - (rq : ℝ))]
    have hcb : ((-q - r) - (ry : ℝ)) ^ 2 ≤ (q - (rq : ℝ)) ^ 2 := by
      nlinarith [mul_self_le_mul_self (abs_nonneg ((-q - r) - (ry : ℝ))) h1.2,
                 abs_mul_abs_self ((-q - r) - (ry : ℝ)), abs_mul_abs_self (q - (rq : ℝ))]
    exact quad_bound_B (r - (rr : ℝ)) ((-q - r) - (ry : ℝ)) (q - (rq : ℝ))
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
      hsum1 hca hcb
  · -- Branch 2: r-error is largest, output (rq, -rq-ry).  Q = Q(eq0, ey0).
    show (q - (rq : ℝ)) ^ 2 +
         (q - (rq : ℝ)) * (r - ((-rq - ry : ℤ) : ℝ)) + (r - ((-rq - ry : ℤ) : ℝ)) ^ 2 ≤ 1 / 3
    have hconv : (q - (rq : ℝ)) ^ 2 +
        (q - (rq : ℝ)) * (r - ((-rq - ry : ℤ) : ℝ)) + (r - ((-rq - ry : ℤ) : ℝ)) ^ 2 =
        (q - (rq : ℝ)) ^ 2 + (q - (rq : ℝ)) * ((-q - r) - (ry : ℝ)) +
          ((-q - r) - (ry : ℝ)) ^ 2 := by push_cast; ring
    rw [hconv]
    have hne0 : rq + rr + ry ≠ 0 := by intro h; exact h0 (by omega)
    have hsum1 : (q - (rq : ℝ)) + ((-q - r) - (ry : ℝ)) + (r - (rr : ℝ)) = 1 ∨
                 (q - (rq : ℝ)) + ((-q - r) - (ry : ℝ)) + (r - (rr : ℝ)) = -1 := by
      rcases hSint with h | h | h
      · left
        have : ((rq : ℝ) + rr + ry) = -1 := by exact_mod_cast (by exact_mod_cast h : (rq + rr + ry : ℤ) = -1)
        linarith
      · exact absurd h hne0
      · right
        have : ((rq : ℝ) + rr + ry) = 1 := by exact_mod_cast (by exact_mod_cast h : (rq + rr + ry : ℤ) = 1)
        linarith
    have hle : |q - (rq : ℝ)| ≤ |r - (rr : ℝ)| := by
      rcases not_and_or.mp h1 with h | h
      · exact le_of_lt (not_le.mp h)
      · exact le_of_lt (lt_of_lt_of_le (not_le.mp h) h2)
    have hca : (q - (rq : ℝ)) ^ 2 ≤ (r - (rr : ℝ)) ^ 2 := by
      nlinarith [mul_self_le_mul_self (abs_nonneg (q - (rq : ℝ))) hle,
                 abs_mul_abs_self (q - (rq : ℝ)), abs_mul_abs_self (r - (rr : ℝ))]
    have hcb : ((-q - r) - (ry : ℝ)) ^ 2 ≤ (r - (rr : ℝ)) ^ 2 := by
      nlinarith [mul_self_le_mul_self (abs_nonneg ((-q - r) - (ry : ℝ))) h2,
                 abs_mul_abs_self ((-q - r) - (ry : ℝ)), abs_mul_abs_self (r - (rr : ℝ))]
    exact quad_bound_B (q - (rq : ℝ)) ((-q - r) - (ry : ℝ)) (r - (rr : ℝ))
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
      hsum1 hca hcb
  · -- Branch 3: y-error is largest, output (rq, rr).  Q = Q(eq0, er0).
    show (q - (rq : ℝ)) ^ 2 + (q - (rq : ℝ)) * (r - (rr : ℝ)) + (r - (rr : ℝ)) ^ 2 ≤ 1 / 3
    have hne0 : rq + rr + ry ≠ 0 := by intro h; exact h0 (by omega)
    have hsum1 : (q - (rq : ℝ)) + (r - (rr : ℝ)) + ((-q - r) - (ry : ℝ)) = 1 ∨
                 (q - (rq : ℝ)) + (r - (rr : ℝ)) + ((-q - r) - (ry : ℝ)) = -1 := by
      rcases hSint with h | h | h
      · left
        have : ((rq : ℝ) + rr + ry) = -1 := by exact_mod_cast (by exact_mod_cast h : (rq + rr + ry : ℤ) = -1)
        linarith
      · exact absurd h hne0
      · right
        have : ((rq : ℝ) + rr + ry) = 1 := by exact_mod_cast (by exact_mod_cast h : (rq + rr + ry : ℤ) = 1)
        linarith
    have hlt2 : |r - (rr : ℝ)| < |(-q - r) - (ry : ℝ)| := not_le.mp h2
    have hle : |q - (rq : ℝ)| ≤ |(-q - r) - (ry : ℝ)| := by
      rcases not_and_or.mp h1 with h | h
      · exact le_of_lt (lt_trans (not_le.mp h) hlt2)
      · exact le_of_lt (not_le.mp h)
    have hca : (q - (rq : ℝ)) ^ 2 ≤ ((-q - r) - (ry : ℝ)) ^ 2 := by
      nlinarith [mul_self_le_mul_self (abs_nonneg (q - (rq : ℝ))) hle,
                 abs_mul_abs_self (q - (rq : ℝ)), abs_mul_abs_self ((-q - r) - (ry : ℝ))]
    have hcb : (r - (rr : ℝ)) ^ 2 ≤ ((-q - r) - (ry : ℝ)) ^ 2 := by
      nlinarith [mul_self_le_mul_self (abs_nonneg (r - (rr : ℝ))) (le_of_lt hlt2),
                 abs_mul_abs_self (r - (rr : ℝ)), abs_mul_abs_self ((-q - r) - (ry : ℝ))]
    exact quad_bound_B (q - (rq : ℝ)) (r - (rr : ℝ)) ((-q - r) - (ry : ℝ))
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
      hsum1 hca hcb

/-- The cube-rounding output `hexCoord p` keeps the point inside the Voronoi cell:
    `Q(axialQ p − a, axialR p − b) ≤ 1/3`. -/
theorem hexCoord_Q_bound (p : Plane) :
    (axialQ p - ((hexCoord p).1 : ℝ)) ^ 2 +
      (axialQ p - ((hexCoord p).1 : ℝ)) * (axialR p - ((hexCoord p).2 : ℝ)) +
      (axialR p - ((hexCoord p).2 : ℝ)) ^ 2 ≤ 1 / 3 := by
  rw [hexCoord_eq_round]
  exact hexRound_Q_bound (axialQ p) (axialR p)

/-- Covering radius of the A₂ lattice with Voronoi rounding.
    Every point is within distance s of its hexCoord center.
    This is the circumradius of the hexagonal Voronoi cell. -/
theorem covering_radius (p : Plane) :
    dist p (hexCenter (hexCoord p).1 (hexCoord p).2) ≤ hexSideLength := by
  have hs : (0 : ℝ) ≤ hexSideLength := by norm_num [hexSideLength]
  have hd : (0 : ℝ) ≤ dist p (hexCenter (hexCoord p).1 (hexCoord p).2) := dist_nonneg
  have hQ := hexCoord_Q_bound p
  have hsq : dist p (hexCenter (hexCoord p).1 (hexCoord p).2) ^ 2 ≤ hexSideLength ^ 2 := by
    rw [dist_p_center_sq]
    nlinarith [hQ, sq_nonneg hexSideLength]
  nlinarith [hsq, hd, hs]

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
  have h : (9 : ℝ) / 2 = Real.sqrt ((9 / 2) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
  rw [gt_iff_lt, h]
  exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)

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
    have hs_pos : (0 : ℝ) < hexSideLength := by norm_num [hexSideLength]
    have hlhs : (0 : ℝ) ≤ hexSideLength * Real.sqrt 21 := by positivity
    have hsq21 : (hexSideLength * Real.sqrt 21) ^ 2 = 21 * hexSideLength ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 21)]; ring
    nlinarith [hcenter_sq, hsq21, hlhs,
               dist_nonneg (x := hexCenter a₁ b₁) (y := hexCenter a₂ b₂)]
  -- Step 6: Triangle inequality → point distance ≥ center distance - 2s
  have hp := covering_radius p
  have hq := covering_radius q
  have h_tri : dist (hexCenter a₁ b₁) (hexCenter a₂ b₂) ≤
      dist (hexCenter a₁ b₁) p + dist p q + dist q (hexCenter a₂ b₂) := by
    have t1 := dist_triangle (hexCenter a₁ b₁) p (hexCenter a₂ b₂)
    have t2 := dist_triangle p q (hexCenter a₂ b₂)
    linarith
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
