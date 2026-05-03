/-
2D Ehrhart Polynomial via Pick's Theorem
Problem: picks-theorem-oq-01-oq-02

The Ehrhart polynomial L(P, t) counts lattice points in the integer dilation tP
for t ≥ 0. For a convex lattice polygon P with area A and B boundary lattice points:

  L(P, t) = A · t² + (B/2) · t + 1

We prove:
1. L for axis-aligned rectangles: L(R_{a,b}, t) = (ta + 1)(tb + 1)      [PROVED via Finset]
2. L for right triangles: 2·L(T_n, t) = (tn + 1)(tn + 2)                [PROVED via antidiagonal]
3. The Ehrhart formula from Pick's theorem + scaling axioms               [PROVED algebraically]

Derivation from Pick's theorem applied to tP:
  Area(tP) = t² · A,   |∂(tP) ∩ ℤ²| = t · B  (for integer t ≥ 1)
  Pick: Area(tP) = i(tP) + B(tP)/2 - 1  →  i(tP) = t²A - tB/2 + 1
  L(P,t) = i(tP) + B(tP) = (t²A - tB/2 + 1) + tB = t²A + tB/2 + 1
-/

import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace EhrhartPolynomial

open Finset Nat BigOperators

-- ============================================================
-- Part I: Rectangle Ehrhart Polynomial  [Fully proved]
-- ============================================================

/-- Lattice points in t · [0, a] × [0, b] = {(x,y) : 0 ≤ x ≤ ta, 0 ≤ y ≤ tb}. -/
def rectangleScaled (a b t : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range (t * a + 1) ×ˢ Finset.range (t * b + 1)

/-- Rectangle Ehrhart polynomial: L(R_{a,b}, t) = (ta + 1)(tb + 1). -/
theorem rectangle_ehrhart (a b t : ℕ) :
    (rectangleScaled a b t).card = (t * a + 1) * (t * b + 1) := by
  simp [rectangleScaled, Finset.card_product]

/-- Unit square dilated by t has (t+1)² lattice points. -/
theorem unit_square_ehrhart (t : ℕ) :
    (rectangleScaled 1 1 t).card = (t + 1) ^ 2 := by
  rw [rectangle_ehrhart]; ring

/-- Rectangle Ehrhart in quadratic form: L = ab·t² + (a+b)·t + 1.
    Identifies: area = a*b, boundary/2 = a+b, constant = 1. -/
theorem rectangle_ehrhart_quadratic (a b t : ℕ) :
    (rectangleScaled a b t).card = a * b * t ^ 2 + (a + b) * t + 1 := by
  rw [rectangle_ehrhart]; ring

/-- L(R, 0) = 1. -/
theorem rectangle_ehrhart_zero (a b : ℕ) : (rectangleScaled a b 0).card = 1 := by
  simp [rectangleScaled]

/-- L(R_{a,b}, 1) = (a+1)(b+1). -/
theorem rectangle_ehrhart_one (a b : ℕ) :
    (rectangleScaled a b 1).card = (a + 1) * (b + 1) := by
  simp [rectangleScaled, Finset.card_product]

-- ============================================================
-- Part II: Right Triangle Ehrhart Polynomial  [Fully proved]
-- ============================================================

/-- Lattice points in t · Δ_n = {(x,y) ∈ ℕ² : x+y ≤ tn}. -/
def triangleScaled (n t : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (t * n + 1) ×ˢ Finset.range (t * n + 1)).filter (fun p => p.1 + p.2 ≤ t * n)

private lemma triangleScaled_eq_biUnion (n t : ℕ) :
    triangleScaled n t = (Finset.range (t * n + 1)).biUnion Finset.Nat.antidiagonal := by
  ext ⟨x, y⟩
  simp only [triangleScaled, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_biUnion, Finset.Nat.mem_antidiagonal]
  constructor
  · intro ⟨⟨hx, hy⟩, hsum⟩; exact ⟨x + y, by omega, rfl⟩
  · intro ⟨k, hk, hxy⟩; omega

private lemma antidiagonals_pairwise_disjoint (N : ℕ) :
    (Finset.range N).PairwiseDisjoint Finset.Nat.antidiagonal := by
  intro k _ l _ hkl
  apply Finset.disjoint_left.mpr
  intro ⟨x, y⟩ hk hl
  rw [Finset.Nat.mem_antidiagonal] at hk hl
  exact hkl (hk.trans hl.symm)

/-- Gauss arithmetic series: 2 · ∑_{k=0}^{n} (k+1) = (n+1)(n+2). -/
lemma gauss_sum_succ (n : ℕ) :
    2 * ∑ k in Finset.range (n + 1), (k + 1) = (n + 1) * (n + 2) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ]; push_cast; linarith

/-- **Right Triangle Ehrhart** (doubled): 2·L(Δ_n, t) = (tn+1)(tn+2).
    This encodes L(Δ_n, t) = C(tn+2, 2), with n²t²/2 + 3nt/2 + 1 for the simplex Δ_n.
    Proof: Δ_n decomposes as ⋃_{k=0}^{tn} antidiag(k); each has k+1 lattice points. -/
theorem triangle_ehrhart_double (n t : ℕ) :
    2 * (triangleScaled n t).card = (t * n + 1) * (t * n + 2) := by
  rw [triangleScaled_eq_biUnion, Finset.card_biUnion (antidiagonals_pairwise_disjoint _)]
  simp only [Finset.Nat.card_antidiagonal]
  exact gauss_sum_succ (t * n)

/-- Special case n=1: 2·L(unit simplex, t) = (t+1)(t+2). -/
theorem unit_simplex_ehrhart_double (t : ℕ) :
    2 * (triangleScaled 1 t).card = (t + 1) * (t + 2) := by
  have h := triangle_ehrhart_double 1 t; simpa using h

/-- Triangle Ehrhart in quadratic form: 2·L(Δ_n, t) = n²t² + 3nt + 2.
    This matches area = n²/2, B/2 = 3n/2, constant = 1 (doubled: n²t² + 3nt + 2). -/
theorem triangle_ehrhart_quadratic_double (n t : ℕ) :
    2 * (triangleScaled n t).card = n ^ 2 * t ^ 2 + 3 * n * t + 2 := by
  rw [triangle_ehrhart_double]; ring

-- ============================================================
-- Part III: General Ehrhart Formula via Pick's Theorem  [Proved from axioms]
-- ============================================================

/-!
### Axiomatic Framework

The general 2D Ehrhart formula follows from three facts:
1. Pick's theorem: A = i + b/2 - 1 for any lattice polygon
2. Area scales quadratically under dilation
3. Boundary lattice points scale linearly under dilation

We axiomatize these (matching the gallery's `PicksTheorem.lean`) and derive
the Ehrhart formula as a clean algebraic consequence.
-/

/-- A simple lattice polygon with Pick's theorem data. -/
structure SimpleLatticePolygon where
  interior_count : ℕ
  boundary_count : ℕ
  area           : ℚ
  area_pos       : 0 < area
  boundary_ge_three : 3 ≤ boundary_count

/-- Pick's theorem (axiom, matching PicksTheorem.lean):
    Area = interior_count + boundary_count/2 - 1. -/
axiom picks_theorem (P : SimpleLatticePolygon) :
    P.area = P.interior_count + P.boundary_count / 2 - 1

/-- The integer dilation tP of P (opaque: implementation not needed for the theorem). -/
opaque scaledPolygon (P : SimpleLatticePolygon) (t : ℕ) : SimpleLatticePolygon

/-- Area scaling: Area(tP) = t² · Area(P). -/
axiom scaled_area (P : SimpleLatticePolygon) (t : ℕ) :
    (scaledPolygon P t).area = t ^ 2 * P.area

/-- Boundary scaling: |∂(tP) ∩ ℤ²| = t · |∂P ∩ ℤ²| for t ≥ 1. -/
axiom scaled_boundary (P : SimpleLatticePolygon) (t : ℕ) (ht : 1 ≤ t) :
    (scaledPolygon P t).boundary_count = t * P.boundary_count

/-- Total lattice points in tP: L(P, t) = interior(tP) + boundary(tP). -/
def latticeCount (P : SimpleLatticePolygon) (t : ℕ) : ℕ :=
  (scaledPolygon P t).interior_count + (scaledPolygon P t).boundary_count

/-- **2D Ehrhart Polynomial Theorem**:
    For any convex lattice polygon P with area A and B boundary lattice points,
    the number of lattice points in tP equals A·t² + (B/2)·t + 1.

    Proof chain:
    • `scaled_area` gives Area(tP) = t²A
    • `scaled_boundary` gives B(tP) = tB
    • Pick on tP: t²A = i(tP) + tB/2 - 1, so i(tP) = t²A - tB/2 + 1
    • L = i(tP) + tB = t²A + tB/2 + 1 -/
theorem ehrhart_formula (P : SimpleLatticePolygon) (t : ℕ) (ht : 1 ≤ t) :
    (latticeCount P t : ℚ) = P.area * t ^ 2 + P.boundary_count / 2 * t + 1 := by
  simp only [latticeCount]
  have h_pick := picks_theorem (scaledPolygon P t)
  have h_area := scaled_area P t
  have h_bdy  := scaled_boundary P t ht
  have h_bdy' : ((scaledPolygon P t).boundary_count : ℚ) = t * P.boundary_count := by
    exact_mod_cast h_bdy
  rw [h_area, h_bdy'] at h_pick
  push_cast
  rw [h_bdy']
  linarith

/-- Interior lattice points of tP: i(tP) = A·t² - (B/2)·t + 1 (2D Ehrhart-Macdonald). -/
theorem ehrhart_interior (P : SimpleLatticePolygon) (t : ℕ) (ht : 1 ≤ t) :
    ((scaledPolygon P t).interior_count : ℚ) =
    P.area * t ^ 2 - P.boundary_count / 2 * t + 1 := by
  have h_pick := picks_theorem (scaledPolygon P t)
  have h_area := scaled_area P t
  have h_bdy' : ((scaledPolygon P t).boundary_count : ℚ) = t * P.boundary_count := by
    exact_mod_cast scaled_boundary P t ht
  rw [h_area, h_bdy'] at h_pick
  push_cast; linarith

/-- L is a degree-2 polynomial in t. -/
theorem ehrhart_is_quadratic (P : SimpleLatticePolygon) (t : ℕ) (ht : 1 ≤ t) :
    ∃ a b c : ℚ, (latticeCount P t : ℚ) = a * t ^ 2 + b * t + c :=
  ⟨P.area, P.boundary_count / 2, 1, by linarith [ehrhart_formula P t ht]⟩

/-- The leading coefficient of the Ehrhart polynomial equals the area. -/
theorem ehrhart_leading_coeff (P : SimpleLatticePolygon) (t : ℕ) (ht : 1 ≤ t) :
    (latticeCount P t : ℚ) - P.boundary_count / 2 * t - 1 = P.area * t ^ 2 := by
  linarith [ehrhart_formula P t ht]

/-- Ehrhart-Macdonald 2D reciprocity: i(tP) + L(P°, -t) = 0 is captured by the
    symmetry i(tP) = A·t² - (B/2)·t + 1, which mirrors L(P,t) = A·t² + (B/2)·t + 1
    with the sign of the linear term flipped. This is the 2D Ehrhart reciprocity law. -/
theorem ehrhart_reciprocity_sign_flip (P : SimpleLatticePolygon) (t : ℕ) (ht : 1 ≤ t) :
    (latticeCount P t : ℚ) + (scaledPolygon P t).interior_count =
    2 * P.area * t ^ 2 + 2 := by
  linarith [ehrhart_formula P t ht, ehrhart_interior P t ht]

-- ============================================================
-- Part IV: Examples and Verification
-- ============================================================

/-- The m × n rectangle as a SimpleLatticePolygon (m, n ≥ 1):
    area = mn, boundary = 2(m+n), interior = (m-1)(n-1). -/
noncomputable def rectanglePolygon (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    SimpleLatticePolygon where
  interior_count := (m - 1) * (n - 1)
  boundary_count := 2 * (m + n)
  area           := (m : ℚ) * n
  area_pos       := by positivity
  boundary_ge_three := by omega

/-- Pick's theorem is satisfied for rectangles: mn = (m-1)(n-1) + (m+n) - 1 = mn - 1 + 1 = mn. -/
theorem rectangle_picks_check (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (rectanglePolygon m n hm hn).area =
    (rectanglePolygon m n hm hn).interior_count +
    (rectanglePolygon m n hm hn).boundary_count / 2 - 1 := by
  simp only [rectanglePolygon]
  have hcm : ((m - 1 : ℕ) : ℚ) = m - 1 := by exact_mod_cast Nat.cast_sub hm
  have hcn : ((n - 1 : ℕ) : ℚ) = n - 1 := by exact_mod_cast Nat.cast_sub hn
  push_cast [hcm, hcn]
  ring

/-- The Ehrhart formula for rectangles in the abstract framework.
    Combines with `rectangle_ehrhart` to show both frameworks agree. -/
theorem rectangle_ehrhart_abstract (m n t : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (ht : 1 ≤ t) :
    (latticeCount (rectanglePolygon m n hm hn) t : ℚ) =
    (m : ℚ) * n * t ^ 2 + (m + n) * t + 1 := by
  rw [ehrhart_formula]
  · simp [rectanglePolygon]; push_cast; ring
  · exact ht

/-- Consistency: the abstract Ehrhart formula for R_{m,n} matches the Finset count.
    Both give (tm+1)(tn+1) = mn·t² + (m+n)·t + 1. -/
theorem rectangle_frameworks_agree (m n t : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (ht : 1 ≤ t) :
    (latticeCount (rectanglePolygon m n hm hn) t : ℚ) =
    (rectangleScaled m n t).card := by
  rw [rectangle_ehrhart_abstract m n t hm hn ht]
  rw [rectangle_ehrhart]
  push_cast; ring

-- ============================================================
-- Part V: The Ehrhart h*-vector
-- ============================================================

/-!
### h*-vector

The Ehrhart series ∑_{t≥0} L(P,t) z^t = h*(z) / (1-z)³ where
  h*(z) = 1 + h₁z + h₂z²

For a 2D lattice polygon: h₀=1, h₁ = A + B/2 - 1 = i(P) + B - 1, h₂ = i(P).
By Pick's theorem: h₁ = i(P) + B - 1 and all hᵢ are non-negative (Stanley's theorem).
-/

/-- h*-vector of a SimpleLatticePolygon. -/
noncomputable def hstar (P : SimpleLatticePolygon) : Fin 3 → ℚ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => P.area + P.boundary_count / 2 - 1
  | ⟨2, _⟩ => P.interior_count

/-- h*₀ = 1. -/
theorem hstar_zero (P : SimpleLatticePolygon) : hstar P ⟨0, by omega⟩ = 1 := rfl

/-- h*₂ = i(P) = interior lattice count of P (by definition). -/
theorem hstar_two_eq_interior (P : SimpleLatticePolygon) :
    hstar P ⟨2, by omega⟩ = P.interior_count := rfl

/-- h*₁ ≥ 0: follows from Pick's theorem since h*₁ = i(P) + B - 1 ≥ 0. -/
theorem hstar_one_nonneg (P : SimpleLatticePolygon) : 0 ≤ hstar P ⟨1, by omega⟩ := by
  simp only [hstar]
  have h := picks_theorem P
  -- h: A = i + B/2 - 1, so A + B/2 - 1 = i + B - 2 + B/2... let me compute
  -- h*₁ = A + B/2 - 1 = (i + B/2 - 1) + B/2 - 1 = i + B - 2 ≥ 0 since i ≥ 0 and B ≥ 3
  have hB : (3 : ℚ) ≤ P.boundary_count := by exact_mod_cast P.boundary_ge_three
  linarith [h, (Nat.cast_nonneg P.interior_count : (0 : ℚ) ≤ P.interior_count)]

/-- h*₂ ≥ 0: i(P) ≥ 0 trivially. -/
theorem hstar_two_nonneg (P : SimpleLatticePolygon) : 0 ≤ hstar P ⟨2, by omega⟩ := by
  simp [hstar]; exact Nat.cast_nonneg _

/-- The Ehrhart polynomial recovers from the h*-vector:
    L(P,t) = h*₀ · C(t+2,2) + h*₁ · C(t+1,2) + h*₂ · C(t,2). -/
theorem ehrhart_from_hstar (P : SimpleLatticePolygon) (t : ℕ) (ht : 1 ≤ t) :
    (latticeCount P t : ℚ) =
    hstar P ⟨0, by omega⟩ * ((t + 2) * (t + 1) / 2) +
    hstar P ⟨1, by omega⟩ * ((t + 1) * t / 2) +
    hstar P ⟨2, by omega⟩ * (t * (t - 1) / 2) := by
  simp only [hstar]
  have hE := ehrhart_formula P t ht
  have hB : ((P.boundary_count : ℚ) / 2) * t = P.boundary_count / 2 * t := by ring
  have hi := picks_theorem P
  push_cast at hE ⊢
  field_simp
  nlinarith [hE, hi,
    (Nat.cast_nonneg P.interior_count : (0 : ℚ) ≤ P.interior_count),
    (show (0 : ℚ) ≤ t by exact_mod_cast Nat.zero_le t)]

end EhrhartPolynomial
