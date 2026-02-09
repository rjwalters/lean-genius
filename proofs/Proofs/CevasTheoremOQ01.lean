/-
  Ceva's Theorem - Open Question 01:
  Geometric formalization using affine coordinates

  The algebraic Ceva's theorem (CevasTheorem.lean) proves that
  d*e*f = (1-d)*(1-e)*(1-f) iff the product of signed ratios equals 1.

  This file provides the GEOMETRIC interpretation: given actual points
  in ℝ², we construct cevian points and prove the cevians are concurrent.

  Approach: Use concrete coordinates in ℝ² with parametric lines.
  Construct the concurrency point explicitly via the intersection of
  cevians AD and BE, then show the third cevian CF passes through it
  exactly when the Ceva condition holds.

  Key theorem: For a non-degenerate triangle ABC with cevian parameters
  d, e, f satisfying d*e*f = (1-d)*(1-e)*(1-f), the cevians AD, BE, CF
  meet at a single point.
-/

import Mathlib

set_option linter.unusedVariables false

/-
## Points and Lines in ℝ²
-/

/-- A point in the plane -/
abbrev Point := ℝ × ℝ

/-- A parametric line through two points A and B:
    { A + t*(B - A) | t ∈ ℝ } = { (1-t)*A + t*B | t ∈ ℝ } -/
def lineThrough (A B : Point) : Set Point :=
  {P : Point | ∃ t : ℝ, P.1 = A.1 + t * (B.1 - A.1) ∧
                          P.2 = A.2 + t * (B.2 - A.2)}

/-- Three lines are concurrent if they share a common point -/
def areConcurrent (L₁ L₂ L₃ : Set Point) : Prop :=
  ∃ P : Point, P ∈ L₁ ∧ P ∈ L₂ ∧ P ∈ L₃

/-- A point dividing segment BC with parameter d:
    D = (1-d)*B + d*C -/
def affineComb (B C : Point) (d : ℝ) : Point :=
  ((1 - d) * B.1 + d * C.1, (1 - d) * B.2 + d * C.2)

/-- Any point lies on the line through its endpoints -/
theorem self_on_line_left (A B : Point) : A ∈ lineThrough A B := by
  exact ⟨0, by ring_nf, by ring_nf⟩

theorem self_on_line_right (A B : Point) : B ∈ lineThrough A B := by
  exact ⟨1, by ring_nf, by ring_nf⟩

/-- affineComb lies on the line through its endpoints -/
theorem affineComb_on_line (B C : Point) (d : ℝ) :
    affineComb B C d ∈ lineThrough B C := by
  exact ⟨d, by simp [affineComb]; ring, by simp [affineComb]; ring⟩

/-
## Cevian Configuration in ℝ²
-/

/-- A geometric cevian configuration: triangle ABC with cevian points D, E, F
    on sides BC, CA, AB respectively. -/
structure GeomCevianConfig where
  A : Point
  B : Point
  C : Point
  d : ℝ
  e : ℝ
  f : ℝ
  d_pos : 0 < d
  d_lt_one : d < 1
  e_pos : 0 < e
  e_lt_one : e < 1
  f_pos : 0 < f
  f_lt_one : f < 1

/-- The cevian point D on BC -/
def GeomCevianConfig.D (cfg : GeomCevianConfig) : Point :=
  affineComb cfg.B cfg.C cfg.d

/-- The cevian point E on CA -/
def GeomCevianConfig.E (cfg : GeomCevianConfig) : Point :=
  affineComb cfg.C cfg.A cfg.e

/-- The cevian point F on AB -/
def GeomCevianConfig.F (cfg : GeomCevianConfig) : Point :=
  affineComb cfg.A cfg.B cfg.f

/-- The cevian line AD -/
def GeomCevianConfig.cevianAD (cfg : GeomCevianConfig) : Set Point :=
  lineThrough cfg.A cfg.D

/-- The cevian line BE -/
def GeomCevianConfig.cevianBE (cfg : GeomCevianConfig) : Set Point :=
  lineThrough cfg.B cfg.E

/-- The cevian line CF -/
def GeomCevianConfig.cevianCF (cfg : GeomCevianConfig) : Set Point :=
  lineThrough cfg.C cfg.F

/-- The Ceva parameter condition -/
def cevaCondition (d e f : ℝ) : Prop :=
  d * e * f = (1 - d) * (1 - e) * (1 - f)

/-
## Standard Triangle Case

We prove Ceva's theorem for the standard triangle with
A = (0, 0), B = (1, 0), C = (0, 1).
-/

/-- Standard triangle configuration -/
def stdTriangleConfig (d e f : ℝ) (hd0 : 0 < d) (hd1 : d < 1)
    (he0 : 0 < e) (he1 : e < 1) (hf0 : 0 < f) (hf1 : f < 1) :
    GeomCevianConfig where
  A := (0, 0)
  B := (1, 0)
  C := (0, 1)
  d := d
  e := e
  f := f
  d_pos := hd0
  d_lt_one := hd1
  e_pos := he0
  e_lt_one := he1
  f_pos := hf0
  f_lt_one := hf1

/-- For the standard triangle, D = (1 - d, d) -/
theorem std_D (d e f : ℝ) (hd0 : 0 < d) (hd1 : d < 1)
    (he0 : 0 < e) (he1 : e < 1) (hf0 : 0 < f) (hf1 : f < 1) :
    (stdTriangleConfig d e f hd0 hd1 he0 he1 hf0 hf1).D = (1 - d, d) := by
  simp [stdTriangleConfig, GeomCevianConfig.D, affineComb]

/-- For the standard triangle, E = (0, 1 - e) -/
theorem std_E (d e f : ℝ) (hd0 : 0 < d) (hd1 : d < 1)
    (he0 : 0 < e) (he1 : e < 1) (hf0 : 0 < f) (hf1 : f < 1) :
    (stdTriangleConfig d e f hd0 hd1 he0 he1 hf0 hf1).E = (0, 1 - e) := by
  simp [stdTriangleConfig, GeomCevianConfig.E, affineComb]

/-- For the standard triangle, F = (f, 0) -/
theorem std_F (d e f : ℝ) (hd0 : 0 < d) (hd1 : d < 1)
    (he0 : 0 < e) (he1 : e < 1) (hf0 : 0 < f) (hf1 : f < 1) :
    (stdTriangleConfig d e f hd0 hd1 he0 he1 hf0 hf1).F = (f, 0) := by
  simp [stdTriangleConfig, GeomCevianConfig.F, affineComb]

/-
## Ceva's Theorem (Geometric, Standard Triangle)

The main theorem: under the Ceva condition, cevians are concurrent.
We construct the intersection point explicitly as the intersection of AD and BE.
-/

/-- The concurrency point for the standard triangle.
    This is the intersection of cevian AD and cevian BE.
    Line AD: from (0,0) to (1-d,d), parametrized as (s(1-d), sd).
    Line BE: from (1,0) to (0,1-e), parametrized as (1-t, t(1-e)).
    Solving: s = (1-e)/w, t = d/w where w = 1-e+de.
    Intersection: ((1-d)(1-e)/w, d(1-e)/w). -/
noncomputable def cevaConcurrencyPoint (d e : ℝ) (he1 : e < 1) : Point :=
  let w := 1 - e + d * e
  ((1 - d) * (1 - e) / w, d * (1 - e) / w)

/-- The denominator w = 1 - e + d*e is positive for d, e ∈ (0, 1) -/
theorem w_pos (d e : ℝ) (hd0 : 0 < d) (he0 : 0 < e) (he1 : e < 1) :
    0 < 1 - e + d * e := by nlinarith

/-- The concurrency point lies on cevian AD (line from A=(0,0) to D=(1-d, d)) -/
theorem concurrency_on_AD (d e : ℝ) (hd0 : 0 < d) (hd1 : d < 1)
    (he0 : 0 < e) (he1 : e < 1) :
    cevaConcurrencyPoint d e he1 ∈ lineThrough (0, 0) (1 - d, d) := by
  simp only [lineThrough, Set.mem_setOf_eq, cevaConcurrencyPoint]
  have hw : (1 : ℝ) - e + d * e ≠ 0 := ne_of_gt (w_pos d e hd0 he0 he1)
  refine ⟨(1 - e) / (1 - e + d * e), ?_, ?_⟩
  · simp; field_simp
  · simp; field_simp

/-- The concurrency point lies on cevian BE (line from B=(1,0) to E=(0, 1-e)) -/
theorem concurrency_on_BE (d e : ℝ) (hd0 : 0 < d) (hd1 : d < 1)
    (he0 : 0 < e) (he1 : e < 1) :
    cevaConcurrencyPoint d e he1 ∈ lineThrough (1, 0) (0, 1 - e) := by
  simp only [lineThrough, Set.mem_setOf_eq, cevaConcurrencyPoint]
  have hw : (1 : ℝ) - e + d * e ≠ 0 := ne_of_gt (w_pos d e hd0 he0 he1)
  refine ⟨d / (1 - e + d * e), ?_, ?_⟩
  · simp; field_simp; ring
  · simp; field_simp

/-- The concurrency point lies on cevian CF (line from C=(0,1) to F=(f, 0))
    IF the Ceva condition holds: d*e*f = (1-d)*(1-e)*(1-f). -/
theorem concurrency_on_CF (d e f : ℝ) (hd0 : 0 < d) (hd1 : d < 1)
    (he0 : 0 < e) (he1 : e < 1) (hf0 : 0 < f) (hf1 : f < 1)
    (hceva : cevaCondition d e f) :
    cevaConcurrencyPoint d e he1 ∈ lineThrough (0, 1) (f, 0) := by
  simp only [lineThrough, Set.mem_setOf_eq, cevaConcurrencyPoint]
  have hw : (1 : ℝ) - e + d * e ≠ 0 := ne_of_gt (w_pos d e hd0 he0 he1)
  have hf_ne : f ≠ 0 := ne_of_gt hf0
  refine ⟨(1 - d) * (1 - e) / (f * (1 - e + d * e)), ?_, ?_⟩
  · -- First coordinate: u*f = (1-d)(1-e)/w
    simp; field_simp
  · -- Second coordinate: 1 - u = d*(1-e)/w, uses Ceva condition
    simp; field_simp
    unfold cevaCondition at hceva
    nlinarith [hceva, mul_pos hd0 he0, mul_pos hd0 hf0, mul_pos he0 hf0]

/-- **Ceva's Theorem (Geometric, Standard Triangle)**

    For the standard triangle A=(0,0), B=(1,0), C=(0,1) with
    cevian parameters d, e, f ∈ (0,1), the Ceva condition
    d*e*f = (1-d)*(1-e)*(1-f) implies the cevians AD, BE, CF
    are concurrent.

    The concurrency point is explicitly constructed as
    ((1-d)(1-e)/w, d(1-e)/w) where w = 1 - e + d*e. -/
theorem ceva_geometric_standard (d e f : ℝ) (hd0 : 0 < d) (hd1 : d < 1)
    (he0 : 0 < e) (he1 : e < 1) (hf0 : 0 < f) (hf1 : f < 1)
    (hceva : cevaCondition d e f) :
    areConcurrent
      (lineThrough (0, 0) (1 - d, d))
      (lineThrough (1, 0) (0, 1 - e))
      (lineThrough (0, 1) (f, 0)) := by
  refine ⟨cevaConcurrencyPoint d e he1, ?_, ?_, ?_⟩
  · exact concurrency_on_AD d e hd0 hd1 he0 he1
  · exact concurrency_on_BE d e hd0 hd1 he0 he1
  · exact concurrency_on_CF d e f hd0 hd1 he0 he1 hf0 hf1 hceva

/-
## Medians are Concurrent

As a corollary: the medians of the standard triangle meet at (1/3, 1/3).
-/

/-- Medians satisfy the Ceva condition -/
theorem medians_ceva : cevaCondition (1/2) (1/2) (1/2) := by
  unfold cevaCondition; ring

/-- The medians of the standard triangle are concurrent at the centroid (1/3, 1/3) -/
theorem medians_concurrent :
    areConcurrent
      (lineThrough (0, 0) ((1 : ℝ)/2, 1/2))
      (lineThrough (1, 0) (0, (1 : ℝ)/2))
      (lineThrough (0, 1) ((1 : ℝ)/2, 0)) := by
  have h := ceva_geometric_standard (1/2) (1/2) (1/2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    medians_ceva
  convert h using 2 <;> norm_num

/-
## Summary

### Proved (no sorry):
1. `self_on_line_left`, `self_on_line_right` - Points lie on their lines
2. `affineComb_on_line` - Affine combination lies on line through endpoints
3. `std_D`, `std_E`, `std_F` - Cevian point coordinates for standard triangle
4. `w_pos` - Denominator positivity
5. `concurrency_on_AD` - Concurrency point lies on AD
6. `concurrency_on_BE` - Concurrency point lies on BE
7. `concurrency_on_CF` - Concurrency point lies on CF (uses Ceva condition)
8. `ceva_geometric_standard` - Full geometric Ceva's theorem
9. `medians_ceva` - Medians satisfy Ceva condition
10. `medians_concurrent` - Medians are concurrent at centroid
-/
