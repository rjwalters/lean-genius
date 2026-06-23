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
## Converse of Ceva's Theorem

If cevians AD, BE, CF are concurrent, then the Ceva condition holds.

Proof strategy: Suppose all three lines meet at a point P.
P lies on AD means P = (s(1-d), sd) for some s.
P lies on BE means P = (1-t, t(1-e)) for some t.
P lies on CF means P = (uf, 1-u) for some u.

From P on AD ∩ BE: s(1-d) = 1-t and sd = t(1-e).
From P on AD ∩ CF: s(1-d) = uf and sd = 1-u.

The Ceva condition follows from these algebraic constraints.
-/

/-- **Converse of Ceva's Theorem (Standard Triangle)**

    If cevians AD, BE, CF (for the standard triangle) have a common point,
    then the Ceva condition d*e*f = (1-d)*(1-e)*(1-f) holds.

    This is proved by extracting the line parameters at the common point
    and deriving the algebraic identity from the system of equations. -/
theorem ceva_converse_standard (d e f : ℝ) (hd0 : 0 < d) (hd1 : d < 1)
    (he0 : 0 < e) (he1 : e < 1) (hf0 : 0 < f) (hf1 : f < 1)
    (hconc : areConcurrent
      (lineThrough (0, 0) (1 - d, d))
      (lineThrough (1, 0) (0, 1 - e))
      (lineThrough (0, 1) (f, 0))) :
    cevaCondition d e f := by
  -- Extract the common point P and its line parameters
  obtain ⟨P, ⟨s, hs1, hs2⟩, ⟨t, ht1, ht2⟩, ⟨u, hu1, hu2⟩⟩ := hconc
  -- Simplify the line equations
  simp only [] at hs1 hs2 ht1 ht2 hu1 hu2
  -- From AD: P = (s(1-d), sd) since A = (0,0)
  have hP1_AD : P.1 = s * (1 - d) := by linarith
  have hP2_AD : P.2 = s * d := by linarith
  -- From BE: P = (1 - t, t(1-e)) since B = (1,0), E = (0, 1-e)
  have hP1_BE : P.1 = 1 - t := by linarith
  have hP2_BE : P.2 = t * (1 - e) := by linarith
  -- From CF: P = (u*f, 1 - u) since C = (0,1), F = (f, 0)
  have hP1_CF : P.1 = u * f := by linarith
  have hP2_CF : P.2 = 1 - u := by linarith
  -- Key equations:
  -- s(1-d) = 1-t, sd = t(1-e)   ... (from AD ∩ BE)
  -- s(1-d) = uf, sd = 1-u        ... (from AD ∩ CF)
  -- So: 1-t = uf and t(1-e) = 1-u
  have eq1 : 1 - t = u * f := by linarith
  have eq2 : t * (1 - e) = 1 - u := by linarith
  -- Also: s(1-d) + sd = s, and from BE: (1-t) + t(1-e) = 1 - te
  -- From CF: uf + (1-u) = 1 - u + uf = 1 - u(1-f)
  -- These give us s = 1 - te = 1 - u(1-f)
  -- The Ceva condition is d*e*f = (1-d)*(1-e)*(1-f)
  -- From eq1: t = 1 - uf, so te = (1-uf)e = e - uef
  -- From eq2: (1-uf)(1-e) = 1-u, so 1 - uf - e + uef = 1 - u
  --   i.e., u - uf + uef = e, i.e., u(1 - f + ef) = e
  -- Also s(1-d) = uf and sd = 1-u
  -- So s = uf/(1-d) and s = (1-u)/d
  -- Hence uf/(1-d) = (1-u)/d, i.e., ufd = (1-u)(1-d)
  -- From u(1 - f + ef) = e we get u = e/(1 - f + ef)
  -- Then 1-u = (1-f+ef-e)/(1-f+ef) = (1-e)(1-f)/(1-f+ef) + ... let's try directly
  -- ufd = (1-u)(1-d) and u(1-f+ef) = e
  -- From the second: u = e/(1 - f(1-e))
  -- Then ufd = efd/(1 - f(1-e))
  -- 1-u = (1-f(1-e)-e)/(1-f(1-e)) = (1-e-f+ef)/(1-f+ef) = (1-e)(1-f)/(1-f+ef)
  -- (1-u)(1-d) = (1-e)(1-f)(1-d)/(1-f+ef)
  -- So efd/(1-f+ef) = (1-e)(1-f)(1-d)/(1-f+ef)
  -- Since 1-f+ef > 0 (as f < 1, e > 0): def = (1-d)(1-e)(1-f) ✓
  unfold cevaCondition
  -- We need: d * e * f = (1-d) * (1-e) * (1-f)
  -- Use the algebraic approach: from the equations, derive nlinarith-solvable system
  have hd_ne : d ≠ 0 := ne_of_gt hd0
  have h1d_ne : (1 : ℝ) - d ≠ 0 := by linarith
  -- s(1-d) = uf and sd = 1-u give us: u*f*d = (1-u)*(1-d)
  have key : u * f * d = (1 - u) * (1 - d) := by nlinarith
  -- t(1-e) = 1-u and 1-t = uf give us: u*f*(1-e) = (1 - u*f) * (1-e) ... no
  -- Let's use: from eq1: t = 1 - u*f, from eq2: t*(1-e) = 1-u
  -- So (1-uf)(1-e) = 1-u, i.e., 1-e-uf+uef = 1-u, i.e., u-uf+uef = e
  -- i.e., u*(1-f+ef) = e
  have key2 : u * (1 - f + e * f) = e := by nlinarith
  -- From key: ufd = (1-u)(1-d) = (1-d) - u(1-d)
  -- From key2: u = e/(1-f+ef) (when denom ≠ 0)
  -- Substitute: e*f*d/(1-f+ef) = (1-d) - e*(1-d)/(1-f+ef)
  -- Multiply by (1-f+ef): efd = (1-d)(1-f+ef) - e(1-d)
  --   = (1-d)(1-f+ef-e) = (1-d)(1-e)(1-f)  ... wait, 1-f+ef-e = (1-e) + f(e-1) = (1-e)(1-f)
  -- So efd = (1-d)(1-e)(1-f), which is def = (1-d)(1-e)(1-f) ✓
  -- nlinarith should handle this from key and key2
  have hw_pos : (1 : ℝ) - f + e * f > 0 := by nlinarith
  -- From key: u*f*d + u*(1-d) = (1-d), so u*(f*d + 1 - d) = 1-d
  -- From key2: u*(1 - f + e*f) = e
  -- Cross multiply: e*(f*d + 1 - d) = (1-d)*(1-f+e*f)
  -- efd + e - ed = (1-d)(1-f) + (1-d)*ef
  -- efd + e - ed = 1 - f - d + df + ef - def
  -- efd + e - ed = 1 - f - d + df + ef - def
  -- 2*def = 1 - f - d + df + ef - e + ed
  -- 2*def = (1-d)(1-f) + e(d+f) ... hmm, let's just use nlinarith
  nlinarith [mul_pos hd0 he0, mul_pos he0 hf0, mul_pos hd0 hf0,
             mul_pos hw_pos hd0, mul_pos hw_pos he0]


/-- **Ceva's Theorem (Iff, Standard Triangle)**

    For the standard triangle, cevians AD, BE, CF are concurrent
    if and only if the Ceva condition d*e*f = (1-d)*(1-e)*(1-f) holds. -/
theorem ceva_iff_standard (d e f : ℝ) (hd0 : 0 < d) (hd1 : d < 1)
    (he0 : 0 < e) (he1 : e < 1) (hf0 : 0 < f) (hf1 : f < 1) :
    areConcurrent
      (lineThrough (0, 0) (1 - d, d))
      (lineThrough (1, 0) (0, 1 - e))
      (lineThrough (0, 1) (f, 0)) ↔
    cevaCondition d e f :=
  ⟨ceva_converse_standard d e f hd0 hd1 he0 he1 hf0 hf1,
   ceva_geometric_standard d e f hd0 hd1 he0 he1 hf0 hf1⟩


/-
## General Triangle via Affine Transformation

Any non-degenerate triangle can be reduced to the standard triangle by
an invertible affine map. We define non-degeneracy and prove that the
cevian concurrency is preserved under such maps.
-/

/-- The signed area of triangle PQR (twice the area) -/
noncomputable def signedArea (P Q R : Point) : ℝ :=
  (Q.1 - P.1) * (R.2 - P.2) - (R.1 - P.1) * (Q.2 - P.2)

/-- A triangle is non-degenerate iff its signed area is nonzero -/
def triangleNonDegenerate (A B C : Point) : Prop :=
  signedArea A B C ≠ 0

/-- An affine map on ℝ² -/
structure AffineMap2D where
  a₁₁ : ℝ
  a₁₂ : ℝ
  a₂₁ : ℝ
  a₂₂ : ℝ
  b₁ : ℝ
  b₂ : ℝ

/-- Apply an affine map to a point -/
def AffineMap2D.apply (M : AffineMap2D) (P : Point) : Point :=
  (M.a₁₁ * P.1 + M.a₁₂ * P.2 + M.b₁, M.a₂₁ * P.1 + M.a₂₂ * P.2 + M.b₂)

/-- The determinant of the linear part -/
noncomputable def AffineMap2D.det (M : AffineMap2D) : ℝ :=
  M.a₁₁ * M.a₂₂ - M.a₁₂ * M.a₂₁

/-- Affine maps preserve affine combinations -/
theorem affine_preserves_comb (M : AffineMap2D) (B C : Point) (d : ℝ) :
    M.apply (affineComb B C d) = affineComb (M.apply B) (M.apply C) d := by
  ext <;> simp [AffineMap2D.apply, affineComb] <;> ring

/-- Affine maps preserve line membership -/
theorem affine_preserves_line (M : AffineMap2D) (hdet : M.det ≠ 0)
    (A B : Point) (P : Point) (hP : P ∈ lineThrough A B) :
    M.apply P ∈ lineThrough (M.apply A) (M.apply B) := by
  obtain ⟨t, ht1, ht2⟩ := hP
  refine ⟨t, ?_, ?_⟩
  · simp only [AffineMap2D.apply]
    linear_combination M.a₁₁ * ht1 + M.a₁₂ * ht2
  · simp only [AffineMap2D.apply]
    linear_combination M.a₂₁ * ht1 + M.a₂₂ * ht2

/-- Affine maps preserve concurrency (with nonzero determinant) -/
theorem affine_preserves_concurrency (M : AffineMap2D) (hdet : M.det ≠ 0)
    (L₁ L₂ L₃ : Set Point)
    (A₁ B₁ A₂ B₂ A₃ B₃ : Point)
    (hL₁ : L₁ = lineThrough A₁ B₁)
    (hL₂ : L₂ = lineThrough A₂ B₂)
    (hL₃ : L₃ = lineThrough A₃ B₃)
    (hconc : areConcurrent L₁ L₂ L₃) :
    areConcurrent
      (lineThrough (M.apply A₁) (M.apply B₁))
      (lineThrough (M.apply A₂) (M.apply B₂))
      (lineThrough (M.apply A₃) (M.apply B₃)) := by
  obtain ⟨P, hP1, hP2, hP3⟩ := hconc
  refine ⟨M.apply P, ?_, ?_, ?_⟩
  · exact affine_preserves_line M hdet A₁ B₁ P (hL₁ ▸ hP1)
  · exact affine_preserves_line M hdet A₂ B₂ P (hL₂ ▸ hP2)
  · exact affine_preserves_line M hdet A₃ B₃ P (hL₃ ▸ hP3)

/-- The affine map sending the standard triangle to an arbitrary triangle.
    Maps (0,0)↦A, (1,0)↦B, (0,1)↦C. -/
noncomputable def stdToTriangle (A B C : Point) : AffineMap2D where
  a₁₁ := B.1 - A.1
  a₁₂ := C.1 - A.1
  a₂₁ := B.2 - A.2
  a₂₂ := C.2 - A.2
  b₁ := A.1
  b₂ := A.2

/-- stdToTriangle maps (0,0) to A -/
theorem stdToTriangle_origin (A B C : Point) :
    (stdToTriangle A B C).apply (0, 0) = A := by
  simp [stdToTriangle, AffineMap2D.apply]

/-- stdToTriangle maps (1,0) to B -/
theorem stdToTriangle_e1 (A B C : Point) :
    (stdToTriangle A B C).apply (1, 0) = B := by
  ext <;> simp [stdToTriangle, AffineMap2D.apply]

/-- stdToTriangle maps (0,1) to C -/
theorem stdToTriangle_e2 (A B C : Point) :
    (stdToTriangle A B C).apply (0, 1) = C := by
  ext <;> simp [stdToTriangle, AffineMap2D.apply]

/-- The determinant of stdToTriangle equals the signed area -/
theorem stdToTriangle_det (A B C : Point) :
    (stdToTriangle A B C).det = signedArea A B C := by
  simp [stdToTriangle, AffineMap2D.det, signedArea]

/-- For a non-degenerate triangle, stdToTriangle is invertible -/
theorem stdToTriangle_invertible (A B C : Point) (hnd : triangleNonDegenerate A B C) :
    (stdToTriangle A B C).det ≠ 0 := by
  rw [stdToTriangle_det]
  exact hnd

/-- The inverse affine map (from triangle back to standard) -/
noncomputable def triangleToStd (A B C : Point) (hnd : triangleNonDegenerate A B C) :
    AffineMap2D :=
  let Δ := signedArea A B C
  { a₁₁ := (C.2 - A.2) / Δ
    a₁₂ := -(C.1 - A.1) / Δ
    a₂₁ := -(B.2 - A.2) / Δ
    a₂₂ := (B.1 - A.1) / Δ
    b₁ := (A.1 * (C.2 - A.2) - A.2 * (C.1 - A.1)) / (-Δ)
    b₂ := (A.2 * (B.1 - A.1) - A.1 * (B.2 - A.2)) / (-Δ) }

/-- triangleToStd maps A to (0,0) -/
theorem triangleToStd_A (A B C : Point) (hnd : triangleNonDegenerate A B C) :
    (triangleToStd A B C hnd).apply A = (0, 0) := by
  unfold triangleToStd AffineMap2D.apply
  simp only []
  unfold triangleNonDegenerate signedArea at hnd
  set Δ := (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2) with hΔ_def
  have hΔ : Δ ≠ 0 := hnd
  ext
  · simp only [signedArea]
    rw [show (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2) = Δ from rfl]
    field_simp; ring
  · simp only [signedArea]
    rw [show (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2) = Δ from rfl]
    field_simp; ring

/-- triangleToStd maps B to (1,0) -/
theorem triangleToStd_B (A B C : Point) (hnd : triangleNonDegenerate A B C) :
    (triangleToStd A B C hnd).apply B = (1, 0) := by
  unfold triangleToStd AffineMap2D.apply
  simp only []
  unfold triangleNonDegenerate signedArea at hnd
  set Δ := (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2) with hΔ_def
  have hΔ : Δ ≠ 0 := hnd
  ext
  · simp only [signedArea]
    rw [show (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2) = Δ from rfl]
    field_simp; ring
  · simp only [signedArea]
    rw [show (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2) = Δ from rfl]
    field_simp; ring

/-- triangleToStd maps C to (0,1) -/
theorem triangleToStd_C (A B C : Point) (hnd : triangleNonDegenerate A B C) :
    (triangleToStd A B C hnd).apply C = (0, 1) := by
  unfold triangleToStd AffineMap2D.apply
  simp only []
  unfold triangleNonDegenerate signedArea at hnd
  set Δ := (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2) with hΔ_def
  have hΔ : Δ ≠ 0 := hnd
  ext
  · simp only [signedArea]
    rw [show (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2) = Δ from rfl]
    field_simp; ring
  · simp only [signedArea]
    rw [show (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2) = Δ from rfl]
    field_simp; ring

/-- The determinant of triangleToStd is nonzero -/
theorem triangleToStd_det (A B C : Point) (hnd : triangleNonDegenerate A B C) :
    (triangleToStd A B C hnd).det ≠ 0 := by
  unfold triangleNonDegenerate signedArea at hnd
  set Δ := (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2) with hΔ_def
  have hΔ : Δ ≠ 0 := hnd
  show (C.2 - A.2) / Δ * ((B.1 - A.1) / Δ) -
    -(C.1 - A.1) / Δ * (-(B.2 - A.2) / Δ) ≠ 0
  rw [div_mul_div_comm, div_mul_div_comm, ← sub_div]
  rw [show (C.2 - A.2) * (B.1 - A.1) - -(C.1 - A.1) * -(B.2 - A.2) = Δ from by
    rw [neg_mul_neg]; rw [hΔ_def]; ring]
  exact div_ne_zero hΔ (mul_ne_zero hΔ hΔ)

/-- **Ceva's Theorem (General Triangle, Forward Direction)**

    For any non-degenerate triangle ABC with cevian parameters d, e, f ∈ (0,1),
    if the Ceva condition d*e*f = (1-d)*(1-e)*(1-f) holds, then the cevians
    AD, BE, CF are concurrent.

    This follows from the standard triangle case via the affine map stdToTriangle. -/
theorem ceva_geometric_general (A B C : Point)
    (hnd : triangleNonDegenerate A B C)
    (d e f : ℝ) (hd0 : 0 < d) (hd1 : d < 1)
    (he0 : 0 < e) (he1 : e < 1) (hf0 : 0 < f) (hf1 : f < 1)
    (hceva : cevaCondition d e f) :
    areConcurrent
      (lineThrough A (affineComb B C d))
      (lineThrough B (affineComb C A e))
      (lineThrough C (affineComb A B f)) := by
  -- Use the standard triangle result and map forward
  have hstd := ceva_geometric_standard d e f hd0 hd1 he0 he1 hf0 hf1 hceva
  -- The standard triangle maps to our triangle via stdToTriangle
  set M := stdToTriangle A B C
  have hdet : M.det ≠ 0 := stdToTriangle_invertible A B C hnd
  -- Map the standard concurrency forward
  have hmapped := affine_preserves_concurrency M hdet
    (lineThrough (0, 0) (1 - d, d))
    (lineThrough (1, 0) (0, 1 - e))
    (lineThrough (0, 1) (f, 0))
    (0, 0) (1 - d, d) (1, 0) (0, 1 - e) (0, 1) (f, 0)
    rfl rfl rfl hstd
  -- Now show that M maps the standard points to our triangle points
  have hMA : M.apply (0, 0) = A := stdToTriangle_origin A B C
  have hMB : M.apply (1, 0) = B := stdToTriangle_e1 A B C
  have hMC : M.apply (0, 1) = C := stdToTriangle_e2 A B C
  -- And M maps affine combinations correctly
  have hMD : M.apply (1 - d, d) = affineComb B C d := by
    rw [show ((1 - d, d) : Point) = affineComb (1, 0) (0, 1) d from by
      ext <;> simp [affineComb]]
    rw [affine_preserves_comb, hMB, hMC]
  have hME : M.apply (0, 1 - e) = affineComb C A e := by
    rw [show ((0, 1 - e) : Point) = affineComb (0, 1) (0, 0) e from by
      ext <;> simp [affineComb]]
    rw [affine_preserves_comb, hMC, hMA]
  have hMF : M.apply (f, 0) = affineComb A B f := by
    rw [show ((f, 0) : Point) = affineComb (0, 0) (1, 0) f from by
      ext <;> simp [affineComb]]
    rw [affine_preserves_comb, hMA, hMB]
  -- Rewrite the mapped result
  rw [hMA, hMD, hMB, hME, hMC, hMF] at hmapped
  exact hmapped


/-
## Additional Corollaries
-/

/-- The cevian configuration for a general triangle -/
structure GeneralCevianConfig where
  A : Point
  B : Point
  C : Point
  d : ℝ
  e : ℝ
  f : ℝ
  nd : triangleNonDegenerate A B C
  d_pos : 0 < d
  d_lt_one : d < 1
  e_pos : 0 < e
  e_lt_one : e < 1
  f_pos : 0 < f
  f_lt_one : f < 1

/-- The cevian point D on BC for a general triangle -/
def GeneralCevianConfig.D (cfg : GeneralCevianConfig) : Point :=
  affineComb cfg.B cfg.C cfg.d

/-- The cevian point E on CA for a general triangle -/
def GeneralCevianConfig.E (cfg : GeneralCevianConfig) : Point :=
  affineComb cfg.C cfg.A cfg.e

/-- The cevian point F on AB for a general triangle -/
def GeneralCevianConfig.F (cfg : GeneralCevianConfig) : Point :=
  affineComb cfg.A cfg.B cfg.f

/-- **Ceva's Theorem (General, Forward)**
    For any non-degenerate cevian configuration satisfying the Ceva condition,
    the cevians are concurrent. -/
theorem ceva_general_forward (cfg : GeneralCevianConfig)
    (hceva : cevaCondition cfg.d cfg.e cfg.f) :
    areConcurrent
      (lineThrough cfg.A cfg.D)
      (lineThrough cfg.B cfg.E)
      (lineThrough cfg.C cfg.F) :=
  ceva_geometric_general cfg.A cfg.B cfg.C cfg.nd cfg.d cfg.e cfg.f
    cfg.d_pos cfg.d_lt_one cfg.e_pos cfg.e_lt_one cfg.f_pos cfg.f_lt_one hceva

/-
## Converse of Ceva's Theorem (General Triangle)

If cevians are concurrent in a general non-degenerate triangle,
then the Ceva condition holds. Proved by mapping back to the standard
triangle via triangleToStd and applying the standard converse.
-/

/-- **Converse of Ceva's Theorem (General Triangle)**

    For any non-degenerate triangle, if the cevians AD, BE, CF are concurrent,
    then the Ceva condition d*e*f = (1-d)*(1-e)*(1-f) holds.

    Proof: apply the inverse affine map (triangleToStd) to reduce to the
    standard triangle, then use ceva_converse_standard. -/
theorem ceva_converse_general (A B C : Point)
    (hnd : triangleNonDegenerate A B C)
    (d e f : ℝ) (hd0 : 0 < d) (hd1 : d < 1)
    (he0 : 0 < e) (he1 : e < 1) (hf0 : 0 < f) (hf1 : f < 1)
    (hconc : areConcurrent
      (lineThrough A (affineComb B C d))
      (lineThrough B (affineComb C A e))
      (lineThrough C (affineComb A B f))) :
    cevaCondition d e f := by
  -- Map to standard triangle via triangleToStd
  set M := triangleToStd A B C hnd
  have hdet : M.det ≠ 0 := triangleToStd_det A B C hnd
  -- Map the concurrent lines to the standard triangle
  have hmapped := affine_preserves_concurrency M hdet
    (lineThrough A (affineComb B C d))
    (lineThrough B (affineComb C A e))
    (lineThrough C (affineComb A B f))
    A (affineComb B C d) B (affineComb C A e) C (affineComb A B f)
    rfl rfl rfl hconc
  -- Show M maps our points to the standard triangle points
  have hMA : M.apply A = (0, 0) := triangleToStd_A A B C hnd
  have hMB : M.apply B = (1, 0) := triangleToStd_B A B C hnd
  have hMC : M.apply C = (0, 1) := triangleToStd_C A B C hnd
  -- M preserves affine combinations
  have hMD : M.apply (affineComb B C d) = affineComb (1, 0) (0, 1) d := by
    rw [affine_preserves_comb M B C d, hMB, hMC]
  have hME : M.apply (affineComb C A e) = affineComb (0, 1) (0, 0) e := by
    rw [affine_preserves_comb M C A e, hMC, hMA]
  have hMF : M.apply (affineComb A B f) = affineComb (0, 0) (1, 0) f := by
    rw [affine_preserves_comb M A B f, hMA, hMB]
  -- Compute the standard triangle cevian points
  have hD_std : affineComb (1, 0) (0, 1) d = (1 - d, d) := by
    ext <;> simp [affineComb]
  have hE_std : affineComb (0, 1) (0, 0) e = (0, 1 - e) := by
    ext <;> simp [affineComb]
  have hF_std : affineComb (0, 0) (1, 0) f = (f, 0) := by
    ext <;> simp [affineComb]
  rw [hMA, hMB, hMC, hMD, hME, hMF, hD_std, hE_std, hF_std] at hmapped
  -- Now we have concurrency in the standard triangle
  exact ceva_converse_standard d e f hd0 hd1 he0 he1 hf0 hf1 hmapped

/-- **Ceva's Theorem (Iff, General Triangle)**

    For any non-degenerate triangle ABC with cevian parameters d, e, f ∈ (0,1),
    the cevians AD, BE, CF are concurrent if and only if
    d*e*f = (1-d)*(1-e)*(1-f). -/
theorem ceva_iff_general (A B C : Point)
    (hnd : triangleNonDegenerate A B C)
    (d e f : ℝ) (hd0 : 0 < d) (hd1 : d < 1)
    (he0 : 0 < e) (he1 : e < 1) (hf0 : 0 < f) (hf1 : f < 1) :
    areConcurrent
      (lineThrough A (affineComb B C d))
      (lineThrough B (affineComb C A e))
      (lineThrough C (affineComb A B f)) ↔
    cevaCondition d e f :=
  ⟨ceva_converse_general A B C hnd d e f hd0 hd1 he0 he1 hf0 hf1,
   ceva_geometric_general A B C hnd d e f hd0 hd1 he0 he1 hf0 hf1⟩

/-- **Ceva's Theorem (Iff) via GeneralCevianConfig** -/
theorem ceva_general_iff (cfg : GeneralCevianConfig) :
    areConcurrent
      (lineThrough cfg.A cfg.D)
      (lineThrough cfg.B cfg.E)
      (lineThrough cfg.C cfg.F) ↔
    cevaCondition cfg.d cfg.e cfg.f :=
  ceva_iff_general cfg.A cfg.B cfg.C cfg.nd cfg.d cfg.e cfg.f
    cfg.d_pos cfg.d_lt_one cfg.e_pos cfg.e_lt_one cfg.f_pos cfg.f_lt_one

/-
## Classical Concurrence Results via Ceva
-/

/-- Angle bisectors satisfy the Ceva condition when the parameters relate to
    side lengths as d = b/(b+c), e = c/(c+a), f = a/(a+b).

    For a triangle with side lengths a, b, c opposite to vertices A, B, C:
    - D on BC divides it as BD/DC = c/b, so d = b/(b+c)
    - E on CA divides it as CE/EA = a/c, so e = c/(c+a)
    - F on AB divides it as AF/FB = b/a, so f = a/(a+b)

    Then d*e*f = abc/[(b+c)(c+a)(a+b)] = (1-d)*(1-e)*(1-f). -/
theorem angle_bisectors_ceva (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    cevaCondition (b / (b + c)) (c / (c + a)) (a / (a + b)) := by
  unfold cevaCondition
  have hbc : 0 < b + c := by linarith
  have hca : 0 < c + a := by linarith
  have hab : 0 < a + b := by linarith
  field_simp
  ring

/-- The angle bisector parameters are in (0, 1) -/
theorem angle_bisector_param_pos (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < b / (b + c) ∧ b / (b + c) < 1 ∧
    0 < c / (c + a) ∧ c / (c + a) < 1 ∧
    0 < a / (a + b) ∧ a / (a + b) < 1 := by
  have hbc : 0 < b + c := by linarith
  have hca : 0 < c + a := by linarith
  have hab : 0 < a + b := by linarith
  refine ⟨div_pos hb hbc, (div_lt_one hbc).mpr (by linarith),
          div_pos hc hca, (div_lt_one hca).mpr (by linarith),
          div_pos ha hab, (div_lt_one hab).mpr (by linarith)⟩

/-- **Angle Bisectors are Concurrent (Incenter)**

    For any non-degenerate triangle with side lengths a, b, c > 0,
    the angle bisectors are concurrent. -/
theorem angle_bisectors_concurrent (A B C : Point)
    (hnd : triangleNonDegenerate A B C)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    areConcurrent
      (lineThrough A (affineComb B C (b / (b + c))))
      (lineThrough B (affineComb C A (c / (c + a))))
      (lineThrough C (affineComb A B (a / (a + b)))) := by
  obtain ⟨hd0, hd1, he0, he1, hf0, hf1⟩ := angle_bisector_param_pos a b c ha hb hc
  exact ceva_geometric_general A B C hnd _ _ _ hd0 hd1 he0 he1 hf0 hf1
    (angle_bisectors_ceva a b c ha hb hc)

-- Altitudes satisfy the Ceva condition when the parameters relate to
-- side lengths and angles. We use the projection formula approach:
-- d = b·cos(C)/a, e = c·cos(A)/b, f = a·cos(B)/c.

/-- For an equilateral triangle, all altitudes have d = e = f = 1/2,
    which is the same as medians. This verifies altitude concurrence
    for the equilateral case. -/
theorem equilateral_altitudes_ceva :
    cevaCondition (1/2) (1/2) (1/2) := by
  unfold cevaCondition; ring

-- The altitude Ceva condition follows algebraically from the projection formulas:
-- d = b·cos(C)/a, e = c·cos(A)/b, f = a·cos(B)/c
-- Then d·e·f = cos(A)·cos(B)·cos(C) = (1-d)·(1-e)·(1-f).

/-- **Altitude Ceva Condition (Algebraic)**

    For a triangle with sides a, b, c (all positive) and altitude foot parameters
    d = b·cos(C)/a, e = c·cos(A)/b, f = a·cos(B)/c, the complementary parameters
    satisfy (1-d) = c·cos(B)/a, (1-e) = a·cos(C)/b, (1-f) = b·cos(A)/c.

    Therefore d·e·f = cos(A)·cos(B)·cos(C) = (1-d)·(1-e)·(1-f).

    We formalize this as: for any positive reals p, q, r, s, t, u with
    p + s = a, q + t = b, r + u = c (altitude foot decompositions),
    the corresponding Ceva parameters satisfy the condition. -/
theorem altitude_ceva_algebraic (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (cosA cosB cosC : ℝ)
    (h_proj_a : b * cosC + c * cosB = a)
    (h_proj_b : c * cosA + a * cosC = b)
    (h_proj_c : a * cosB + b * cosA = c) :
    cevaCondition (b * cosC / a) (c * cosA / b) (a * cosB / c) := by
  unfold cevaCondition
  have ha' : a ≠ 0 := ne_of_gt ha
  have hb' : b ≠ 0 := ne_of_gt hb
  have hc' : c ≠ 0 := ne_of_gt hc
  -- 1 - d = (a - b*cosC)/a = c*cosB/a (from projection formula)
  -- 1 - e = (b - c*cosA)/b = a*cosC/b
  -- 1 - f = (c - a*cosB)/c = b*cosA/c
  -- Use projection formulas: a - b*cosC = c*cosB, etc.
  -- LHS = d*e*f = (b*cosC/a)*(c*cosA/b)*(a*cosB/c) = cosA*cosB*cosC
  -- RHS = (1-d)*(1-e)*(1-f) = (c*cosB/a)*(a*cosC/b)*(b*cosA/c) = cosA*cosB*cosC
  -- Both sides are equal, so rewrite using projection formulas then use ring.
  have h1 : a - b * cosC = c * cosB := by linarith [h_proj_a]
  have h2 : b - c * cosA = a * cosC := by linarith [h_proj_b]
  have h3 : c - a * cosB = b * cosA := by linarith [h_proj_c]
  -- Rewrite (1 - b*cosC/a) = c*cosB/a, etc.
  -- Both sides equal cosA*cosB*cosC after projection formula substitution
  -- LHS = b*cosC/a * c*cosA/b * a*cosB/c = cosA*cosB*cosC
  -- RHS = (a-b*cosC)/a * (b-c*cosA)/b * (c-a*cosB)/c
  --     = c*cosB/a * a*cosC/b * b*cosA/c = cosA*cosB*cosC
  -- After field_simp, both are polynomials. We substitute h1,h2,h3 and use ring.
  suffices h : b * cosC * (c * cosA) * (a * cosB) =
    (a - b * cosC) * (b - c * cosA) * (c - a * cosB) by
    field_simp; linarith
  -- Substitute: a - b*cosC = c*cosB, b - c*cosA = a*cosC, c - a*cosB = b*cosA
  rw [h1, h2, h3]; ring

/-
## Routh's Theorem (Area Ratio)

When cevians don't quite satisfy the Ceva condition, they form an inner
triangle. Routh's theorem computes the ratio of this triangle's area
to the original.

For cevian parameters d, e, f, the area ratio is:
  (d·e·f - (1-d)·(1-e)·(1-f))² / ((1-d+d·e)(1-e+e·f)(1-f+f·d))

When d·e·f = (1-d)·(1-e)·(1-f) (Ceva condition), the ratio is 0
(the inner triangle degenerates to a point = concurrency point).
-/

/-- Routh's ratio for the inner triangle formed by three cevians. -/
noncomputable def routhRatio (d e f : ℝ) : ℝ :=
  (d * e * f - (1 - d) * (1 - e) * (1 - f)) ^ 2 /
  ((1 - d + d * e) * (1 - e + e * f) * (1 - f + f * d))

/-- When the Ceva condition holds, Routh's ratio is 0
    (cevians are concurrent, no inner triangle). -/
theorem routh_zero_iff_ceva (d e f : ℝ)
    (hd0 : 0 < d) (hd1 : d < 1)
    (he0 : 0 < e) (he1 : e < 1)
    (hf0 : 0 < f) (hf1 : f < 1) :
    routhRatio d e f = 0 ↔ cevaCondition d e f := by
  unfold routhRatio cevaCondition
  have hw1 : 0 < 1 - d + d * e := by nlinarith
  have hw2 : 0 < 1 - e + e * f := by nlinarith
  have hw3 : 0 < 1 - f + f * d := by nlinarith
  rw [div_eq_zero_iff]
  constructor
  · intro h
    cases h with
    | inl h =>
      have := sq_eq_zero_iff.mp h
      linarith
    | inr h =>
      exfalso; exact absurd h (ne_of_gt (mul_pos (mul_pos hw1 hw2) hw3))
  · intro h
    left
    have : d * e * f - (1 - d) * (1 - e) * (1 - f) = 0 := by linarith
    rw [this, zero_pow (by norm_num : 2 ≠ 0)]

/-- **Routh's theorem for medial cevians**: when d = e = f = 1/3,
    the inner triangle has area ratio 1/7 of the original.
    (This is a well-known result: cevians through the centroid
    at 1/3 divisions create a triangle with 1/7 the area.) -/
theorem routh_medial_thirds :
    routhRatio (1/3) (1/3) (1/3) = 1 / 7 := by
  unfold routhRatio
  norm_num

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
8. `ceva_geometric_standard` - Ceva's theorem (standard triangle, forward)
9. `medians_ceva` - Medians satisfy Ceva condition
10. `medians_concurrent` - Medians are concurrent at centroid
11. `ceva_converse_standard` - Converse of Ceva's theorem (standard triangle)
12. `ceva_iff_standard` - Ceva's theorem iff (standard triangle)
13. `affine_preserves_comb` - Affine maps preserve affine combinations
14. `affine_preserves_line` - Affine maps preserve line membership
15. `affine_preserves_concurrency` - Affine maps preserve concurrency
16. `stdToTriangle_*` - Standard-to-general affine map properties
17. `triangleToStd_*` - General-to-standard inverse map properties
18. `ceva_geometric_general` - Ceva's theorem (general triangle, forward)
19. `ceva_general_forward` - Ceva's theorem via GeneralCevianConfig
20. `ceva_converse_general` - Converse of Ceva (general triangle)
21. `ceva_iff_general` - Full iff characterization (general triangle)
22. `ceva_general_iff` - Iff via GeneralCevianConfig
23. `angle_bisectors_ceva` - Angle bisector parameters satisfy Ceva condition
24. `angle_bisectors_concurrent` - Angle bisectors meet at incenter
25. `altitude_ceva_algebraic` - Altitude parameters satisfy Ceva condition
26. `routh_zero_iff_ceva` - Routh's ratio = 0 iff Ceva condition
27. `routh_medial_thirds` - Routh's ratio for 1/3 divisions = 1/7
-/
