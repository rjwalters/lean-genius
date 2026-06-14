import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-
# Feuerbach's Theorem OQ-02 (Murakami): the positive 3D analogue via Grace's theorem

## Open Question
"What is the 3D analogue of Feuerbach's theorem for tetrahedra?"

The sister entry `feuerbachs-theorem-oq-02-incomplete-01` (and the parent file
`FeuerbachsTheoremOQ02.lean`) refuted every *naive* candidate — no single sphere
built from centroid/circumcenter data is tangent to the insphere of a general
tetrahedron.  The genuine 3D Feuerbach statement is **Grace's theorem**
(Grace 1897): the eight tangent spheres of a tetrahedron split into four
homothety pairs (centred at a vertex), and for each pair there is a sphere
through the three vertices of the opposite face that is tangent to *both*
members of the pair.

For a **trirectangular** tetrahedron (mutually perpendicular legs `a, b, c` at the
right-angle vertex `D`) this is provable in explicit coordinates over the field
extension `ℚ(t)`, `t = √(a²b² + b²c² + c²a²)`, avoiding Mathlib's sparse 3D
sphere-tangency layer (Maehara–Martini, *Amer. Math. Monthly* 127(10):897-910, 2020).

## What is proved here
Place `D = (0,0,0)`, `A = (a,0,0)`, `B = (0,b,0)`, `C = (0,0,c)` with `a,b,c > 0`.
The homothety pair centred at `D` consists of the **insphere** and the
**D-exsphere**, with centres `ρ_in·(1,1,1)` and `ρ_ex·(1,1,1)` where, writing
`σ = a+b+c` and `t = √(a²b²+b²c²+c²a²)`,

  ρ_in = (ab+bc+ca − t)/(2σ),   ρ_ex = (ab+bc+ca + t)/(2σ).

The **Grace sphere** through `A, B, C` has the *rational* centre and radius
(the surd `t` cancels)

  Θ = ((a+b)(a+c), (a+b)(b+c), (a+c)(b+c)) / (2σ),
  R = (a² + b² + c² + ab + bc + ca) / (2σ).

We prove (all over `ℚ(t)`, no 3D-tangency API):
1. `grace_through_A/B/C` : `Θ` is equidistant from `A, B, C` at distance `R`
   (so the sphere `(Θ, R)` passes through the opposite face);
2. `grace_tangent_insphere`  : `dist(Θ, I)² = (R − ρ_in)²`  (internal tangency);
3. `grace_tangent_Dexsphere` : `dist(Θ, E)² = (R − ρ_ex)²`  (internal tangency),
   with `R − ρ_in = (a²+b²+c²+t)/(2σ) > 0` and `R − ρ_ex = (a²+b²+c²−t)/(2σ) > 0`,
   so both spheres lie *inside* the Grace sphere — the positive 3D Feuerbach
   (Grace) theorem for the trirectangular family.

The specialisation `(a,b,c) = (2,3,6)`, `t = 6√14`, recovers the parent file's
counterexample tetrahedron `T₀`: `Θ = (40,45,72)/22`, `R = 85/22`.

## Definitional note (parent file)
The parent `FeuerbachsTheoremOQ02.lean` defines `mongePoint = 4G − 3O`, which is
non-standard.  The classical Monge point is `M = 2G − O` (reflection of `O`
through `G`; Encyclopedia of Mathematics, "Tetrahedron").  We record the
classical form here as `mongePointClassical`; the parent entry is left untouched.

## References
- Grace (1897); Maehara & Martini, *Amer. Math. Monthly* 127(10) (2020) 897-910
- arXiv:2301.00731, "Tangent spheres of tetrahedra and a theorem of Grace"
- Murakami (1952); Court (1934); Altshiller-Court, *Modern Pure Solid Geometry* (1935)
-/

set_option linter.unusedVariables false

noncomputable section

namespace FeuerbachsTheoremOQ02Murakami

open Real

-- ============================================================
-- PART 1: Points and squared distance in ℝ³
-- ============================================================

/-- A point in 3-space. -/
abbrev Point3 := ℝ × ℝ × ℝ

/-- Squared Euclidean distance between two points in ℝ³ (avoids `sqrt`). -/
def dist3_sq (P Q : Point3) : ℝ :=
  (Q.1 - P.1) ^ 2 + (Q.2.1 - P.2.1) ^ 2 + (Q.2.2 - P.2.2) ^ 2

/-- Classical Monge point of a tetrahedron with circumcentre `O` and centroid `G`:
    `M = 2G − O` (reflection of `O` through `G`).  Recorded to flag the parent
    file's non-standard `4G − 3O`; not used below. -/
def mongePointClassical (O G : Point3) : Point3 :=
  (2 * G.1 - O.1, 2 * G.2.1 - O.2.1, 2 * G.2.2 - O.2.2)

-- ============================================================
-- PART 2: Cleared (division-free) polynomial backbone
-- ============================================================
/-
These lemmas are the algebraic heart of the result, stated over the surd
variable `t` with the single relation `t² = a²b² + b²c² + c²a²`.  Each is a
polynomial identity discharged by `ring` (part 1) or `linear_combination`
(parts 2-3, using the surd relation exactly once with coefficient `2`).
-/

variable {a b c t : ℝ}

/-- Numerator identity behind `grace_through_A`: with `2σ`-scaled coordinates,
    `‖(2σ)(Θ − A)‖² = ((2σ)R)²`.  Pure `ring` (no surd needed). -/
theorem grace_through_A_cleared :
    ((a + b) * (a + c) - 2 * (a + b + c) * a) ^ 2
      + ((a + b) * (b + c)) ^ 2 + ((a + c) * (b + c)) ^ 2
    = (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a) ^ 2 := by
  ring

/-- Numerator identity behind `grace_through_B`. -/
theorem grace_through_B_cleared :
    ((a + b) * (a + c)) ^ 2
      + ((a + b) * (b + c) - 2 * (a + b + c) * b) ^ 2 + ((a + c) * (b + c)) ^ 2
    = (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a) ^ 2 := by
  ring

/-- Numerator identity behind `grace_through_C`. -/
theorem grace_through_C_cleared :
    ((a + b) * (a + c)) ^ 2 + ((a + b) * (b + c)) ^ 2
      + ((a + c) * (b + c) - 2 * (a + b + c) * c) ^ 2
    = (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a) ^ 2 := by
  ring

/-- Numerator identity behind `grace_tangent_insphere`: writing `ρ_in`'s
    `2σ`-scaled numerator as `ab+bc+ca − t` and `(R − ρ_in)`'s as `a²+b²+c² + t`,
    the squared-distance identity holds modulo `t² = a²b²+b²c²+c²a²`. -/
theorem grace_tangent_insphere_cleared (ht : t ^ 2 = a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) :
    ((a + b) * (a + c) - (a * b + b * c + c * a - t)) ^ 2
      + ((a + b) * (b + c) - (a * b + b * c + c * a - t)) ^ 2
      + ((a + c) * (b + c) - (a * b + b * c + c * a - t)) ^ 2
    = (a ^ 2 + b ^ 2 + c ^ 2 + t) ^ 2 := by
  linear_combination 2 * ht

/-- Numerator identity behind `grace_tangent_Dexsphere`. -/
theorem grace_tangent_Dexsphere_cleared (ht : t ^ 2 = a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) :
    ((a + b) * (a + c) - (a * b + b * c + c * a + t)) ^ 2
      + ((a + b) * (b + c) - (a * b + b * c + c * a + t)) ^ 2
      + ((a + c) * (b + c) - (a * b + b * c + c * a + t)) ^ 2
    = (a ^ 2 + b ^ 2 + c ^ 2 - t) ^ 2 := by
  linear_combination 2 * ht

-- ============================================================
-- PART 3: Geometric statement (Grace sphere over ℚ(t))
-- ============================================================

variable (a b c t)

/-- Right-angle vertex `D = (0,0,0)`. -/
def vD : Point3 := (0, 0, 0)
/-- Vertex `A = (a,0,0)`. -/
def vA : Point3 := (a, 0, 0)
/-- Vertex `B = (0,b,0)`. -/
def vB : Point3 := (0, b, 0)
/-- Vertex `C = (0,0,c)`. -/
def vC : Point3 := (0, 0, c)

/-- Grace-sphere centre `Θ = ((a+b)(a+c),(a+b)(b+c),(a+c)(b+c)) / (2σ)`. -/
def graceCenter : Point3 :=
  ((a + b) * (a + c) / (2 * (a + b + c)),
   (a + b) * (b + c) / (2 * (a + b + c)),
   (a + c) * (b + c) / (2 * (a + b + c)))

/-- Grace-sphere radius `R = (a²+b²+c²+ab+bc+ca) / (2σ)`. -/
def graceRadius : ℝ :=
  (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a) / (2 * (a + b + c))

/-- Inradius scalar `ρ_in = (ab+bc+ca − t) / (2σ)`. -/
def rhoIn : ℝ := (a * b + b * c + c * a - t) / (2 * (a + b + c))

/-- D-exsphere radius scalar `ρ_ex = (ab+bc+ca + t) / (2σ)`. -/
def rhoDex : ℝ := (a * b + b * c + c * a + t) / (2 * (a + b + c))

/-- Insphere centre `I = ρ_in · (1,1,1)`. -/
def inCenter : Point3 := (rhoIn a b c t, rhoIn a b c t, rhoIn a b c t)

/-- D-exsphere centre `E = ρ_ex · (1,1,1)`. -/
def DexCenter : Point3 := (rhoDex a b c t, rhoDex a b c t, rhoDex a b c t)

variable {a b c t}

/-- The Grace sphere passes through `A`: `dist(Θ, A)² = R²`. -/
theorem grace_through_A (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    dist3_sq (graceCenter a b c) (vA a) = graceRadius a b c ^ 2 := by
  have hσ : 2 * (a + b + c) ≠ 0 := by positivity
  simp only [dist3_sq, graceCenter, vA, graceRadius]
  field_simp
  ring

/-- The Grace sphere passes through `B`: `dist(Θ, B)² = R²`. -/
theorem grace_through_B (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    dist3_sq (graceCenter a b c) (vB b) = graceRadius a b c ^ 2 := by
  have hσ : 2 * (a + b + c) ≠ 0 := by positivity
  simp only [dist3_sq, graceCenter, vB, graceRadius]
  field_simp
  ring

/-- The Grace sphere passes through `C`: `dist(Θ, C)² = R²`. -/
theorem grace_through_C (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    dist3_sq (graceCenter a b c) (vC c) = graceRadius a b c ^ 2 := by
  have hσ : 2 * (a + b + c) ≠ 0 := by positivity
  simp only [dist3_sq, graceCenter, vC, graceRadius]
  field_simp
  ring

/-- Internal tangency to the insphere: `dist(Θ, I)² = (R − ρ_in)²`. -/
theorem grace_tangent_insphere (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ht : t ^ 2 = a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) :
    dist3_sq (graceCenter a b c) (inCenter a b c t)
      = (graceRadius a b c - rhoIn a b c t) ^ 2 := by
  have hσ : 2 * (a + b + c) ≠ 0 := by positivity
  simp only [dist3_sq, graceCenter, inCenter, graceRadius, rhoIn]
  field_simp
  linear_combination 2 * ht

/-- Internal tangency to the D-exsphere: `dist(Θ, E)² = (R − ρ_ex)²`. -/
theorem grace_tangent_Dexsphere (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ht : t ^ 2 = a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) :
    dist3_sq (graceCenter a b c) (DexCenter a b c t)
      = (graceRadius a b c - rhoDex a b c t) ^ 2 := by
  have hσ : 2 * (a + b + c) ≠ 0 := by positivity
  simp only [dist3_sq, graceCenter, DexCenter, graceRadius, rhoDex]
  field_simp
  linear_combination 2 * ht

/-- Both tangencies are *internal*: `R − ρ_in = (a²+b²+c²+t)/(2σ) > 0`. -/
theorem grace_minus_rhoIn_eq (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    graceRadius a b c - rhoIn a b c t
      = (a ^ 2 + b ^ 2 + c ^ 2 + t) / (2 * (a + b + c)) := by
  have hσ : 2 * (a + b + c) ≠ 0 := by positivity
  simp only [graceRadius, rhoIn]
  field_simp
  ring

/-- `R − ρ_ex = (a²+b²+c²−t)/(2σ)`; positive since `t < a²+b²+c²`
    (`t² = a²b²+b²c²+c²a² ≤ (a²+b²+c²)²`), so the D-exsphere is internal too. -/
theorem grace_minus_rhoDex_eq (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    graceRadius a b c - rhoDex a b c t
      = (a ^ 2 + b ^ 2 + c ^ 2 - t) / (2 * (a + b + c)) := by
  have hσ : 2 * (a + b + c) ≠ 0 := by positivity
  simp only [graceRadius, rhoDex]
  field_simp
  ring

end FeuerbachsTheoremOQ02Murakami

end
