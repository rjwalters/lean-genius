import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-
# Feuerbach's Theorem OQ-02 (Murakami successor): the positive 3D Feuerbach
  (Grace) theorem for trirectangular tetrahedra.

## Open question
The classical "3D analogue of Feuerbach's theorem" asks for a sphere associated
to every tetrahedron that is tangent to the insphere and the four exspheres.
The naive candidates (homothetic / centroid spheres) are all FALSE: see the
parent file `FeuerbachsTheoremOQ02.lean`, where four candidate spheres are
refuted at the orthocentric tetrahedron T₀ = ((2,0,0),(0,3,0),(0,0,6),(0,0,0)).

The genuine 3D analogue is **Grace's theorem** (Grace 1897): the eight tangent
spheres of a tetrahedron split into four homothety pairs (one per vertex), and
for each pair there is a sphere through the three vertices of the *opposite*
face that is tangent to both members of the pair. Maehara & Martini
(*Tangent Spheres of Tetrahedra and a Theorem of Grace*, Amer. Math. Monthly
127(10):897–910, 2020) give an elementary proof in the **trirectangular** case.
This file formalizes that case.

## The result (trirectangular family)
Let `D = (0,0,0)`, `A = (a,0,0)`, `B = (0,b,0)`, `C = (0,0,c)` with `a,b,c > 0`
(mutually perpendicular legs at `D`). Set `σ = a+b+c`. The `(+,+,+)` homothety
pair of tangent spheres (centred on the ray through `D`) consists of the
insphere `I = ρ_in·(1,1,1)` and the `D`-exsphere `E = ρ_E·(1,1,1)`, where
  ρ_in = (ab+bc+ca − t)/(2σ),   ρ_E = (ab+bc+ca + t)/(2σ),   t = √(a²b² + b²c² + c²a²).

The **Grace sphere** `Θ` through `A, B, C` tangent (internally) to both has

  centre  Θ = ((a+b)(a+c), (a+b)(b+c), (a+c)(b+c)) / (2σ),
  radius  R = (a² + b² + c² + ab + bc + ca) / (2σ),

both **rational** in `a, b, c` — the surd `t` cancels entirely (the 3D analogue
of the 2D nine-point centre being a rational combination of triangle data).

The tangency radii satisfy `R − ρ_in = (a²+b²+c² + t)/(2σ)` and
`R − ρ_E = (a²+b²+c² − t)/(2σ)`, both positive, so the insphere and the
`D`-exsphere both lie *inside* the Grace sphere (both tangencies internal).

At `T₀ = (a,b,c) = (2,3,6)`, `t = 6√14`, this recovers
`Θ = (40,45,72)/22`, `R = 85/22`, `ρ_in = (18−3√14)/11`, `ρ_E = (18+3√14)/11`.

## How the proof is encoded
All claims are algebraic identities. To keep them inside `ring`/`linear_combination`
(no 3D-tangency Mathlib API, which is sparse), we represent the surd `t` by a
real variable with the single relation `t^2 = a²b² + b²c² + c²a²`, and we state
each squared-distance identity in **cleared-denominator form** (every coordinate
scaled by `2σ`, so the geometric identity `‖Θ−P‖² = ρ²` becomes the polynomial
identity `(2σ)²‖Θ−P‖² = (2σ·ρ)²`). The through-vertex identities are pure `ring`;
the tangency identities reduce to `linear_combination 2 * ht` because the
odd-in-`t` part vanishes identically (the mechanism behind the surd cancellation
in Maehara–Martini's proof).

Each scaled identity is paired with its divided, fully geometric counterpart
stated via `sqDist` on coordinate triples, proved from the scaled version.
-/

namespace FeuerbachOQ02Murakami

/-- Squared Euclidean distance on coordinate triples `ℝ × ℝ × ℝ`. -/
def sqDist (p q : ℝ × ℝ × ℝ) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 + (p.2.2 - q.2.2) ^ 2

section Trirectangular

variable (a b c t : ℝ)

/-- The cancelling surd `t = √(a²b² + b²c² + c²a²)`, encoded by its defining
relation. Throughout we assume `ht : t ^ 2 = a²b² + b²c² + c²a²`. -/
def surdRel : Prop := t ^ 2 = a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2

/-! ### Cleared-denominator (scaled) identities

Every quantity below is the geometric one multiplied by `2σ = 2(a+b+c)`.
`Θs k` is `2σ · Θ_k`, `rho_in_s = 2σ · ρ_in`, etc. -/

/-- `2σ · Θ` (Grace-sphere centre, scaled): three coordinates. -/
def ΘsX : ℝ := (a + b) * (a + c)
def ΘsY : ℝ := (a + b) * (b + c)
def ΘsZ : ℝ := (a + c) * (b + c)

/-- `2σ · R` (Grace-sphere radius, scaled). -/
def RsVal : ℝ := a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a

/-- `2σ · ρ_in` and `2σ · ρ_E` (insphere / D-exsphere radii, scaled). -/
def rhoInS : ℝ := a * b + b * c + c * a - t
def rhoES : ℝ := a * b + b * c + c * a + t

/-- **Through-vertex, scaled.** `(2σ)²‖Θ − A‖² = (2σ·R)²` — pure ring identity. -/
theorem grace_through_A_scaled :
    (ΘsX a b c - 2 * (a + b + c) * a) ^ 2 + (ΘsY a b c) ^ 2 + (ΘsZ a b c) ^ 2
      = (RsVal a b c) ^ 2 := by
  simp only [ΘsX, ΘsY, ΘsZ, RsVal]; ring

theorem grace_through_B_scaled :
    (ΘsX a b c) ^ 2 + (ΘsY a b c - 2 * (a + b + c) * b) ^ 2 + (ΘsZ a b c) ^ 2
      = (RsVal a b c) ^ 2 := by
  simp only [ΘsX, ΘsY, ΘsZ, RsVal]; ring

theorem grace_through_C_scaled :
    (ΘsX a b c) ^ 2 + (ΘsY a b c) ^ 2 + (ΘsZ a b c - 2 * (a + b + c) * c) ^ 2
      = (RsVal a b c) ^ 2 := by
  simp only [ΘsX, ΘsY, ΘsZ, RsVal]; ring

/-- **Insphere tangency, scaled.** `(2σ)²‖Θ − I‖² = (2σ(R − ρ_in))²`, i.e.
`(2σ·R − 2σ·ρ_in) = a²+b²+c² + t`. Reduces to `linear_combination 2·ht`
because the odd-in-`t` part cancels. -/
theorem grace_tangent_insphere_scaled (ht : surdRel a b c t) :
    (ΘsX a b c - rhoInS a b c t) ^ 2 + (ΘsY a b c - rhoInS a b c t) ^ 2
        + (ΘsZ a b c - rhoInS a b c t) ^ 2
      = (a ^ 2 + b ^ 2 + c ^ 2 + t) ^ 2 := by
  simp only [ΘsX, ΘsY, ΘsZ, rhoInS, surdRel] at *
  linear_combination 2 * ht

/-- **D-exsphere tangency, scaled.** `(2σ)²‖Θ − E‖² = (2σ(R − ρ_E))²`, i.e.
`(2σ·R − 2σ·ρ_E) = a²+b²+c² − t`. -/
theorem grace_tangent_exsphere_scaled (ht : surdRel a b c t) :
    (ΘsX a b c - rhoES a b c t) ^ 2 + (ΘsY a b c - rhoES a b c t) ^ 2
        + (ΘsZ a b c - rhoES a b c t) ^ 2
      = (a ^ 2 + b ^ 2 + c ^ 2 - t) ^ 2 := by
  simp only [ΘsX, ΘsY, ΘsZ, rhoES, surdRel] at *
  linear_combination 2 * ht

/-! ### Geometric (divided) statements

The actual sphere centre, radius, vertices and tangent-sphere centres, with the
`2σ` denominator restored. Tangency to a sphere of radius `ρ` is the identity
`sqDist Θ P = (R − ρ)²` (internal) / `(R + ρ)²` (external). -/

variable (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)

/-- Grace-sphere centre `Θ`. -/
def Θ : ℝ × ℝ × ℝ :=
  ((a + b) * (a + c) / (2 * (a + b + c)),
   (a + b) * (b + c) / (2 * (a + b + c)),
   (a + c) * (b + c) / (2 * (a + b + c)))

/-- Grace-sphere radius `R`. -/
def Rval : ℝ := (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a) / (2 * (a + b + c))

/-- Vertex `A = (a,0,0)` of the face opposite `D`. -/
def vA : ℝ × ℝ × ℝ := (a, 0, 0)
def vB : ℝ × ℝ × ℝ := (0, b, 0)
def vC : ℝ × ℝ × ℝ := (0, 0, c)

/-- Insphere centre `I = ρ_in·(1,1,1)`. -/
def Icent : ℝ × ℝ × ℝ :=
  ((a * b + b * c + c * a - t) / (2 * (a + b + c)),
   (a * b + b * c + c * a - t) / (2 * (a + b + c)),
   (a * b + b * c + c * a - t) / (2 * (a + b + c)))

/-- `D`-exsphere centre `E = ρ_E·(1,1,1)`. -/
def Ecent : ℝ × ℝ × ℝ :=
  ((a * b + b * c + c * a + t) / (2 * (a + b + c)),
   (a * b + b * c + c * a + t) / (2 * (a + b + c)),
   (a * b + b * c + c * a + t) / (2 * (a + b + c)))

/-- Insphere radius `ρ_in`. -/
def rhoIn : ℝ := (a * b + b * c + c * a - t) / (2 * (a + b + c))
/-- `D`-exsphere radius `ρ_E`. -/
def rhoE : ℝ := (a * b + b * c + c * a + t) / (2 * (a + b + c))

include ha hb hc in
theorem twoσ_ne : (2 * (a + b + c)) ≠ 0 := by positivity

/-- **Grace sphere passes through `A`.** -/
include ha hb hc in
theorem grace_through_A : sqDist (Θ a b c) (vA a) = (Rval a b c) ^ 2 := by
  have h := twoσ_ne a b c ha hb hc
  simp only [sqDist, Θ, vA, Rval]
  field_simp
  ring

include ha hb hc in
theorem grace_through_B : sqDist (Θ a b c) (vB b) = (Rval a b c) ^ 2 := by
  have h := twoσ_ne a b c ha hb hc
  simp only [sqDist, Θ, vB, Rval]
  field_simp
  ring

include ha hb hc in
theorem grace_through_C : sqDist (Θ a b c) (vC c) = (Rval a b c) ^ 2 := by
  have h := twoσ_ne a b c ha hb hc
  simp only [sqDist, Θ, vC, Rval]
  field_simp
  ring

/-- **Internal tangency to the insphere.** `‖Θ − I‖² = (R − ρ_in)²`. -/
include ha hb hc in
theorem grace_tangent_insphere (ht : surdRel a b c t) :
    sqDist (Θ a b c) (Icent a b c t) = (Rval a b c - rhoIn a b c t) ^ 2 := by
  have h := twoσ_ne a b c ha hb hc
  simp only [sqDist, Θ, Icent, Rval, rhoIn]
  field_simp
  have key := grace_tangent_insphere_scaled a b c t ht
  simp only [ΘsX, ΘsY, ΘsZ, rhoInS] at key
  linear_combination key

/-- **Internal tangency to the `D`-exsphere.** `‖Θ − E‖² = (R − ρ_E)²`. -/
include ha hb hc in
theorem grace_tangent_exsphere (ht : surdRel a b c t) :
    sqDist (Θ a b c) (Ecent a b c t) = (Rval a b c - rhoE a b c t) ^ 2 := by
  have h := twoσ_ne a b c ha hb hc
  simp only [sqDist, Θ, Ecent, Rval, rhoE]
  field_simp
  have key := grace_tangent_exsphere_scaled a b c t ht
  simp only [ΘsX, ΘsY, ΘsZ, rhoES] at key
  linear_combination key

end Trirectangular

/-! ### Specialisation to T₀ = (2,3,6)

A numeric sanity check recovering the S4 closed forms `Θ = (40,45,72)/22`,
`R = 85/22`, `ρ_in = (18−3√14)/11`, `ρ_E = (18+3√14)/11`, with `t = 6√14`. -/

section T0

/-- At `T₀`, `t = 6√14` satisfies the surd relation `t² = 2²·3² + 3²·6² + 6²·2²`. -/
theorem T0_surdRel : surdRel 2 3 6 (6 * Real.sqrt 14) := by
  unfold surdRel
  rw [mul_pow, Real.sq_sqrt (by norm_num : (14 : ℝ) ≥ 0)]
  norm_num

/-- Grace sphere at `T₀` passes through `A = (2,0,0)`. -/
theorem T0_through_A : sqDist (Θ 2 3 6) (vA 2) = (Rval 2 3 6) ^ 2 :=
  grace_through_A (a := 2) (b := 3) (c := 6)
    (ha := by norm_num) (hb := by norm_num) (hc := by norm_num)

/-- Grace sphere at `T₀` is internally tangent to the insphere. -/
theorem T0_tangent_insphere :
    sqDist (Θ 2 3 6) (Icent 2 3 6 (6 * Real.sqrt 14))
      = (Rval 2 3 6 - rhoIn 2 3 6 (6 * Real.sqrt 14)) ^ 2 :=
  grace_tangent_insphere (a := 2) (b := 3) (c := 6) (t := 6 * Real.sqrt 14)
    (ha := by norm_num) (hb := by norm_num) (hc := by norm_num) (ht := T0_surdRel)

end T0

end FeuerbachOQ02Murakami
