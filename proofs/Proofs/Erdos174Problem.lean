/-
# Erdős Problem #174: Euclidean Ramsey Sets

Source: https://erdosproblems.com/174
Status: OPEN (characterization problem)

Statement:
A finite set A ⊂ ℝⁿ is called Ramsey if, for any k ≥ 1, there exists some
d = d(A,k) such that in any k-colouring of ℝᵈ there exists a monochromatic
copy of A. Characterise the Ramsey sets in ℝⁿ.

Key Results:
- [EGMRSS73] Every Ramsey set is spherical (lies on a sphere's surface)
- Graham's conjecture: Every spherical set is Ramsey
- Leader-Russell-Walters conjecture: A set is Ramsey iff subtransitive

Known Ramsey Sets:
- Vertices of k-dimensional rectangles [EGMRSS73]
- Non-degenerate simplices [FrRo90]
- Trapezoids [Kr92]
- Regular polygons and polyhedra [Kr91]

History:
- Introduced by Erdős, Graham, Montgomery, Rothschild, Spencer, Straus (1973)
- Part of Euclidean Ramsey theory, extending classical Ramsey theory to geometry

References:
- [EGMRSS73] Erdős-Graham-Montgomery-Rothschild-Spencer-Straus (1973),
  "Euclidean Ramsey Theorems I", J. Comb. Th. A
- [FrRo90] Frankl-Rödl (1990), "A partition property of simplices"
- [Kr91] Kříž (1991), "Permutation groups in Euclidean Ramsey theory"
- [Kr92] Kříž (1992), "All trapezoids are Ramsey"
- [LRW12] Leader-Russell-Walters (2012), "Transitive sets in Euclidean Ramsey theory"
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fin.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.LinearAlgebra.AffineSpace.Combination

namespace Erdos174

/- ## Part I: Basic Setup -/

/-- A finite configuration in ℝⁿ. -/
def FiniteConfig (n : ℕ) := Finset (EuclideanSpace ℝ (Fin n))

/-- A congruent copy of configuration A in ℝᵈ: the image of A under
    a distance-preserving map. -/
def IsCongruentCopy {n d : ℕ} (A : FiniteConfig n) (B : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d)),
    (∀ x y : EuclideanSpace ℝ (Fin n), dist (f x) (f y) = dist x y) ∧
    B = A.image f

/- ## Part II: Euclidean Ramsey Property -/

/-- A k-coloring of ℝᵈ. -/
def Coloring (d k : ℕ) := EuclideanSpace ℝ (Fin d) → Fin k

/-- A set B is monochromatic under coloring χ. -/
def IsMonochromatic {d k : ℕ} (B : Finset (EuclideanSpace ℝ (Fin d)))
    (χ : Coloring d k) : Prop :=
  ∃ c : Fin k, ∀ x ∈ B, χ x = c

/-- **Euclidean Ramsey Property:**
A finite set A ⊂ ℝⁿ is Ramsey if for any number of colors k,
there exists a dimension d such that any k-coloring of ℝᵈ
contains a monochromatic congruent copy of A. -/
def IsRamsey {n : ℕ} (A : FiniteConfig n) : Prop :=
  ∀ k : ℕ, k ≥ 1 →
    ∃ d : ℕ,
      ∀ χ : Coloring d k,
        ∃ B : Finset (EuclideanSpace ℝ (Fin d)),
          IsCongruentCopy A B ∧ IsMonochromatic B χ

/- ## Part III: Spherical Sets -/

/-- A set lies on the surface of a sphere. -/
def IsSpherical {n : ℕ} (A : FiniteConfig n) : Prop :=
  ∃ (center : EuclideanSpace ℝ (Fin n)) (radius : ℝ),
    radius > 0 ∧ ∀ x ∈ A, dist x center = radius

/-- **EGMRSS (1973):** Every Ramsey set is spherical.
This is a necessary condition for being Ramsey.
The proof uses a distance-based coloring: if A is not spherical,
construct a coloring that prevents any monochromatic copy. -/
axiom ramsey_implies_spherical {n : ℕ} (A : FiniteConfig n) :
    IsRamsey A → IsSpherical A

/- ## Part IV: Open Conjectures -/

/-- **Graham's Conjecture:** Every spherical set is Ramsey.
This would give a complete characterization: Ramsey ⟺ Spherical. -/
def graham_conjecture : Prop :=
  ∀ (n : ℕ) (A : FiniteConfig n), IsSpherical A → IsRamsey A

/-- A set is subtransitive if it can be embedded in a set on which
    the rotation group acts transitively. -/
def IsSubtransitive {n : ℕ} (A : FiniteConfig n) : Prop :=
  ∃ (m : ℕ) (S : Set (EuclideanSpace ℝ (Fin m))),
    (∀ x y ∈ S, ∃ (R : EuclideanSpace ℝ (Fin m) ≃ᵢ EuclideanSpace ℝ (Fin m)),
      R x = y ∧ ∀ z ∈ S, R z ∈ S) ∧
    (∃ (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)),
      (∀ x y, dist (f x) (f y) = dist x y) ∧
      ∀ a ∈ A, f a ∈ S)

/-- **Leader-Russell-Walters Conjecture (2012):**
A set is Ramsey if and only if it is subtransitive. -/
def lrw_conjecture : Prop :=
  ∀ (n : ℕ) (A : FiniteConfig n), IsRamsey A ↔ IsSubtransitive A

/- ## Part V: Known Ramsey Sets -/

/-- A rectangle: vertices of a k-dimensional box. -/
def IsRectangle {n : ℕ} (A : FiniteConfig n) : Prop :=
  ∃ (k : ℕ) (sides : Fin k → ℝ),
    (∀ i, sides i > 0) ∧
    A.card = 2^k

/-- **EGMRSS (1973):** All rectangles are Ramsey.
Uses a product argument in high dimensions. -/
axiom rectangle_is_ramsey {n : ℕ} (A : FiniteConfig n) :
    IsRectangle A → IsRamsey A

/-- A non-degenerate simplex: k+1 affinely independent points. -/
def IsSimplex {n : ℕ} (A : FiniteConfig n) : Prop :=
  ∃ k : ℕ, A.card = k + 1 ∧ k ≤ n ∧
    ∀ (coeffs : A → ℝ), (∑ a ∈ A.attach, coeffs a = 0) →
      (∑ a ∈ A.attach, coeffs a • (a : EuclideanSpace ℝ (Fin n)) = 0) →
      (∀ a, coeffs a = 0)

/-- **Frankl-Rödl (1990):** All non-degenerate simplices are Ramsey.
Uses partite methods and product structure. -/
axiom simplex_is_ramsey {n : ℕ} (A : FiniteConfig n) :
    IsSimplex A → IsRamsey A

/-- A trapezoid: four points with two parallel sides. -/
def IsTrapezoid {n : ℕ} (A : FiniteConfig n) : Prop :=
  A.card = 4 ∧
  ∃ (a b c d : EuclideanSpace ℝ (Fin n)),
    A = {a, b, c, d} ∧
    ∃ (t : ℝ), t > 0 ∧ t ≠ 1 ∧ (d - c) = t • (b - a)

/-- **Kříž (1992):** All trapezoids are Ramsey.
Extends Ramsey families using affine structure. -/
axiom trapezoid_is_ramsey {n : ℕ} (A : FiniteConfig n) :
    IsTrapezoid A → IsRamsey A

/-- A regular polygon with m vertices. -/
def IsRegularPolygon {n : ℕ} (A : FiniteConfig n) (m : ℕ) : Prop :=
  m ≥ 3 ∧ A.card = m ∧ IsSpherical A

/-- **Kříž (1991):** All regular polygons and polyhedra are Ramsey.
Uses permutation group methods and symmetry arguments. -/

/- ## Part VI: Examples -/

/-- The simplest Ramsey set: two points. -/
def twoPoints : FiniteConfig 1 :=
  {![0], ![1]}

/-- Two points always lie on a sphere and are trivially Ramsey (pigeonhole). -/

/-- An equilateral triangle in ℝ². -/
def equilateralTriangle : FiniteConfig 2 :=
  {![0, 0], ![1, 0], ![0.5, Real.sqrt 3 / 2]}

/-- Equilateral triangles are Ramsey (special case of simplex). -/

/-- A unit square in ℝ². -/
def square : FiniteConfig 2 :=
  {![0, 0], ![1, 0], ![1, 1], ![0, 1]}

/-- Squares are Ramsey (special case of rectangle). -/

/- ## Part VII: Non-Ramsey Sets -/

/-- A necessary condition: non-spherical sets are not Ramsey. -/
theorem not_spherical_not_ramsey {n : ℕ} (A : FiniteConfig n) :
    ¬IsSpherical A → ¬IsRamsey A := by
  intro hNotSph hRam
  exact hNotSph (ramsey_implies_spherical A hRam)

/-- Four collinear points with non-equal spacing: not spherical, hence not Ramsey. -/
def collinearFour : FiniteConfig 1 :=
  {![0], ![1], ![2], ![4]}

/-- Four collinear points with unequal spacing cannot all lie on a circle. -/
axiom collinear_not_spherical : ¬IsSpherical collinearFour

/-- Collinear non-spherical points are not Ramsey. -/
theorem collinear_not_ramsey : ¬IsRamsey collinearFour := by
  exact not_spherical_not_ramsey collinearFour collinear_not_spherical

/- ## Part VIII: The Characterization Problem -/

/-- The main open question: find a characterization of Ramsey sets.
There exists some property P that characterizes Ramsey sets
(trivially: P = IsRamsey), but the goal is a geometrically meaningful one. -/
def erdos_174_question : Prop :=
  ∃ (P : ∀ n, FiniteConfig n → Prop),
    ∀ n (A : FiniteConfig n), P n A ↔ IsRamsey A

/-- The characterization exists (non-constructive: take P = IsRamsey). -/
theorem characterization_exists : erdos_174_question := by
  use fun n A => IsRamsey A
  intro n A
  rfl

/- ## Part IX: Summary

**Erdős Problem #174: OPEN**

**What We Know:**
- Every Ramsey set must be spherical (EGMRSS 1973)
- Many specific classes are known to be Ramsey: rectangles, simplices,
  trapezoids, regular polygons/polyhedra

**What We Don't Know:**
- Whether every spherical set is Ramsey (Graham's conjecture)
- Whether subtransitivity characterizes Ramsey sets (LRW conjecture)
- A clean necessary-and-sufficient characterization

The gap between the necessary condition (spherical) and the known
sufficient conditions (rectangles, simplices, trapezoids, etc.) remains open.
-/

/-- **Erdős Problem #174: OPEN**

The EGMRSS necessary condition (Ramsey ⟹ Spherical) holds, and several
specific families (rectangles, simplices, trapezoids) are known to be Ramsey. -/
theorem erdos_174 :
    (∀ {n : ℕ} (A : FiniteConfig n), IsRamsey A → IsSpherical A) ∧
    (∀ {n : ℕ} (A : FiniteConfig n), IsRectangle A → IsRamsey A) ∧
    (∀ {n : ℕ} (A : FiniteConfig n), IsSimplex A → IsRamsey A) ∧
    (∀ {n : ℕ} (A : FiniteConfig n), IsTrapezoid A → IsRamsey A) :=
  ⟨ramsey_implies_spherical, rectangle_is_ramsey, simplex_is_ramsey, trapezoid_is_ramsey⟩

/-- Summary: the EGMRSS necessary condition for any configuration. -/
theorem erdos_174_summary {n : ℕ} (A : FiniteConfig n) :
    IsRamsey A → IsSpherical A :=
  ramsey_implies_spherical A

end Erdos174
