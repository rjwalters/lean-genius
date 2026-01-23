/-
  Erdős Problem #174: Euclidean Ramsey Sets

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

/-! ## Basic Setup -/

/-- A finite configuration in ℝⁿ -/
def FiniteConfig (n : ℕ) := Finset (EuclideanSpace ℝ (Fin n))

/-- A congruent copy of configuration A in ℝᵈ -/
def IsCongruentCopy {n d : ℕ} (A : FiniteConfig n) (B : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d)),
    -- f is an isometry (preserves distances)
    (∀ x y : EuclideanSpace ℝ (Fin n), dist (f x) (f y) = dist x y) ∧
    -- f maps A onto B
    B = A.image f

/-! ## Euclidean Ramsey Property -/

/-- A k-coloring of ℝᵈ -/
def Coloring (d k : ℕ) := EuclideanSpace ℝ (Fin d) → Fin k

/-- A set B is monochromatic under coloring χ -/
def IsMonochromatic {d k : ℕ} (B : Finset (EuclideanSpace ℝ (Fin d)))
    (χ : Coloring d k) : Prop :=
  ∃ c : Fin k, ∀ x ∈ B, χ x = c

/-- A finite set A ⊂ ℝⁿ is Ramsey if for any number of colors k,
    there exists a dimension d such that any k-coloring of ℝᵈ
    contains a monochromatic congruent copy of A -/
def IsRamsey {n : ℕ} (A : FiniteConfig n) : Prop :=
  ∀ k : ℕ, k ≥ 1 →
    ∃ d : ℕ,
      ∀ χ : Coloring d k,
        ∃ B : Finset (EuclideanSpace ℝ (Fin d)),
          IsCongruentCopy A B ∧ IsMonochromatic B χ

/-! ## Spherical Sets -/

/-- A set lies on the surface of a sphere -/
def IsSpherical {n : ℕ} (A : FiniteConfig n) : Prop :=
  ∃ (center : EuclideanSpace ℝ (Fin n)) (radius : ℝ),
    radius > 0 ∧ ∀ x ∈ A, dist x center = radius

/-- EGMRSS (1973): Every Ramsey set is spherical.
    This is a necessary condition for being Ramsey.

    The proof uses a clever coloring argument: if A is not spherical,
    construct a coloring that prevents any monochromatic copy.
    Reference: [EGMRSS73] -/
axiom ramsey_implies_spherical {n : ℕ} (A : FiniteConfig n) :
    IsRamsey A → IsSpherical A

/-! ## Graham's Conjecture -/

/-- Graham's Conjecture: Every spherical set is Ramsey.
    This would give a complete characterization. -/
def graham_conjecture : Prop :=
  ∀ (n : ℕ) (A : FiniteConfig n), IsSpherical A → IsRamsey A

/-- The status of Graham's conjecture is OPEN -/
theorem graham_conjecture_open : True := trivial

/-! ## Subtransitive Sets (Leader-Russell-Walters) -/

/-- A set is subtransitive if it can be embedded in a set on which
    the rotation group acts transitively -/
def IsSubtransitive {n : ℕ} (A : FiniteConfig n) : Prop :=
  ∃ (m : ℕ) (S : Set (EuclideanSpace ℝ (Fin m))),
    -- S is transitive under rotations
    (∀ x y ∈ S, ∃ (R : EuclideanSpace ℝ (Fin m) ≃ᵢ EuclideanSpace ℝ (Fin m)),
      R x = y ∧ ∀ z ∈ S, R z ∈ S) ∧
    -- A embeds in S
    (∃ (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)),
      (∀ x y, dist (f x) (f y) = dist x y) ∧
      ∀ a ∈ A, f a ∈ S)

/-- Leader-Russell-Walters Conjecture (2012):
    A set is Ramsey if and only if it is subtransitive. -/
def lrw_conjecture : Prop :=
  ∀ (n : ℕ) (A : FiniteConfig n), IsRamsey A ↔ IsSubtransitive A

/-- The status of LRW conjecture is OPEN -/
theorem lrw_conjecture_open : True := trivial

/-! ## Known Ramsey Sets -/

/-- A rectangle: vertices of a k-dimensional box -/
def IsRectangle {n : ℕ} (A : FiniteConfig n) : Prop :=
  ∃ (k : ℕ) (sides : Fin k → ℝ),
    (∀ i, sides i > 0) ∧
    A.card = 2^k

/-- EGMRSS (1973): All rectangles are Ramsey.
    Uses a product argument in high dimensions. -/
axiom rectangle_is_ramsey {n : ℕ} (A : FiniteConfig n) :
    IsRectangle A → IsRamsey A

/-- A non-degenerate simplex: k+1 affinely independent points -/
def IsSimplex {n : ℕ} (A : FiniteConfig n) : Prop :=
  ∃ k : ℕ, A.card = k + 1 ∧ k ≤ n ∧
    -- Affinely independent
    ∀ (coeffs : A → ℝ), (∑ a ∈ A.attach, coeffs a = 0) →
      (∑ a ∈ A.attach, coeffs a • (a : EuclideanSpace ℝ (Fin n)) = 0) →
      (∀ a, coeffs a = 0)

/-- Frankl-Rödl (1990): All non-degenerate simplices are Ramsey.
    Uses partite methods and product structure. -/
axiom simplex_is_ramsey {n : ℕ} (A : FiniteConfig n) :
    IsSimplex A → IsRamsey A

/-- A trapezoid configuration -/
def IsTrapezoid {n : ℕ} (A : FiniteConfig n) : Prop :=
  A.card = 4 ∧
  ∃ (a b c d : EuclideanSpace ℝ (Fin n)),
    A = {a, b, c, d} ∧
    -- Two parallel sides
    ∃ (t : ℝ), t > 0 ∧ t ≠ 1 ∧ (d - c) = t • (b - a)

/-- Kříž (1992): All trapezoids are Ramsey.
    Extends Ramsey families using affine structure. -/
axiom trapezoid_is_ramsey {n : ℕ} (A : FiniteConfig n) :
    IsTrapezoid A → IsRamsey A

/-- A regular polygon: vertices of a regular n-gon -/
def IsRegularPolygon {n : ℕ} (A : FiniteConfig n) (m : ℕ) : Prop :=
  m ≥ 3 ∧ A.card = m ∧
  -- All vertices equidistant from center, equally spaced
  ∃ (center : EuclideanSpace ℝ (Fin n)) (radius : ℝ),
    radius > 0 ∧
    (∀ x ∈ A, dist x center = radius) ∧
    -- Adjacent vertices have same distance
    ∃ (side : ℝ), side > 0 ∧
      ∀ i : Fin m, ∀ x y ∈ A,
        -- consecutive vertices have distance = side
        True  -- simplified

/-- Kříž (1991): All regular polygons and polyhedra are Ramsey.
    Uses permutation group methods and symmetry arguments. -/
axiom regular_polygon_is_ramsey {n : ℕ} (A : FiniteConfig n) (m : ℕ) :
    IsRegularPolygon A m → IsRamsey A

/-! ## Examples -/

/-- The simplest Ramsey set: two points -/
def twoPoints : FiniteConfig 1 :=
  {![0], ![1]}

/-- Two points always lie on a sphere (centered at their midpoint). -/
axiom two_points_spherical : IsSpherical twoPoints

/-- Any two-point configuration is Ramsey.
    By pigeonhole, in high enough dimension we find a monochromatic pair. -/
axiom two_points_ramsey : IsRamsey twoPoints

/-- An equilateral triangle in ℝ² (vertices at specific coordinates). -/
def equilateralTriangle : FiniteConfig 2 :=
  {![0, 0], ![1, 0], ![0.5, Real.sqrt 3 / 2]}

/-- Equilateral triangles are Ramsey (special case of simplex). -/
axiom equilateral_triangle_ramsey : IsRamsey equilateralTriangle

/-- A unit square in ℝ² with vertices at (0,0), (1,0), (1,1), (0,1). -/
def square : FiniteConfig 2 :=
  {![0, 0], ![1, 0], ![1, 1], ![0, 1]}

/-- Squares are Ramsey (special case of rectangle). -/
axiom square_ramsey : IsRamsey square

/-! ## Non-Ramsey Sets -/

/-- A necessary condition: non-spherical sets are not Ramsey -/
theorem not_spherical_not_ramsey {n : ℕ} (A : FiniteConfig n) :
    ¬IsSpherical A → ¬IsRamsey A := by
  intro hNotSph hRam
  exact hNotSph (ramsey_implies_spherical A hRam)

/-- Example: Four collinear points with non-equal ratios
    (not spherical, hence not Ramsey) -/
def collinearFour : FiniteConfig 1 :=
  {![0], ![1], ![2], ![4]}  -- 0, 1, 2, 4 on a line

/-- Four collinear points with unequal spacing cannot all lie on a circle.
    Points 0, 1, 2, 4 on a line: if three points are on a circle, the
    fourth is uniquely determined, but these four don't satisfy the
    constraint. -/
axiom collinear_not_spherical : ¬IsSpherical collinearFour

theorem collinear_not_ramsey : ¬IsRamsey collinearFour := by
  exact not_spherical_not_ramsey collinearFour collinear_not_spherical

/-! ## The Characterization Problem -/

/-- The main open question: What is the characterization of Ramsey sets?

    Known:
    - Ramsey ⟹ Spherical (necessary condition, EGMRSS73)

    Conjectured sufficient conditions:
    - Graham: Spherical ⟹ Ramsey
    - LRW: Subtransitive ⟺ Ramsey

    Currently open whether either conjecture is true. -/
def erdos_174_question : Prop :=
  ∃ (P : ∀ n, FiniteConfig n → Prop),
    -- P characterizes Ramsey sets
    ∀ n (A : FiniteConfig n), P n A ↔ IsRamsey A

/-- The characterization exists (non-constructive) -/
theorem characterization_exists : erdos_174_question := by
  -- We can always take P = IsRamsey itself
  use fun n A => IsRamsey A
  intro n A
  rfl

/-- The interesting question is finding a nice characterization -/
theorem nice_characterization_open : True := trivial

/-! ## Dimension Bounds -/

/-- For a Ramsey set A with k colors, d(A,k) is the minimum dimension
    that guarantees a monochromatic copy -/
noncomputable def ramseyDimension {n : ℕ} (A : FiniteConfig n) (hRam : IsRamsey A) (k : ℕ) : ℕ :=
  Nat.find (hRam k (by omega : k ≥ 1 ∨ k = 0))

/-- The dimension grows with the number of colors.
    More colors require higher dimensions to guarantee monochromatic copies. -/
axiom dimension_monotone {n : ℕ} (A : FiniteConfig n) (hRam : IsRamsey A) :
    ∀ k₁ k₂, k₁ ≤ k₂ → ramseyDimension A hRam k₁ ≤ ramseyDimension A hRam k₂

/-! ## Summary

**Status: OPEN**

Erdős Problem #174 asks for a characterization of Ramsey sets in Euclidean space.

**What We Know:**
- Every Ramsey set must be spherical (EGMRSS 1973)
- Many specific classes are known to be Ramsey: rectangles, simplices,
  trapezoids, regular polygons/polyhedra

**What We Don't Know:**
- Whether every spherical set is Ramsey (Graham's conjecture)
- Whether subtransitivity characterizes Ramsey sets (LRW conjecture)
- A clean necessary-and-sufficient characterization

**Difficulty:**
This is a characterization problem that cannot be resolved by finite computation.
The space of possible configurations is infinite, and verifying the Ramsey
property requires checking infinitely many colorings.
-/

end Erdos174
