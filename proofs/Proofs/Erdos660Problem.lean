/-
  Erdős Problem #660: Distinct Distances in Convex Polyhedra

  Source: https://erdosproblems.com/660
  Status: OPEN

  Statement:
  Let x₁, ..., xₙ ∈ ℝ³ be the vertices of a convex polyhedron.
  Are there at least (1 - o(1)) · n/2 many distinct distances between the xᵢ?

  Background:
  This problem asks whether the vertices of a convex polyhedron in three-dimensional
  space must determine a number of distinct pairwise distances that grows linearly
  with the number of vertices. The conjectured lower bound is (1 - o(1)) · n/2,
  meaning that as n → ∞, the number of distinct distances approaches n/2.

  Related Results:
  - In ℝ² (planar convex polygons), Altman (1963) proved that vertices always
    determine at least n/2 distinct distances.
  - Erdős (1975) claimed Altman proved an even stronger result (≫ n distances)
    but provided no reference.
  - The 3D case remains open and represents a natural generalization.

  Mathematical Context:
  The distinct distances problem is a fundamental topic in combinatorial geometry.
  The general problem (for arbitrary point sets) was posed by Erdős in 1946 and
  resolved by Guth and Katz (2015) who proved Ω(n/log n) distinct distances for
  n points in the plane. For structured point sets like convex polygon/polyhedron
  vertices, stronger bounds are expected due to geometric constraints.

  References:
  - [Al63] Altman, E., "On a problem of P. Erdős", Amer. Math. Monthly (1963), 148-157.
  - [Er75f] Erdős, P., "On some problems of elementary and combinatorial geometry",
           Ann. Mat. Pura Appl. (4) (1975), 99-108.
-/

import Mathlib

namespace Erdos660

/-! ## Basic Definitions -/

/-- A point in three-dimensional Euclidean space -/
abbrev Point3D := EuclideanSpace ℝ (Fin 3)

/-- The Euclidean distance between two points in ℝ³ -/
noncomputable def euclideanDist (p q : Point3D) : ℝ :=
  dist p q

/-- A finite set of points forms the vertices of a convex polyhedron if their
    convex hull has the points as its extreme points (vertices). -/
def IsConvexPolyhedronVertices (S : Finset Point3D) : Prop :=
  S.Nonempty ∧
  (∀ p ∈ S, p ∈ Set.extremePoints ℝ (convexHull ℝ (S : Set Point3D))) ∧
  (convexHull ℝ (S : Set Point3D)).Nonempty

/-- The set of all pairwise distances between points in a finite set -/
noncomputable def pairwiseDistances (S : Finset Point3D) : Finset ℝ :=
  (S.product S).image (fun pq => euclideanDist pq.1 pq.2)

/-- The number of distinct positive distances (excluding self-distances of 0) -/
noncomputable def distinctDistances (S : Finset Point3D) : ℕ :=
  ((pairwiseDistances S).filter (· > 0)).card

/-! ## Two-Dimensional Analogue (Altman's Result) -/

/-- A point in two-dimensional Euclidean space -/
abbrev Point2D := EuclideanSpace ℝ (Fin 2)

/-- A set forms convex polygon vertices in 2D -/
def IsConvexPolygonVertices (S : Finset Point2D) : Prop :=
  S.Nonempty ∧
  (∀ p ∈ S, p ∈ Set.extremePoints ℝ (convexHull ℝ (S : Set Point2D)))

/-- Pairwise distances for 2D points -/
noncomputable def pairwiseDistances2D (S : Finset Point2D) : Finset ℝ :=
  (S.product S).image (fun pq => dist pq.1 pq.2)

/-- Distinct distances for 2D point set -/
noncomputable def distinctDistances2D (S : Finset Point2D) : ℕ :=
  ((pairwiseDistances2D S).filter (· > 0)).card

/-- Altman's Theorem (1963): The vertices of a convex polygon in ℝ²
    determine at least ⌊n/2⌋ distinct distances.

    This is the solved 2D analogue of Erdős Problem #660. -/
theorem altman_convex_polygon_distances
    (S : Finset Point2D)
    (hConvex : IsConvexPolygonVertices S)
    (hn : S.card ≥ 3) :
    distinctDistances2D S ≥ S.card / 2 := by
  sorry -- Altman (1963)

/-! ## The Main Conjecture (Open Problem) -/

/-- The little-o notation: f(n) = o(g(n)) means f(n)/g(n) → 0 as n → ∞ -/
def IsLittleO (f g : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, g n ≠ 0 → |f n / g n| < ε

/-- Erdős Problem #660 (OPEN): For vertices of a convex polyhedron in ℝ³,
    the number of distinct distances is at least (1 - o(1)) · n/2.

    More precisely: there exists a function ε : ℕ → ℝ with ε(n) → 0
    such that any n vertices of a convex polyhedron determine at least
    (1 - ε(n)) · n/2 distinct distances. -/
theorem erdos_660_conjecture
    (S : Finset Point3D)
    (hConvex : IsConvexPolyhedronVertices S)
    (hn : S.card ≥ 4) :
    ∃ (ε : ℕ → ℝ), IsLittleO ε (fun _ => 1) ∧
      (distinctDistances S : ℝ) ≥ (1 - ε S.card) * (S.card / 2) := by
  sorry -- OPEN PROBLEM

/-! ## Weaker Bounds and Partial Results -/

/-- A trivial lower bound: any n ≥ 2 points determine at least 1 distinct distance -/
theorem trivial_lower_bound
    (S : Finset Point3D)
    (hn : S.card ≥ 2) :
    distinctDistances S ≥ 1 := by
  unfold distinctDistances
  obtain ⟨p, hp, q, hq, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  have hmem : euclideanDist p q ∈ (pairwiseDistances S).filter (· > 0) := by
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · simp only [pairwiseDistances, Finset.mem_image]
      exact ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, rfl⟩
    · simpa [euclideanDist] using dist_pos.mpr hne
  exact Finset.card_pos.mpr ⟨_, hmem⟩

/-! ### Verified base cases

These small cases are fully machine-checked (no `sorry`). They pin down the
behaviour of `distinctDistances` on empty, singleton, and two-point sets, and
record that the count is monotone under adding vertices — the structural facts
any lower-bound argument for the main conjecture must respect. -/

/-- The empty configuration has no pairwise distances. -/
theorem pairwiseDistances_empty :
    pairwiseDistances (∅ : Finset Point3D) = ∅ := by
  simp [pairwiseDistances]

/-- The empty configuration has zero distinct distances. -/
theorem distinctDistances_empty :
    distinctDistances (∅ : Finset Point3D) = 0 := by
  simp [distinctDistances, pairwiseDistances_empty]

/-- A single point determines only the zero self-distance. -/
theorem pairwiseDistances_singleton (p : Point3D) :
    pairwiseDistances {p} = {0} := by
  simp [pairwiseDistances, euclideanDist, dist_self]

/-- A single point has zero distinct (positive) distances. -/
theorem distinctDistances_singleton (p : Point3D) :
    distinctDistances {p} = 0 := by
  simp [distinctDistances, pairwiseDistances_singleton]

/-- Two distinct points determine exactly one distinct distance. -/
theorem two_point_one_distance (p q : Point3D) (hne : p ≠ q) :
    distinctDistances {p, q} = 1 := by
  have hpq : (0 : ℝ) < euclideanDist p q := dist_pos.mpr hne
  have h1 : pairwiseDistances {p, q} = {0, euclideanDist p q} := by
    ext d
    constructor
    · intro hd
      simp only [pairwiseDistances, Finset.mem_image] at hd
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := hd
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rw [Finset.mem_insert, Finset.mem_singleton]
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact Or.inl (by simp [euclideanDist])
      · exact Or.inr rfl
      · exact Or.inr (by simp [euclideanDist, dist_comm])
      · exact Or.inl (by simp [euclideanDist])
    · intro hd
      simp only [pairwiseDistances, Finset.mem_image]
      rw [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl
      · exact ⟨(p, p), Finset.mem_product.mpr
          ⟨Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩, by simp [euclideanDist]⟩
      · exact ⟨(p, q), Finset.mem_product.mpr
          ⟨Finset.mem_insert_self _ _,
            Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩, rfl⟩
  unfold distinctDistances
  rw [h1]
  have h2 : ({0, euclideanDist p q} : Finset ℝ).filter (· > 0)
      = {euclideanDist p q} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
      gt_iff_lt]
    constructor
    · rintro ⟨rfl | rfl, hd⟩
      · exact absurd hd (lt_irrefl 0)
      · rfl
    · rintro rfl
      exact ⟨Or.inr rfl, hpq⟩
  rw [h2, Finset.card_singleton]

/-- Distinct distances are monotone: adding vertices never decreases the count. -/
theorem distinctDistances_mono {S T : Finset Point3D} (h : S ⊆ T) :
    distinctDistances S ≤ distinctDistances T := by
  unfold distinctDistances
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  unfold pairwiseDistances
  exact Finset.image_subset_image (Finset.product_subset_product h h)

/-- Conjecture: Linear lower bound without the precise constant.
    The vertices of a convex polyhedron in ℝ³ determine Ω(n) distinct distances. -/
theorem linear_lower_bound_conjecture
    (S : Finset Point3D)
    (hConvex : IsConvexPolyhedronVertices S)
    (hn : S.card ≥ 4) :
    ∃ (c : ℝ), c > 0 ∧ (distinctDistances S : ℝ) ≥ c * S.card := by
  sorry -- OPEN (weaker form of the conjecture)

/-! ## Special Cases and Constructions -/

/-- The regular tetrahedron has 4 vertices and exactly 1 distinct distance -/
theorem regular_tetrahedron_distances :
    ∃ (S : Finset Point3D), S.card = 4 ∧
      IsConvexPolyhedronVertices S ∧
      distinctDistances S = 1 := by
  sorry

/-- The cube has 8 vertices and exactly 3 distinct distances
    (edge length, face diagonal, space diagonal) -/
theorem cube_distances :
    ∃ (S : Finset Point3D), S.card = 8 ∧
      IsConvexPolyhedronVertices S ∧
      distinctDistances S = 3 := by
  sorry

/-- The regular octahedron has 6 vertices and exactly 2 distinct distances -/
theorem regular_octahedron_distances :
    ∃ (S : Finset Point3D), S.card = 6 ∧
      IsConvexPolyhedronVertices S ∧
      distinctDistances S = 2 := by
  sorry

/-- The regular dodecahedron has 20 vertices -/
theorem regular_dodecahedron_vertices :
    ∃ (S : Finset Point3D), S.card = 20 ∧
      IsConvexPolyhedronVertices S := by
  sorry

/-- The regular icosahedron has 12 vertices -/
theorem regular_icosahedron_vertices :
    ∃ (S : Finset Point3D), S.card = 12 ∧
      IsConvexPolyhedronVertices S := by
  sorry

/-! ## Related: General Distinct Distances Problem -/

/-- Guth-Katz Theorem (2015): Any n points in ℝ² determine Ω(n/log n)
    distinct distances. This is tight up to the logarithmic factor. -/
theorem guth_katz_distinct_distances
    (S : Finset Point2D)
    (hn : S.card ≥ 2) :
    ∃ (c : ℝ), c > 0 ∧
      (distinctDistances2D S : ℝ) ≥ c * S.card / Real.log S.card := by
  sorry -- Guth-Katz (2015)

end Erdos660
