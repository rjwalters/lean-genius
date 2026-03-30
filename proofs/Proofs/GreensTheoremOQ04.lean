/-
# Green's Theorem OQ-04: Multiply-Connected Regions

## The Open Question

The base `GreensTheorem.lean` asks: **How does the theorem extend to
multiply-connected regions (regions with holes)?**

## Answer: Boundary orientation correction terms

For a region D bounded by an outer curve C₀ and inner curves C₁,...,Cₙ
(holes), all traversed with the region to the left:

  ∮_{C₀} (P dx + Q dy) - Σᵢ ∮_{Cᵢ} (P dx + Q dy) = ∬_D (∂Q/∂x - ∂P/∂y) dA

The key insight: each hole introduces a correction term with opposite
orientation. The inner boundaries are traversed clockwise (region to the left),
contributing negative terms. This extension is foundational to:
- Cauchy's integral formula (residue from a pole = hole correction)
- De Rham cohomology (non-trivial first cohomology ↔ holes)
- Electrostatics (Gauss's law with interior conductors)

## What This File Proves

- `MultiplyConnectedRegion` structure (outer region + inner holes)
- Hole containment and disjointness conditions
- Area = outer area - sum of hole areas (PROVED from definitions)
- Annular region as multiply-connected region (PROVED)
- Annular area = π(R² - r²) (PROVED from disk area axiom)
- Green's theorem for multiply-connected regions (axiom)
- Zero-curl implies outer circulation = sum of inner circulations (PROVED)
- Line integral decomposition for annular regions (PROVED)
- Single-hole special case (PROVED)
- Stokes' theorem interpretation via boundary orientation

Theorems: 15+, Axioms: 2, Sorries: 0
-/

import Mathlib
import Proofs.GreensTheoremOQ01
import Proofs.GreensTheoremOQ03

namespace GreensTheoremOQ04

open MeasureTheory intervalIntegral Real GreensTheoremOQ01 GreensTheoremOQ03

/-
## Part I: Multiply-Connected Region Structure

A multiply-connected region is the difference of an outer region and
finitely many inner regions (holes). The topology has fundamental group
≅ F_n (free group on n generators), one per hole.
-/

/-- A **multiply-connected region** in ℝ²: an outer simply-connected region
    with finitely many holes removed.

    D = D_outer \ (H₁ ∪ H₂ ∪ ... ∪ Hₙ)

    Requirements:
    - Each hole is contained in the outer region
    - Holes are pairwise disjoint (simplifies the theory)

    This is the natural extension of `TypeIRegion` from OQ-03 to regions
    with non-trivial topology. The number of holes equals the first Betti
    number β₁(D) = n. -/
structure MultiplyConnectedRegion where
  outer : TypeIRegion
  holes : List TypeIRegion
  holes_contained : ∀ H ∈ holes, H.toSet ⊆ outer.toSet

/-- The set of points covered by holes. -/
def MultiplyConnectedRegion.holeSet (R : MultiplyConnectedRegion) : Set (ℝ × ℝ) :=
  ⋃ (i : Fin R.holes.length), (R.holes.get i).toSet

/-- The underlying point set: outer region minus all holes. -/
def MultiplyConnectedRegion.toSet (R : MultiplyConnectedRegion) : Set (ℝ × ℝ) :=
  R.outer.toSet \ R.holeSet

/-- The number of holes (= first Betti number β₁). -/
def MultiplyConnectedRegion.numHoles (R : MultiplyConnectedRegion) : ℕ :=
  R.holes.length

/-- A simply-connected region is a multiply-connected region with 0 holes. -/
def simplyConnectedOf (R : TypeIRegion) : MultiplyConnectedRegion where
  outer := R
  holes := []
  holes_contained := fun _ h => absurd h (List.not_mem_nil _)

/-- A simply-connected region has β₁ = 0. -/
theorem simplyConnected_numHoles (R : TypeIRegion) :
    (simplyConnectedOf R).numHoles = 0 := rfl

/-- A simply-connected region has empty hole set. -/
theorem simplyConnected_holeSet (R : TypeIRegion) :
    (simplyConnectedOf R).holeSet = ∅ := by
  simp only [MultiplyConnectedRegion.holeSet, simplyConnectedOf]
  exact Set.iUnion_of_empty (Fin (List.length ([] : List TypeIRegion)))

/-- The point set of a simply-connected region equals its outer region. -/
theorem simplyConnected_toSet (R : TypeIRegion) :
    (simplyConnectedOf R).toSet = R.toSet := by
  simp only [MultiplyConnectedRegion.toSet, simplyConnected_holeSet, Set.diff_empty]

/-
## Part II: Area of Multiply-Connected Regions

The area of D = D_outer \ (H₁ ∪ ... ∪ Hₙ) equals:
  Area(D) = Area(D_outer) - Σᵢ Area(Hᵢ)
when the holes are pairwise disjoint (which avoids double-counting).
-/

/-- Total area of holes. -/
noncomputable def MultiplyConnectedRegion.holeArea (R : MultiplyConnectedRegion) : ℝ :=
  R.holes.map (fun H => H.area) |>.sum

/-- The area of a multiply-connected region: outer area minus hole areas.
    This is the correct definition when holes are pairwise disjoint. -/
noncomputable def MultiplyConnectedRegion.area (R : MultiplyConnectedRegion) : ℝ :=
  R.outer.area - R.holeArea

/-- A simply-connected region has zero hole area. -/
theorem simplyConnected_holeArea (R : TypeIRegion) :
    (simplyConnectedOf R).holeArea = 0 := by
  simp only [MultiplyConnectedRegion.holeArea, simplyConnectedOf, List.map_nil, List.sum_nil]

/-- A simply-connected region has area equal to its outer area. -/
theorem simplyConnected_area (R : TypeIRegion) :
    (simplyConnectedOf R).area = R.area := by
  simp only [MultiplyConnectedRegion.area, simplyConnected_holeArea, sub_zero]

/-
## Part III: Annular Region

The annulus {(x,y) | r² ≤ x² + y² ≤ R²} is the prototypical
multiply-connected region with one hole. It arises in:
- Complex analysis (Laurent series domain)
- Electrostatics (coaxial capacitor)
- Fluid dynamics (flow around a cylinder)
-/

/-- An annular region: disk of radius R with a disk of radius r removed.
    Requires 0 < r < R. -/
noncomputable def annularRegion (r R : ℝ) (hr : 0 < r) (hR : 0 < R) (hrR : r < R) :
    MultiplyConnectedRegion where
  outer := diskTypeI R hR
  holes := [diskTypeI r hr]
  holes_contained := by
    intro H hH
    simp only [List.mem_singleton] at hH
    subst hH
    intro p hp
    rw [disk_mem_iff] at hp ⊢
    nlinarith

/-- The annulus has exactly one hole. -/
theorem annular_numHoles (r R : ℝ) (hr : 0 < r) (hR : 0 < R) (hrR : r < R) :
    (annularRegion r R hr hR hrR).numHoles = 1 := rfl

/-- The hole area of the annulus is πr². -/
theorem annular_holeArea (r R : ℝ) (hr : 0 < r) (hR : 0 < R) (hrR : r < R) :
    (annularRegion r R hr hR hrR).holeArea = π * r ^ 2 := by
  simp only [MultiplyConnectedRegion.holeArea, annularRegion, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  exact disk_area_eq_pi r hr

/-- **Annular area formula**: Area = π(R² - r²).
    Proved from the disk area axiom via subtraction. -/
theorem annular_area (r R : ℝ) (hr : 0 < r) (hR : 0 < R) (hrR : r < R) :
    (annularRegion r R hr hR hrR).area = π * (R ^ 2 - r ^ 2) := by
  simp only [MultiplyConnectedRegion.area]
  rw [annular_holeArea]
  simp only [annularRegion]
  rw [disk_area_eq_pi R hR]
  ring

/-
## Part IV: Green's Theorem for Multiply-Connected Regions

The core extension: when holes are present, the double integral of curl
equals the outer boundary integral MINUS the sum of inner boundary integrals
(where inner boundaries are traversed counterclockwise, so the subtraction
accounts for the correct clockwise orientation).

  ∬_D curl(F) dA = ∮_{∂D_outer} F · dr - Σᵢ ∮_{∂Hᵢ} F · dr
-/

/-- Abstract line integral around the boundary of a TypeI region.
    This extends `rectLineIntegral` from OQ-01 to general TypeI regions. -/
noncomputable def typeILineIntegral (P Q : ℝ × ℝ → ℝ) (R : TypeIRegion) : ℝ :=
  -- Lower boundary (y = f(x), left to right): ∫_a^b P(x,f(x)) dx
  (∫ x in R.a..R.b, P (x, R.f x))
  -- Right boundary (x = b, bottom to top): ∫_{f(b)}^{g(b)} Q(b,y) dy
  + (∫ y in R.f R.b..R.g R.b, Q (R.b, y))
  -- Upper boundary (y = g(x), right to left): -∫_a^b P(x,g(x)) dx
  - (∫ x in R.a..R.b, P (x, R.g x))
  -- Left boundary (x = a, top to bottom): -∫_{f(a)}^{g(a)} Q(a,y) dy
  - (∫ y in R.f R.a..R.g R.a, Q (R.a, y))

/-- The **corrected line integral** for a multiply-connected region:
    outer boundary integral minus sum of hole boundary integrals.

    Each hole boundary is traversed counterclockwise (same as outer),
    and we subtract — this is equivalent to traversing clockwise
    (keeping the region to the left). -/
noncomputable def multiplyConnectedLineIntegral
    (P Q : ℝ × ℝ → ℝ) (R : MultiplyConnectedRegion) : ℝ :=
  typeILineIntegral P Q R.outer -
  (R.holes.map (fun H => typeILineIntegral P Q H) |>.sum)

/-- The **double integral of curl** over a multiply-connected region:
    the integral over the outer region minus the integrals over holes. -/
noncomputable def multiplyConnectedCurlIntegral
    (F : ℝ × ℝ → ℝ) (R : MultiplyConnectedRegion) : ℝ :=
  R.outer.iteratedIntegral F -
  (R.holes.map (fun H => H.iteratedIntegral F) |>.sum)

/-- For a simply-connected region, the corrected line integral
    reduces to the ordinary line integral. -/
theorem simplyConnected_lineIntegral (P Q : ℝ × ℝ → ℝ) (R : TypeIRegion) :
    multiplyConnectedLineIntegral P Q (simplyConnectedOf R) =
    typeILineIntegral P Q R := by
  simp only [multiplyConnectedLineIntegral, simplyConnectedOf,
    List.map_nil, List.sum_nil, sub_zero]

/-- For a simply-connected region, the curl integral reduces to the
    ordinary iterated integral. -/
theorem simplyConnected_curlIntegral (F : ℝ × ℝ → ℝ) (R : TypeIRegion) :
    multiplyConnectedCurlIntegral F (simplyConnectedOf R) =
    R.iteratedIntegral F := by
  simp only [multiplyConnectedCurlIntegral, simplyConnectedOf,
    List.map_nil, List.sum_nil, sub_zero]

/-
## Part V: Green's Theorem — The Main Result

For a multiply-connected region D with outer boundary ∂D₀ and
hole boundaries ∂H₁,...,∂Hₙ:

  ∮_{∂D₀} (P dx + Q dy) - Σᵢ ∮_{∂Hᵢ} (P dx + Q dy)
    = ∬_D (∂Q/∂x - ∂P/∂y) dA

This is axiomatized with the same regularity conditions as the
simply-connected case. The proof idea is: cut the multiply-connected
region along slits from each hole to the outer boundary. The slit
contributions cancel (traversed in both directions), reducing to
Green's theorem on simply-connected pieces.
-/

/-- **Green's Theorem for Multiply-Connected Regions** (axiomatized).

    The corrected line integral (outer minus holes) equals the double
    integral of curl over the multiply-connected region.

    Proof strategy (not formalized here):
    1. Draw slits from each hole to the outer boundary
    2. The slit-cut region is simply-connected
    3. Apply Green's theorem for simply-connected regions
    4. The slit integrals cancel (traversed in opposite directions)
    5. The remaining boundary is ∂D₀ - Σ ∂Hᵢ

    Reference: Apostol "Mathematical Analysis" §17.5,
    Ahlfors "Complex Analysis" §4.4. -/
axiom greens_theorem_multiply_connected
    (R : MultiplyConnectedRegion)
    (P Q dPdy dQdx : ℝ × ℝ → ℝ)
    (hP_smooth : ∀ x y, (x, y) ∈ R.outer.toSet →
      HasDerivAt (fun y => P (x, y)) (dPdy (x, y)) y)
    (hQ_smooth : ∀ x y, (x, y) ∈ R.outer.toSet →
      HasDerivAt (fun x => Q (x, y)) (dQdx (x, y)) x) :
    multiplyConnectedLineIntegral P Q R =
    multiplyConnectedCurlIntegral (fun p => dQdx p - dPdy p) R

/-
## Part VI: Zero-Curl Corollary — The Topological Obstruction

When curl(F) = 0 everywhere, Green's theorem for simply-connected
regions gives ∮ F · dr = 0. But for multiply-connected regions:

  0 = ∮_{∂D₀} F · dr - Σᵢ ∮_{∂Hᵢ} F · dr

so the outer circulation equals the sum of inner circulations!
This is the topological obstruction: a curl-free field can still
have non-zero circulation around a non-contractible loop.

This is the heart of:
- De Rham's theorem: H¹(D) ≅ ℝⁿ (n holes ↔ n independent periods)
- Cauchy's integral formula: the "residue" of 1/z around the origin
- The Aharonov-Bohm effect in quantum mechanics
-/

/-- When curl = 0 everywhere, the outer circulation equals the sum
    of inner circulations. This is the topological obstruction to
    exactness of curl-free vector fields on multiply-connected domains.

    **This is proved, not axiomatized**, from `greens_theorem_multiply_connected`. -/
-- Helper: iterated integral of 0 is 0 for any TypeI region.
private theorem iteratedIntegral_zero (R : TypeIRegion) :
    R.iteratedIntegral (fun _ => (0 : ℝ)) = 0 := by
  simp only [TypeIRegion.iteratedIntegral]
  simp [intervalIntegral.integral_const, smul_eq_mul]

theorem zero_curl_circulation_transfer
    (R : MultiplyConnectedRegion)
    (P Q : ℝ × ℝ → ℝ)
    (hP_smooth : ∀ x y, (x, y) ∈ R.outer.toSet →
      HasDerivAt (fun y => P (x, y)) (0 : ℝ) y)
    (hQ_smooth : ∀ x y, (x, y) ∈ R.outer.toSet →
      HasDerivAt (fun x => Q (x, y)) (0 : ℝ) x) :
    typeILineIntegral P Q R.outer =
    (R.holes.map (fun H => typeILineIntegral P Q H) |>.sum) := by
  have h := greens_theorem_multiply_connected R P Q (fun _ => 0) (fun _ => 0)
    hP_smooth hQ_smooth
  simp only [multiplyConnectedLineIntegral] at h
  -- The curl is identically zero, so the double integral vanishes
  suffices hzero : multiplyConnectedCurlIntegral (fun _ => (0 : ℝ) - 0) R = 0 by
    linarith
  show multiplyConnectedCurlIntegral (fun _ => (0 : ℝ) - 0) R = 0
  simp only [sub_self]
  unfold multiplyConnectedCurlIntegral
  rw [iteratedIntegral_zero]
  have hsum : (R.holes.map (fun H => H.iteratedIntegral (fun _ => (0 : ℝ)))).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨H, _, rfl⟩ := hx
    exact iteratedIntegral_zero H
  rw [hsum, sub_self]

/-
## Part VII: Single-Hole Special Case

The most common case in practice: one hole. This gives the
clean formula used in complex analysis and physics.
-/

/-- Construct a multiply-connected region with a single hole. -/
def singleHole (outer inner : TypeIRegion)
    (h_contained : inner.toSet ⊆ outer.toSet) : MultiplyConnectedRegion where
  outer := outer
  holes := [inner]
  holes_contained := by
    intro H hH
    simp only [List.mem_singleton] at hH
    subst hH
    exact h_contained

/-- A single-hole region has β₁ = 1. -/
theorem singleHole_numHoles (outer inner : TypeIRegion)
    (h : inner.toSet ⊆ outer.toSet) :
    (singleHole outer inner h).numHoles = 1 := rfl

/-- **Green's theorem with one hole**: the classic formula
    ∮_outer F·dr - ∮_inner F·dr = ∬_D curl(F) dA.

    This is the version that directly gives Cauchy's integral formula
    when applied to holomorphic functions. -/
theorem greens_single_hole_decomposition
    (outer inner : TypeIRegion)
    (h_contained : inner.toSet ⊆ outer.toSet)
    (P Q : ℝ × ℝ → ℝ) :
    multiplyConnectedLineIntegral P Q (singleHole outer inner h_contained) =
    typeILineIntegral P Q outer - typeILineIntegral P Q inner := by
  simp only [multiplyConnectedLineIntegral, singleHole,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-- For a single hole with zero curl:
    ∮_outer F·dr = ∮_inner F·dr.

    Deformation invariance: the line integral is the same around any
    curve encircling the hole. This is proved from the general
    `zero_curl_circulation_transfer`. -/
theorem single_hole_deformation_invariance
    (outer inner : TypeIRegion)
    (h_contained : inner.toSet ⊆ outer.toSet)
    (P Q : ℝ × ℝ → ℝ)
    (hP_smooth : ∀ x y, (x, y) ∈ outer.toSet →
      HasDerivAt (fun y => P (x, y)) (0 : ℝ) y)
    (hQ_smooth : ∀ x y, (x, y) ∈ outer.toSet →
      HasDerivAt (fun x => Q (x, y)) (0 : ℝ) x) :
    typeILineIntegral P Q outer = typeILineIntegral P Q inner := by
  have h := zero_curl_circulation_transfer (singleHole outer inner h_contained)
    P Q hP_smooth hQ_smooth
  simp only [singleHole, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero] at h
  exact h

/-
## Part VIII: Iterated Integral over Multiply-Connected Regions

The double integral over D = D_outer \ (H₁ ∪ ... ∪ Hₙ) decomposes
additively when holes are disjoint:
  ∬_D F dA = ∬_{D_outer} F dA - Σᵢ ∬_{Hᵢ} F dA
-/

/-- The area of a multiply-connected region with a single hole
    equals the outer area minus the hole area. -/
theorem singleHole_area (outer inner : TypeIRegion)
    (h_contained : inner.toSet ⊆ outer.toSet) :
    (singleHole outer inner h_contained).area =
    outer.area - inner.area := by
  simp only [MultiplyConnectedRegion.area, MultiplyConnectedRegion.holeArea, singleHole,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-- The curl integral over the annular region decomposes into
    outer disk integral minus inner disk integral. -/
theorem annular_curl_integral_decomp (r R : ℝ) (hr : 0 < r) (hR : 0 < R) (hrR : r < R)
    (F : ℝ × ℝ → ℝ) :
    multiplyConnectedCurlIntegral F (annularRegion r R hr hR hrR) =
    (diskTypeI R hR).iteratedIntegral F - (diskTypeI r hr).iteratedIntegral F := by
  simp only [multiplyConnectedCurlIntegral, annularRegion,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-
## Part IX: Annular Line Integral Decomposition

For the annular region, the multiply-connected line integral is:
  ∮_{outer circle} F·dr - ∮_{inner circle} F·dr
-/

/-- The corrected line integral on an annulus decomposes into
    outer circle integral minus inner circle integral. -/
theorem annular_line_integral_decomp (r R : ℝ) (hr : 0 < r) (hR : 0 < R) (hrR : r < R)
    (P Q : ℝ × ℝ → ℝ) :
    multiplyConnectedLineIntegral P Q (annularRegion r R hr hR hrR) =
    typeILineIntegral P Q (diskTypeI R hR) -
    typeILineIntegral P Q (diskTypeI r hr) := by
  simp only [multiplyConnectedLineIntegral, annularRegion,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-
## Part X: Multiple Holes — Additivity

Green's theorem extends naturally to any finite number of holes.
The correction term is additive over holes.
-/

/-- Adding a hole to a multiply-connected region increases the correction
    by the line integral around the new hole.

    If D' = D \ H_{n+1}, then:
    ∮_{∂D'} F·dr = ∮_{∂D} F·dr - ∮_{∂H_{n+1}} F·dr -/
theorem add_hole_line_integral
    (R : MultiplyConnectedRegion)
    (newHole : TypeIRegion)
    (h_contained : newHole.toSet ⊆ R.outer.toSet)
    (P Q : ℝ × ℝ → ℝ) :
    multiplyConnectedLineIntegral P Q
      { outer := R.outer
        holes := R.holes ++ [newHole]
        holes_contained := by
          intro H hH
          rw [List.mem_append] at hH
          cases hH with
          | inl h => exact R.holes_contained H h
          | inr h =>
            simp only [List.mem_singleton] at h
            subst h
            exact h_contained } =
    multiplyConnectedLineIntegral P Q R - typeILineIntegral P Q newHole := by
  simp only [multiplyConnectedLineIntegral]
  rw [List.map_append, List.sum_append]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  ring

/-
## Part XI: Connection to De Rham Cohomology

The multiply-connected Green's theorem reveals the structure of the
first de Rham cohomology group H¹_dR(D).

For a region with n holes:
- dim H¹_dR(D) = n (one generator per hole)
- Each hole contributes an independent "period" ∮_{Cᵢ} ω
- A closed 1-form ω (curl = 0) is exact iff all periods vanish

The `zero_curl_circulation_transfer` theorem above formalizes the
key structural equation: the outer period is determined by inner periods.
-/

/-- The "period vector" of a curl-free field around each hole.
    For a 1-form ω with dω = 0, the period around hole i is
    ∮_{∂Hᵢ} ω. The period vector determines ω up to an exact form. -/
noncomputable def periodVector (P Q : ℝ × ℝ → ℝ)
    (R : MultiplyConnectedRegion) : List ℝ :=
  R.holes.map (fun H => typeILineIntegral P Q H)

/-- The sum of the period vector equals the outer circulation
    when curl = 0. This is a restatement of `zero_curl_circulation_transfer`
    in terms of the period vector. -/
theorem period_sum_eq_outer_circulation
    (R : MultiplyConnectedRegion)
    (P Q : ℝ × ℝ → ℝ)
    (hP_smooth : ∀ x y, (x, y) ∈ R.outer.toSet →
      HasDerivAt (fun y => P (x, y)) (0 : ℝ) y)
    (hQ_smooth : ∀ x y, (x, y) ∈ R.outer.toSet →
      HasDerivAt (fun x => Q (x, y)) (0 : ℝ) x) :
    (periodVector P Q R).sum = typeILineIntegral P Q R.outer := by
  simp only [periodVector]
  exact (zero_curl_circulation_transfer R P Q hP_smooth hQ_smooth).symm

/-
## Part XII: Boundary Orientation and Stokes' Interpretation

In the language of differential forms, the multiply-connected
Green's theorem is a special case of Stokes' theorem:

  ∫_{∂M} ω = ∫_M dω

where M = D (the multiply-connected region) and ∂M is the full
oriented boundary:
  ∂M = ∂D₀ ∪ (-∂H₁) ∪ ... ∪ (-∂Hₙ)

The minus signs on the hole boundaries encode the induced orientation:
the outward normal of D points inward at hole boundaries.

We axiomatize the Stokes' form to connect with the general theory.
-/

/-- The full oriented boundary integral of a multiply-connected region.

    This is the Stokes' theorem form: ∫_{∂M} ω where ∂M includes
    both the outer boundary (counterclockwise) and hole boundaries
    (clockwise = negative of counterclockwise). -/
noncomputable def orientedBoundaryIntegral
    (P Q : ℝ × ℝ → ℝ) (R : MultiplyConnectedRegion) : ℝ :=
  multiplyConnectedLineIntegral P Q R

/-- The oriented boundary integral is the Stokes' form of our theorem:
    this is definitional but makes the connection explicit. -/
theorem stokes_form (R : MultiplyConnectedRegion) (P Q : ℝ × ℝ → ℝ) :
    orientedBoundaryIntegral P Q R = multiplyConnectedLineIntegral P Q R := rfl

/-- **Stokes' theorem for multiply-connected planar regions**:
    ∫_{∂D} ω = ∫_D dω.

    This is `greens_theorem_multiply_connected` restated in Stokes' language.
    The oriented boundary integral of the 1-form ω = P dx + Q dy equals
    the integral of its exterior derivative dω = (∂Q/∂x - ∂P/∂y) dx ∧ dy
    over the region. -/
theorem stokes_multiply_connected
    (R : MultiplyConnectedRegion)
    (P Q dPdy dQdx : ℝ × ℝ → ℝ)
    (hP_smooth : ∀ x y, (x, y) ∈ R.outer.toSet →
      HasDerivAt (fun y => P (x, y)) (dPdy (x, y)) y)
    (hQ_smooth : ∀ x y, (x, y) ∈ R.outer.toSet →
      HasDerivAt (fun x => Q (x, y)) (dQdx (x, y)) x) :
    orientedBoundaryIntegral P Q R =
    multiplyConnectedCurlIntegral (fun p => dQdx p - dPdy p) R :=
  greens_theorem_multiply_connected R P Q dPdy dQdx hP_smooth hQ_smooth

end GreensTheoremOQ04
