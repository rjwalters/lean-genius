/-!
# Erdős Problem #1071 — Maximal Packings of Unit Segments in the Unit Square

Erdős and Tóth asked two questions about unit line segments in [0,1]²:

(a) SOLVED (Danzer, $10 prize): Is there a finite maximal set of pairwise
    non-intersecting unit segments in the unit square?

(b) OPEN: Is there a region R with a countably infinite maximal set of
    pairwise disjoint unit segments?

A set S of unit segments is maximal if no additional unit segment can
be added while maintaining the disjointness property.

Reference: https://erdosproblems.com/1071
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic

/-! ## Segment Abstractions -/

/-- A unit segment in ℝ², represented by its two endpoints -/
structure UnitSegment where
  x1 : ℚ × ℚ
  x2 : ℚ × ℚ
  -- The endpoints are at distance 1 apart (abstracted)
  unit_length : True

/-- A point lies in the unit square [0,1]² -/
def InUnitSquare (p : ℚ × ℚ) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1

/-- A unit segment lies in the unit square -/
def SegmentInSquare (s : UnitSegment) : Prop :=
  InUnitSquare s.x1 ∧ InUnitSquare s.x2

/-- Two segments are interior-disjoint (do not intersect except possibly at endpoints) -/
axiom AreDisjoint : UnitSegment → UnitSegment → Prop

/-- Disjointness is symmetric -/
axiom disjoint_symm (s t : UnitSegment) : AreDisjoint s t → AreDisjoint t s

/-! ## Packing Definitions -/

/-- A packing: a set of pairwise disjoint unit segments in the unit square -/
def IsPacking (S : Set UnitSegment) : Prop :=
  (∀ s ∈ S, SegmentInSquare s) ∧
  (∀ s ∈ S, ∀ t ∈ S, s ≠ t → AreDisjoint s t)

/-- A packing is maximal if no additional unit segment can be added -/
def IsMaximalPacking (S : Set UnitSegment) : Prop :=
  IsPacking S ∧
  ∀ s : UnitSegment, SegmentInSquare s → s ∉ S →
    ∃ t ∈ S, ¬AreDisjoint s t

/-- A finite packing -/
def IsFinitePacking (S : Set UnitSegment) : Prop :=
  IsPacking S ∧ S.Finite

/-- A countably infinite packing -/
def IsCountablyInfinitePacking (S : Set UnitSegment) : Prop :=
  IsPacking S ∧ S.Countable ∧ Set.Infinite S

/-! ## Danzer's Result -/

/-- Erdős Problem 1071(a) — SOLVED by Danzer:
    There exists a finite maximal packing of unit segments in [0,1]² -/
axiom danzer_finite_maximal :
  ∃ S : Set UnitSegment, IsFinitePacking S ∧ IsMaximalPacking S

/-! ## The Open Problem -/

/-- A region R in ℝ² (abstracted as a set of rational points) -/
def Region := Set (ℚ × ℚ)

/-- A packing restricted to a region R -/
def IsRegionPacking (R : Region) (S : Set UnitSegment) : Prop :=
  (∀ s ∈ S, s.x1 ∈ R ∧ s.x2 ∈ R) ∧
  (∀ s ∈ S, ∀ t ∈ S, s ≠ t → AreDisjoint s t)

/-- Maximal packing in a region -/
def IsMaximalRegionPacking (R : Region) (S : Set UnitSegment) : Prop :=
  IsRegionPacking R S ∧
  ∀ s : UnitSegment, s.x1 ∈ R → s.x2 ∈ R → s ∉ S →
    ∃ t ∈ S, ¬AreDisjoint s t

/-- Erdős Problem 1071(b) — OPEN:
    Is there a region R with a countably infinite maximal packing? -/
axiom ErdosProblem1071b :
  ∃ R : Region, ∃ S : Set UnitSegment,
    IsMaximalRegionPacking R S ∧ S.Countable ∧ Set.Infinite S

/-! ## Endpoint-Intersection Variant -/

/-- Two segments may intersect only at their endpoints -/
axiom EndpointDisjoint : UnitSegment → UnitSegment → Prop

/-- The endpoint-intersection variant: can a finite set of unit segments
    in [0,1]², allowed to touch only at endpoints, be maximal? -/
axiom ErdosProblem1071_endpoint_variant :
  ∃ S : Set UnitSegment, S.Finite ∧
    (∀ s ∈ S, SegmentInSquare s) ∧
    (∀ s ∈ S, ∀ t ∈ S, s ≠ t → EndpointDisjoint s t) ∧
    (∀ s : UnitSegment, SegmentInSquare s → s ∉ S →
      ∃ t ∈ S, ¬EndpointDisjoint s t)
