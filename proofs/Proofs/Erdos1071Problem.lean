/-
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

import Mathlib

open Set

namespace Erdos1071

/-
# Part 1: Geometric Foundations

Define points, segments, and disjointness using real-valued geometry.
-/

/-- Euclidean distance in ℝ² -/
noncomputable def euclidDist (p q : ℝ × ℝ) : ℝ :=
  Real.sqrt ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2)

/-- A unit segment in ℝ², represented by its two endpoints at Euclidean distance 1 -/
structure UnitSegment where
  x1 : ℝ × ℝ
  x2 : ℝ × ℝ
  unit_length : euclidDist x1 x2 = 1

/-- The set of points on a line segment from p to q (convex combination) -/
def segmentSet (p q : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {r | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
    r = ((1 - t) * p.1 + t * q.1, (1 - t) * p.2 + t * q.2)}

/-- A point lies in the unit square [0,1]² -/
def InUnitSquare (p : ℝ × ℝ) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1

/-- A unit segment lies in the unit square (endpoint check) -/
def SegmentInSquare (s : UnitSegment) : Prop :=
  InUnitSquare s.x1 ∧ InUnitSquare s.x2

/-
# Part 2: Disjointness (DEFINED, was axiom)

Two segments are disjoint if their point sets don't intersect.
-/

/-- Two segments are disjoint: their point sets have empty intersection -/
def AreDisjoint (s t : UnitSegment) : Prop :=
  Disjoint (segmentSet s.x1 s.x2) (segmentSet t.x1 t.x2)

/-- Disjointness is symmetric (PROVED, was axiom) -/
theorem disjoint_symm (s t : UnitSegment) : AreDisjoint s t → AreDisjoint t s := by
  intro h; exact h.symm

/-- Two segments may intersect only at their endpoints -/
def EndpointDisjoint (s t : UnitSegment) : Prop :=
  segmentSet s.x1 s.x2 ∩ segmentSet t.x1 t.x2 ⊆ {s.x1, s.x2} ∪ {t.x1, t.x2}

/-
# Part 3: Packing Definitions
-/

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

/-
# Part 4: Structural Lemmas
-/

/-- Endpoints lie on their segment -/
lemma left_endpoint_mem_segment (p q : ℝ × ℝ) : p ∈ segmentSet p q :=
  ⟨0, le_refl 0, le_of_lt one_pos, by ring_nf⟩

lemma right_endpoint_mem_segment (p q : ℝ × ℝ) : q ∈ segmentSet p q :=
  ⟨1, le_of_lt one_pos, le_refl 1, by ring_nf⟩

/-- The empty set is a packing -/
theorem packing_empty : IsPacking (∅ : Set UnitSegment) :=
  ⟨fun _ h => absurd h (Set.notMem_empty _),
   fun _ h => absurd h (Set.notMem_empty _)⟩

/-- A subset of a packing is a packing -/
theorem packing_subset {S T : Set UnitSegment} (hT : IsPacking T) (hST : S ⊆ T) :
    IsPacking S :=
  ⟨fun s hs => hT.1 s (hST hs),
   fun s hs t ht hne => hT.2 s (hST hs) t (hST ht) hne⟩

/-- A finite packing is countable -/
theorem finite_packing_countable {S : Set UnitSegment}
    (h : IsFinitePacking S) : S.Countable :=
  h.2.countable

/-- AreDisjoint implies EndpointDisjoint (strictly disjoint is endpoint-disjoint) -/
theorem disjoint_implies_endpoint_disjoint (s t : UnitSegment) :
    AreDisjoint s t → EndpointDisjoint s t := by
  intro h p hp
  exfalso
  exact Set.disjoint_iff.mp h ⟨hp.1, hp.2⟩

/-- The segment set is nonempty (contains at least the left endpoint). -/
theorem segmentSet_nonempty (p q : ℝ × ℝ) : (segmentSet p q).Nonempty :=
  ⟨p, left_endpoint_mem_segment p q⟩

/-- A segment is not disjoint from itself (it intersects at its own endpoints). -/
theorem not_areDisjoint_self (s : UnitSegment) : ¬AreDisjoint s s := by
  intro h
  have := Set.disjoint_left.mp h (left_endpoint_mem_segment s.x1 s.x2)
  exact this (left_endpoint_mem_segment s.x1 s.x2)

/- Part 4b: Euclidean Distance Properties -/

/-- Euclidean distance is symmetric -/
theorem euclidDist_symm (p q : ℝ × ℝ) : euclidDist p q = euclidDist q p := by
  unfold euclidDist; congr 1; ring

/-- Euclidean distance is non-negative -/
theorem euclidDist_nonneg (p q : ℝ × ℝ) : 0 ≤ euclidDist p q :=
  Real.sqrt_nonneg _

/-- Distance from a point to itself is 0 -/
theorem euclidDist_self (p : ℝ × ℝ) : euclidDist p p = 0 := by
  unfold euclidDist
  have : (p.1 - p.1) ^ 2 + (p.2 - p.2) ^ 2 = 0 := by ring
  rw [this, Real.sqrt_zero]

/-- A unit segment's endpoints are distinct -/
theorem UnitSegment.endpoints_ne (s : UnitSegment) : s.x1 ≠ s.x2 := by
  intro h; have := s.unit_length; rw [h, euclidDist_self] at this; linarith

/- Part 4c: Convexity of the Unit Square -/

/-- The unit square [0,1]² is convex: convex combinations stay inside -/
theorem unitSquare_convex {p q : ℝ × ℝ} (hp : InUnitSquare p) (hq : InUnitSquare q)
    {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    InUnitSquare ((1 - t) * p.1 + t * q.1, (1 - t) * p.2 + t * q.2) := by
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
  obtain ⟨hq1, hq2, hq3, hq4⟩ := hq
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- All points on a segment between two unit-square points are in [0,1]² -/
theorem segment_in_square_all_points {p q : ℝ × ℝ}
    (hp : InUnitSquare p) (hq : InUnitSquare q) :
    ∀ r ∈ segmentSet p q, InUnitSquare r := by
  intro r ⟨t, h0, h1, hrfl⟩; rw [hrfl]; exact unitSquare_convex hp hq h0 h1

/-- SegmentInSquare implies all points on the segment are in the square -/
theorem packing_segment_all_in_square (s : UnitSegment) (h : SegmentInSquare s) :
    ∀ r ∈ segmentSet s.x1 s.x2, InUnitSquare r :=
  segment_in_square_all_points h.1 h.2

/- Part 4d: Concrete Constructions -/

/-- The horizontal segment from (0, 1/2) to (1, 1/2) -/
noncomputable def horizontalMidSegment : UnitSegment where
  x1 := (0, 1/2)
  x2 := (1, 1/2)
  unit_length := by
    unfold euclidDist
    have : ((0 : ℝ) - 1) ^ 2 + ((1 : ℝ) / 2 - 1 / 2) ^ 2 = 1 := by ring
    rw [this, Real.sqrt_one]

/-- The horizontal mid-segment is in the unit square -/
theorem horizontalMidSegment_in_square : SegmentInSquare horizontalMidSegment := by
  dsimp [SegmentInSquare, InUnitSquare, horizontalMidSegment]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;> norm_num

/-- A singleton set is a valid packing -/
theorem packing_singleton (s : UnitSegment) (h : SegmentInSquare s) :
    IsPacking {s} := by
  constructor
  · intro t ht; rwa [Set.mem_singleton_iff.mp ht]
  · intro a ha b hb hab
    exact absurd ((Set.mem_singleton_iff.mp ha).symm.trans (Set.mem_singleton_iff.mp hb)) hab

/-- There exists a non-empty packing (witness: horizontal mid-segment) -/
theorem exists_nonempty_packing :
    ∃ S : Set UnitSegment, IsPacking S ∧ S.Nonempty :=
  ⟨{horizontalMidSegment}, packing_singleton _ horizontalMidSegment_in_square,
   Set.singleton_nonempty _⟩

/-- A maximal packing in the unit square must be nonempty.
    (If S were empty, any unit segment could be added, contradicting maximality.) -/
theorem maximal_packing_nonempty (S : Set UnitSegment) (hmax : IsMaximalPacking S) :
    S.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hblock := hmax.2 horizontalMidSegment horizontalMidSegment_in_square
    (by rw [h]; exact Set.not_mem_empty _)
  obtain ⟨t, ht, _⟩ := hblock
  rw [h] at ht
  exact Set.not_mem_empty _ ht

/-
# Part 5: Danzer's Result (SOLVED)
-/

/-- Erdős Problem 1071(a) — SOLVED by Danzer:
    There exists a finite maximal packing of unit segments in [0,1]² -/
/-
# Part 6: The Open Problem
-/

/-- A region R in ℝ² -/
abbrev Region := Set (ℝ × ℝ)

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
/-
# Part 7: Endpoint-Intersection Variant
-/

/-- The endpoint-intersection variant: can a finite set of unit segments
    in [0,1]², allowed to touch only at endpoints, be maximal? -/
end Erdos1071
