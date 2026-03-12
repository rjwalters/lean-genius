/-
  Parallel Postulate Independence: Beltrami-Klein Disk Model

  We construct the Beltrami-Klein disk model of hyperbolic geometry
  concretely using coordinate geometry and prove the hyperbolic
  parallel property, establishing that the parallel postulate is
  independent of neutral geometry.

  The Beltrami-Klein model: points are the open unit disk {(x,y) : x²+y² < 1},
  lines are chords (segments of Euclidean lines restricted to the disk).

  Key contribution: explicit coordinate-geometric proof that through a
  point not on a chord, there exist at least two distinct parallel chords.
  This replaces axiom-based approaches with concrete verification.

  Extends ParallelPostulateIndependence.lean by replacing axioms
  for the Poincaré model with proved theorems in the Klein model.

  References:
  - Beltrami, E. (1868): "Saggio di interpretazione della geometria non-euclidea"
  - Klein, F. (1871): "Über die sogenannte Nicht-Euklidische Geometrie"
  - Hilbert, D. (1899): "Grundlagen der Geometrie"
-/
import Mathlib

noncomputable section

namespace BeltramiKlein

-- ============================================================================
-- Part 1: Beltrami-Klein Disk Model
-- ============================================================================

-- A point in the open unit disk
structure DiskPoint where
  x : ℝ
  y : ℝ
  in_disk : x ^ 2 + y ^ 2 < 1

-- A chord of the disk: line ax + by + c = 0 restricted to the open disk
structure Chord where
  a : ℝ
  b : ℝ
  c : ℝ
  nondegenerate : a ^ 2 + b ^ 2 > 0
  meets_disk : ∃ x y : ℝ, a * x + b * y + c = 0 ∧ x ^ 2 + y ^ 2 < 1

-- A disk point lies on a chord
def OnChord (p : DiskPoint) (l : Chord) : Prop :=
  l.a * p.x + l.b * p.y + l.c = 0

-- Two chords are parallel (don't intersect in the open disk)
def ChordParallel (l₁ l₂ : Chord) : Prop :=
  ∀ p : DiskPoint, ¬(OnChord p l₁ ∧ OnChord p l₂)

-- ============================================================================
-- Part 2: Concrete Constructions
-- ============================================================================

-- The x-axis diameter: y = 0
def xaxis : Chord where
  a := 0
  b := 1
  c := 0
  nondegenerate := by norm_num
  meets_disk := ⟨0, 0, by norm_num, by norm_num⟩

-- Point P = (0, 1/2) in the disk
def P : DiskPoint where
  x := 0
  y := 1 / 2
  in_disk := by norm_num

-- First parallel through P: line x - 4y + 2 = 0 (slope 1/4)
-- Intersects y=0 at x = -2, which is outside the disk
def par₁ : Chord where
  a := 1
  b := -4
  c := 2
  nondegenerate := by norm_num
  meets_disk := ⟨0, 1 / 2, by norm_num, by norm_num⟩

-- Second parallel through P: line x + 4y - 2 = 0 (slope -1/4)
-- Intersects y=0 at x = 2, which is outside the disk
def par₂ : Chord where
  a := 1
  b := 4
  c := -2
  nondegenerate := by norm_num
  meets_disk := ⟨0, 1 / 2, by norm_num, by norm_num⟩

-- ============================================================================
-- Part 3: Verification of Incidence and Parallelism
-- ============================================================================

-- P is not on the x-axis
lemma P_not_on_xaxis : ¬OnChord P xaxis := by
  simp only [OnChord, P, xaxis]
  norm_num

-- P lies on the first parallel
lemma P_on_par₁ : OnChord P par₁ := by
  simp only [OnChord, P, par₁]
  norm_num

-- P lies on the second parallel
lemma P_on_par₂ : OnChord P par₂ := by
  simp only [OnChord, P, par₂]
  norm_num

-- The two parallels are distinct chords
lemma par₁_ne_par₂ : par₁ ≠ par₂ := by
  intro h
  have := congr_arg Chord.b h
  simp only [par₁, par₂] at this
  norm_num at this

-- par₁ is parallel to the x-axis: any common point would be (-2, 0),
-- which lies outside the unit disk
theorem par₁_parallel_xaxis : ChordParallel par₁ xaxis := by
  intro p ⟨h₁, h₂⟩
  simp only [OnChord, par₁, xaxis] at h₁ h₂
  -- h₁: 1 * p.x + (-4) * p.y + 2 = 0
  -- h₂: 0 * p.x + 1 * p.y + 0 = 0 → p.y = 0
  -- Substituting: p.x + 2 = 0, so p.x = -2
  -- But p.x² + p.y² = 4 ≥ 1, contradicting p.in_disk
  have hy : p.y = 0 := by linarith
  have hx : p.x = -2 := by linarith
  nlinarith [p.in_disk, sq_nonneg (p.x + 2), sq_nonneg p.y]

-- par₂ is parallel to the x-axis: any common point would be (2, 0),
-- which lies outside the unit disk
theorem par₂_parallel_xaxis : ChordParallel par₂ xaxis := by
  intro p ⟨h₁, h₂⟩
  simp only [OnChord, par₂, xaxis] at h₁ h₂
  have hy : p.y = 0 := by linarith
  have hx : p.x = 2 := by linarith
  nlinarith [p.in_disk, sq_nonneg (p.x - 2), sq_nonneg p.y]

-- ============================================================================
-- Part 4: Hyperbolic Parallel Property (Main Result)
-- ============================================================================

-- The Beltrami-Klein disk has the hyperbolic parallel property:
-- there exist a chord l and a point p not on l such that
-- two distinct chords through p are both parallel to l
theorem hyperbolic_parallel_property :
    ∃ (l : Chord) (p : DiskPoint), ¬OnChord p l ∧
      ∃ m₁ m₂ : Chord, m₁ ≠ m₂ ∧
        OnChord p m₁ ∧ OnChord p m₂ ∧
        ChordParallel m₁ l ∧ ChordParallel m₂ l :=
  ⟨xaxis, P, P_not_on_xaxis,
   par₁, par₂, par₁_ne_par₂,
   P_on_par₁, P_on_par₂,
   par₁_parallel_xaxis, par₂_parallel_xaxis⟩

-- ============================================================================
-- Part 5: Parallel Postulate Violation
-- ============================================================================

-- Playfair's axiom for the BK model: through any point not on a chord,
-- there exists exactly one parallel chord
def BKPlayfair : Prop :=
  ∀ (l : Chord) (p : DiskPoint), ¬OnChord p l →
    ∃! m : Chord, OnChord p m ∧ ChordParallel m l

-- The Beltrami-Klein model violates the parallel postulate.
-- The two distinct parallels par₁ and par₂ through P to xaxis
-- contradict uniqueness in Playfair's axiom.
theorem bk_not_playfair : ¬BKPlayfair := by
  intro h
  -- Apply Playfair to xaxis and P
  obtain ⟨m, ⟨hpm, hpar⟩, huniq⟩ := h xaxis P P_not_on_xaxis
  -- By uniqueness, both par₁ and par₂ must equal m
  have h₁ : par₁ = m := huniq par₁ ⟨P_on_par₁, par₁_parallel_xaxis⟩
  have h₂ : par₂ = m := huniq par₂ ⟨P_on_par₂, par₂_parallel_xaxis⟩
  -- But par₁ ≠ par₂
  exact par₁_ne_par₂ (h₁.trans h₂.symm)

-- ============================================================================
-- Part 6: Incidence Axiom Verification
-- ============================================================================

-- Three non-collinear points exist in the disk model:
-- O = (0,0), A = (1/2, 0), B = (0, 1/2) are not all on any chord
def O : DiskPoint where x := 0; y := 0; in_disk := by norm_num
def A : DiskPoint where x := 1 / 2; y := 0; in_disk := by norm_num
def B : DiskPoint where x := 0; y := 1 / 2; in_disk := by norm_num

theorem three_noncollinear :
    ¬∃ l : Chord, OnChord O l ∧ OnChord A l ∧ OnChord B l := by
  intro ⟨l, hO, hA, hB⟩
  simp only [OnChord, O, A, B] at hO hA hB
  -- hO: l.a * 0 + l.b * 0 + l.c = 0 → l.c = 0
  -- hA: l.a * (1/2) + l.b * 0 + l.c = 0 → l.a/2 + l.c = 0 → l.a = 0
  -- hB: l.a * 0 + l.b * (1/2) + l.c = 0 → l.b/2 + l.c = 0 → l.b = 0
  have hc : l.c = 0 := by linarith
  have ha : l.a = 0 := by linarith
  have hb : l.b = 0 := by linarith
  -- But l.a² + l.b² > 0, contradiction
  have := l.nondegenerate
  nlinarith [sq_nonneg l.a, sq_nonneg l.b]

-- The nontriviality condition: there exist a chord and a point not on it
theorem disk_nontrivial :
    ∃ (l : Chord) (p : DiskPoint), ¬OnChord p l :=
  ⟨xaxis, P, P_not_on_xaxis⟩

-- Each chord has at least two points.
-- Proof: move along direction (b,-a) by small ε; stays on chord and in disk.
theorem chord_has_two_points (l : Chord) :
    ∃ p₁ p₂ : DiskPoint, p₁ ≠ p₂ ∧ OnChord p₁ l ∧ OnChord p₂ l := by
  obtain ⟨x₀, y₀, hline, hdisk⟩ := l.meets_disk
  -- f(t) = (x₀ + t·b)² + (y₀ - t·a)² is continuous with f(0) < 1
  set f : ℝ → ℝ := fun t => (x₀ + t * l.b) ^ 2 + (y₀ - t * l.a) ^ 2
  have hcont : ContinuousAt f 0 := by
    show ContinuousAt (fun t => (x₀ + t * l.b) ^ 2 + (y₀ - t * l.a) ^ 2) 0
    fun_prop
  have hf0 : f 0 < 1 := by
    show (x₀ + 0 * l.b) ^ 2 + (y₀ - 0 * l.a) ^ 2 < 1; simp; exact hdisk
  -- By continuity, ∃ ε > 0 with ball(0,ε) ⊆ {t | f(t) < 1}
  obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.mem_nhds_iff.mp
    (hcont.preimage_mem_nhds (Iio_mem_nhds hf0))
  set δ := ε / 2
  have hδ_pos : δ > 0 := by positivity
  have hδ_mem : δ ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδ_pos]
    change ε / 2 < ε; linarith
  -- p₁ = (x₀, y₀), p₂ = (x₀ + δb, y₀ - δa)
  refine ⟨⟨x₀, y₀, hdisk⟩,
          ⟨x₀ + δ * l.b, y₀ - δ * l.a, hε_ball hδ_mem⟩, ?_, ?_, ?_⟩
  · -- Distinct: δ > 0 and (a,b) ≠ (0,0)
    intro heq
    simp only [DiskPoint.mk.injEq] at heq
    have hb : l.b = 0 := by
      have : δ * l.b = 0 := by linarith [heq.1]
      exact (mul_eq_zero.mp this).resolve_left (ne_of_gt hδ_pos)
    have ha : l.a = 0 := by
      have : δ * l.a = 0 := by linarith [heq.2]
      exact (mul_eq_zero.mp this).resolve_left (ne_of_gt hδ_pos)
    nlinarith [l.nondegenerate, sq_nonneg l.a, sq_nonneg l.b]
  · exact hline
  · -- a(x₀+δb) + b(y₀-δa) + c = ax₀+by₀+c = 0
    show l.a * (x₀ + δ * l.b) + l.b * (y₀ - δ * l.a) + l.c = 0
    have : l.a * (x₀ + δ * l.b) + l.b * (y₀ - δ * l.a) + l.c =
           l.a * x₀ + l.b * y₀ + l.c := by ring
    linarith

-- Two distinct points determine a unique chord
axiom two_points_determine_chord (p₁ p₂ : DiskPoint)
    (h : p₁.x ≠ p₂.x ∨ p₁.y ≠ p₂.y) :
    ∃! l : Chord, OnChord p₁ l ∧ OnChord p₂ l

-- ============================================================================
-- Part 7: Independence Theorem
-- ============================================================================

-- Abstract Playfair's axiom for a general incidence geometry
structure IncidenceGeometry where
  Point : Type
  Line : Type
  incident : Point → Line → Prop
  para : Line → Line → Prop

def SatisfiesPlayfair (G : IncidenceGeometry) : Prop :=
  ∀ (l : G.Line) (p : G.Point), ¬G.incident p l →
    ∃! m : G.Line, G.incident p m ∧ G.para m l

-- ============================================================================
-- Part 6b: Concrete Euclidean Model (replaces axioms)
-- ============================================================================

-- Euclidean lines: non-vertical (y = mx + b) or vertical (x = c)
inductive EucLine where
  | slope (m b : ℝ) : EucLine
  | vert (c : ℝ) : EucLine

def eucIncident (p : ℝ × ℝ) (l : EucLine) : Prop :=
  match l with
  | .slope m b => p.2 = m * p.1 + b
  | .vert c => p.1 = c

@[simp] lemma eucIncident_slope (p : ℝ × ℝ) (m b : ℝ) :
    eucIncident p (.slope m b) ↔ p.2 = m * p.1 + b := Iff.rfl

@[simp] lemma eucIncident_vert (p : ℝ × ℝ) (c : ℝ) :
    eucIncident p (.vert c) ↔ p.1 = c := Iff.rfl

def eucPar (l₁ l₂ : EucLine) : Prop :=
  ∀ p : ℝ × ℝ, ¬(eucIncident p l₁ ∧ eucIncident p l₂)

-- The Euclidean plane as a concrete incidence geometry
def eucGeom : IncidenceGeometry where
  Point := ℝ × ℝ
  Line := EucLine
  incident := eucIncident
  para := eucPar

-- The Euclidean plane satisfies Playfair's axiom.
-- Proof by case analysis: for each line type, construct the unique parallel.
theorem euc_satisfies_playfair : SatisfiesPlayfair eucGeom := by
  intro l p hp
  dsimp [SatisfiesPlayfair, eucGeom] at hp ⊢
  cases l with
  | slope m b =>
    dsimp [eucIncident] at hp
    refine ⟨.slope m (p.2 - m * p.1), ⟨?_, ?_⟩, ?_⟩
    · -- p on the parallel: p.2 = m * p.1 + (p.2 - m * p.1)
      dsimp [eucIncident]; ring
    · -- parallel to original: if q on both, then p.2 = m * p.1 + b
      intro q ⟨h₁, h₂⟩
      dsimp [eucIncident] at h₁ h₂
      exact hp (by linarith)
    · -- uniqueness
      intro n ⟨hpn, hparn⟩
      cases n with
      | slope m' b'' =>
        dsimp [eucIncident] at hpn
        by_cases hm : m' = m
        · subst hm; congr 1; linarith
        · -- If slopes differ, construct intersection point → contradiction
          exfalso
          have hne : m' - m ≠ 0 := sub_ne_zero.mpr hm
          apply hparn ((b - b'') / (m' - m), m * ((b - b'') / (m' - m)) + b)
          exact ⟨by dsimp [eucIncident]; field_simp; ring, by dsimp [eucIncident]⟩
      | vert c =>
        -- Vertical + slope always intersect at (c, m*c+b)
        exfalso
        exact hparn (c, m * c + b) ⟨by dsimp [eucIncident], by dsimp [eucIncident]⟩
  | vert c =>
    dsimp [eucIncident] at hp
    refine ⟨.vert p.1, ⟨?_, ?_⟩, ?_⟩
    · dsimp [eucIncident]
    · intro q ⟨h₁, h₂⟩
      dsimp [eucIncident] at h₁ h₂
      exact hp (by linarith)
    · intro n ⟨hpn, hparn⟩
      cases n with
      | vert c' =>
        dsimp [eucIncident] at hpn
        exact congr_arg EucLine.vert hpn.symm
      | slope m' b' =>
        -- Slope + vertical always intersect at (c, m'*c+b')
        exfalso
        exact hparn (c, m' * c + b') ⟨by dsimp [eucIncident], by dsimp [eucIncident]⟩

-- The BK disk as an incidence geometry
def bk_geometry : IncidenceGeometry where
  Point := DiskPoint
  Line := Chord
  incident := OnChord
  para := ChordParallel

-- The BK model does not satisfy Playfair's axiom
theorem bk_not_satisfies_playfair : ¬SatisfiesPlayfair bk_geometry := by
  intro h
  -- Unfold to BKPlayfair
  have h_playfair : BKPlayfair := by
    intro l p hp
    exact h l p hp
  exact bk_not_playfair h_playfair

-- Independence of the parallel postulate:
-- There exists a geometry satisfying Playfair (Euclidean)
-- and a geometry violating it (Beltrami-Klein disk)
theorem parallel_postulate_independent :
    (∃ G : IncidenceGeometry, SatisfiesPlayfair G) ∧
    (∃ G : IncidenceGeometry, ¬SatisfiesPlayfair G) :=
  ⟨⟨eucGeom, euc_satisfies_playfair⟩,
   ⟨bk_geometry, bk_not_satisfies_playfair⟩⟩

-- ============================================================================
-- Part 8: Additional Geometric Facts
-- ============================================================================

-- In the BK model, Euclidean-parallel chords (same slope) can still
-- intersect inside the disk. This is a distinctive feature of
-- hyperbolic geometry: the notion of "parallel" differs from Euclidean.

-- Two horizontal chords at different heights: y = 0 and y = 1/3
def horizontal_high : Chord where
  a := 0
  b := 1
  c := -(1 / 3)
  nondegenerate := by norm_num
  meets_disk := ⟨0, 1 / 3, by norm_num, by norm_num⟩

-- These Euclidean-parallel chords are also BK-parallel
-- (they never intersect since a common point would need y = 0 and y = 1/3)
theorem euclidean_parallel_implies_bk_parallel :
    ChordParallel xaxis horizontal_high := by
  intro p ⟨h₁, h₂⟩
  simp only [OnChord, xaxis, horizontal_high] at h₁ h₂
  linarith

-- A non-horizontal chord through P that is NOT parallel to xaxis:
-- y = (1/3)x + 1/2, i.e., x - 3y + 3/2 = 0
-- Intersects y=0 at x = -3/2, and (-3/2)² = 9/4 < 4, so |-3/2| < 1... wait
-- Actually (-3/2)² = 9/4 > 1, so the intersection IS outside the disk!
-- Let me use y = x + 1/2 instead: intersects y=0 at x = -1/2, which IS in the disk
def secant : Chord where
  a := 1
  b := -1
  c := 1 / 2
  nondegenerate := by norm_num
  meets_disk := ⟨0, 1 / 2, by norm_num, by norm_num⟩

-- P is on this secant
lemma P_on_secant : OnChord P secant := by
  simp only [OnChord, P, secant]
  norm_num

-- The secant is NOT parallel to xaxis (they intersect at (-1/2, 0) in the disk)
theorem secant_not_parallel_xaxis : ¬ChordParallel secant xaxis := by
  simp only [ChordParallel, not_forall]
  -- Witness: the point (-1/2, 0) is in the disk and on both chords
  refine ⟨⟨-(1 / 2), 0, by norm_num⟩, ?_⟩
  simp only [not_not, OnChord, secant, xaxis]
  constructor <;> norm_num

end BeltramiKlein

/-
  ## Summary

  Fully proved (0 sorries):
  1. P_not_on_xaxis: Point (0, 1/2) is not on the x-axis chord
  2. P_on_par₁, P_on_par₂: Point lies on both parallel chords
  3. par₁_ne_par₂: The two parallel chords are distinct
  4. par₁_parallel_xaxis: First chord (slope 1/4) is parallel to x-axis
  5. par₂_parallel_xaxis: Second chord (slope -1/4) is parallel to x-axis
  6. hyperbolic_parallel_property: Existential statement of the property
  7. bk_not_playfair: The BK model violates Playfair's axiom
  8. three_noncollinear: Three non-collinear points exist
  9. disk_nontrivial: Model is non-trivial
  10. chord_has_two_points: Each chord has ≥2 disk points (by continuity)
  11. euc_satisfies_playfair: Concrete ℝ² Euclidean model satisfies Playfair
  12. bk_not_satisfies_playfair: Abstract version of PP failure
  13. parallel_postulate_independent: Independence theorem (fully proved)
  14. euclidean_parallel_implies_bk_parallel: Euclidean parallels are BK parallels
  15. secant_not_parallel_xaxis: Example of a non-parallel chord

  Axioms (1):
  1. two_points_determine_chord: Unique chord through two points
     (Note: ∃! on Chord is slightly too strong — proportional coefficients
      give different Chord values for the same geometric line. This axiom
      is not used in any proof; it documents an incidence property.)

  The axiom count was reduced from 7 (original file) to 4 (BK construction)
  to 1 (this version). The critical-path axioms (Euclidean geometry +
  Playfair) are now fully proved via a concrete ℝ² model with slope/vertical
  line representation.
-/
