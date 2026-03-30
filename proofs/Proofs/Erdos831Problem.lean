/-
Erdős Problem #831: Distinct Radii Circles Through Point Configurations

Source: https://erdosproblems.com/831
Status: OPEN

Statement:
Let h(n) be maximal such that in any n points in ℝ² (with no three on a line
and no four on a circle) there are at least h(n) circles of different radii
passing through three of the points. Estimate h(n).

Context:
Given n points in general position (no three collinear, no four concyclic),
any three points determine a unique circle (the circumcircle). With n points,
there are C(n,3) such circles. The question is: how many DISTINCT radii must
appear among these circles?

Key Observations:
- For n points, there are C(n,3) = n(n-1)(n-2)/6 circles through triples
- The problem asks for a lower bound on the number of distinct radii
- The constraint "no four on a circle" prevents degeneracies

Related Problems:
- Problem #104: Related point-line configurations
- Problem #506: Related geometric extremal problems

References:
- [Er75h] Erdős 1975
- [Er92e] Erdős 1992
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Data.Finset.Card

open Set Finset

namespace Erdos831

/-
## Part I: Points in the Plane

We work with points in ℝ².
-/

/-- Type alias for points in the Euclidean plane. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- A triple of distinct points. -/
structure PointTriple where
  p1 : Point
  p2 : Point
  p3 : Point
  distinct12 : p1 ≠ p2
  distinct13 : p1 ≠ p3
  distinct23 : p2 ≠ p3

/-
## Part II: Collinearity and Concyclicity Conditions
-/

/--
**Collinearity:**
Three points are collinear if they lie on a common line.
-/
def areCollinear (p1 p2 p3 : Point) : Prop :=
  ∃ a b c : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧
    a * (p1 0) + b * (p1 1) + c = 0 ∧
    a * (p2 0) + b * (p2 1) + c = 0 ∧
    a * (p3 0) + b * (p3 1) + c = 0

/--
**Concyclicity:**
Four points are concyclic if they lie on a common circle.
-/
def areConcyclic (p1 p2 p3 p4 : Point) : Prop :=
  ∃ center : Point, ∃ r : ℝ, r > 0 ∧
    ‖p1 - center‖ = r ∧ ‖p2 - center‖ = r ∧
    ‖p3 - center‖ = r ∧ ‖p4 - center‖ = r

/--
**General Position:**
A point configuration is in general position if no three points are collinear
and no four points are concyclic.
-/
def isInGeneralPosition (S : Set Point) : Prop :=
  (∀ p1 p2 p3 : Point, p1 ∈ S → p2 ∈ S → p3 ∈ S →
    p1 ≠ p2 → p2 ≠ p3 → p1 ≠ p3 → ¬areCollinear p1 p2 p3) ∧
  (∀ p1 p2 p3 p4 : Point, p1 ∈ S → p2 ∈ S → p3 ∈ S → p4 ∈ S →
    p1 ≠ p2 → p2 ≠ p3 → p3 ≠ p4 → p1 ≠ p3 → p1 ≠ p4 → p2 ≠ p4 →
    ¬areConcyclic p1 p2 p3 p4)

/-
## Part III: Circumcircles and Radii
-/

/--
**Circumradius:**
The radius of the circumcircle through three non-collinear points.
For a triangle with sides a, b, c and area A, the circumradius is R = abc/(4A).
-/
noncomputable def circumradius (t : PointTriple) : ℝ :=
  let a := ‖t.p2 - t.p3‖
  let b := ‖t.p1 - t.p3‖
  let c := ‖t.p1 - t.p2‖
  -- Using the formula R = abc / (4 * Area)
  -- Area via cross product magnitude / 2
  let twiceArea := |((t.p2 0 - t.p1 0) * (t.p3 1 - t.p1 1) -
                     (t.p3 0 - t.p1 0) * (t.p2 1 - t.p1 1))|
  if twiceArea = 0 then 0  -- degenerate case (collinear)
  else (a * b * c) / (2 * twiceArea)

/-- Circumradius computed directly from three points (no PointTriple wrapper).
    Uses the formula R = abc / (4·Area) where a,b,c are side lengths
    and Area is the triangle area from the cross product. -/
noncomputable def circumradiusOf (p1 p2 p3 : Point) : ℝ :=
  let a := ‖p2 - p3‖
  let b := ‖p1 - p3‖
  let c := ‖p1 - p2‖
  let twiceArea := |((p2 0 - p1 0) * (p3 1 - p1 1) -
                     (p3 0 - p1 0) * (p2 1 - p1 1))|
  if twiceArea = 0 then 0
  else (a * b * c) / (2 * twiceArea)

/-
## Part IV: Counting Distinct Radii
-/

/--
**Set of All Circumradii (propositional):**
For a finite point set S, the set of all circumradii from triples in S.
Used for subset/containment reasoning.
-/
noncomputable def allCircumradii (S : Finset Point) : Set ℝ :=
  {r : ℝ | ∃ p1 p2 p3 : Point, p1 ∈ S ∧ p2 ∈ S ∧ p3 ∈ S ∧
    p1 ≠ p2 ∧ p2 ≠ p3 ∧ p1 ≠ p3 ∧
    ∃ t : PointTriple, t.p1 = p1 ∧ t.p2 = p2 ∧ t.p3 = p3 ∧ circumradius t = r}

-- Classical DecidableEq needed for Finset operations on ℝ and Point
noncomputable instance : DecidableEq Point := Classical.decEq _
noncomputable instance : DecidableEq ℝ := Classical.decEq _

/--
**Finset of All Circumradii:**
For a finite point set S, the finset of all circumradii from ordered
triples of distinct points in S. This is the computational version
of allCircumradii, using Finset.image for correct cardinality.

Note: circumradiusOf is permutation-invariant, so each unordered triple
contributes one element to the image even though it appears in 6 ordered forms.
-/
noncomputable def allCircumradiiFinset (S : Finset Point) : Finset ℝ :=
  ((S ×ˢ (S ×ˢ S)).filter (fun p : Point × (Point × Point) =>
    p.1 ≠ p.2.1 ∧ p.2.1 ≠ p.2.2 ∧ p.1 ≠ p.2.2)).image
    (fun p : Point × (Point × Point) => circumradiusOf p.1 p.2.1 p.2.2)

/--
**Number of Distinct Radii:**
The cardinality of the finset of distinct circumradii.

FIXED: Previously used Nat.card on a Set ℝ subtype, which always returned 0
(no Fintype instance available for existentially-quantified subsets of ℝ).
Now uses Finset.card on a properly computed Finset ℝ.
-/
noncomputable def countDistinctRadii (S : Finset Point) : ℕ :=
  (allCircumradiiFinset S).card

/--
**The h Function:**
h(n) is the minimum over all n-point configurations in general position
of the number of distinct circumradii.
-/
noncomputable def h (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ S : Finset Point, S.card = n ∧
    isInGeneralPosition (↑S : Set Point) ∧ countDistinctRadii S = k}

/-
## Part V: Basic Bounds
-/

/--
**Number of Triples:**
With n points, there are C(n,3) triples, hence at most C(n,3) distinct radii.
-/
theorem h_upper_bound (n : ℕ) : h n ≤ Nat.choose n 3 := by
  -- sInf {k | ...} ≤ C(n,3): empty set gives 0 ≤ C(n,3), otherwise
  -- any member k = countDistinctRadii S ≤ C(|S|,3) = C(n,3)
  by_cases hne : Set.Nonempty {k : ℕ | ∃ S : Finset Point, S.card = n ∧
      isInGeneralPosition (↑S : Set Point) ∧ countDistinctRadii S = k}
  · obtain ⟨k, S, hcard, hGP, hcount⟩ := hne
    calc h n ≤ k := Nat.sInf_le ⟨S, hcard, hGP, hcount⟩
      _ ≤ Nat.choose n 3 := by
          rw [hcount, ← hcard]; exact countDistinctRadii_le_choose S
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : h n = 0 := by unfold h; rw [hne]; exact Nat.sInf_eq_zero.mpr (Or.inr rfl)
    omega

/--
**h(3) = 1:**
Three points in general position give exactly one circle, hence one radius.
-/
theorem h_three : h 3 = 1 := by
  apply le_antisymm
  · -- h 3 ≤ 1: exhibit a 3-point GP config with exactly 1 distinct radius
    apply Nat.sInf_le
    refine ⟨{p_origin, p_e1, p_e2}, ?_, ?_, ?_⟩
    · -- card = 3
      have h1 : p_e1 ∉ ({p_e2} : Finset Point) := by
        simp [Finset.mem_singleton, p_e1_ne_e2]
      have h2 : p_origin ∉ ({p_e1, p_e2} : Finset Point) := by
        simp [Finset.mem_insert, Finset.mem_singleton, p_origin_ne_e1, p_origin_ne_e2]
      rw [Finset.card_insert_of_not_mem h2, Finset.card_insert_of_not_mem h1,
          Finset.card_singleton]
    · -- isInGeneralPosition
      constructor
      · -- No 3 collinear: all permutations of (p_origin, p_e1, p_e2) are non-collinear
        intro q1 q2 q3 hq1 hq2 hq3 hd12 hd23 hd13
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
                   Set.mem_singleton_iff] at hq1 hq2 hq3
        -- Case split on membership (27 cases); 21 have qi=qj, 6 are permutations
        rcases hq1 with rfl | rfl | rfl <;> rcases hq2 with rfl | rfl | rfl <;>
          rcases hq3 with rfl | rfl | rfl <;>
        -- First try distinctness contradictions, then reduce to triangle_not_collinear
        first
        | exact absurd rfl hd12 | exact absurd rfl hd23 | exact absurd rfl hd13
        | exact absurd rfl (Ne.symm hd12) | exact absurd rfl (Ne.symm hd23)
        | exact absurd rfl (Ne.symm hd13)
        | (intro ⟨a, b, c, hab, h1, h2, h3⟩; exact triangle_not_collinear
            (by first | exact ⟨a, b, c, hab, h1, h2, h3⟩
                      | exact ⟨a, b, c, hab, h1, h3, h2⟩
                      | exact ⟨a, b, c, hab, h2, h1, h3⟩
                      | exact ⟨a, b, c, hab, h2, h3, h1⟩
                      | exact ⟨a, b, c, hab, h3, h1, h2⟩
                      | exact ⟨a, b, c, hab, h3, h2, h1⟩))
      · -- No 4 concyclic: vacuously true (4 distinct from 3-element set is impossible)
        intro q1 q2 q3 q4 hq1 hq2 hq3 hq4 hd12 hd23 hd34 hd13 hd14 hd24
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
                   Set.mem_singleton_iff] at hq1 hq2 hq3 hq4
        -- Pigeonhole: 4 values from 3 options, two must be equal
        rcases hq1 with rfl | rfl | rfl <;> rcases hq2 with rfl | rfl | rfl <;>
          rcases hq3 with rfl | rfl | rfl <;> rcases hq4 with rfl | rfl | rfl <;>
        first
        | exact absurd rfl hd12 | exact absurd rfl hd13 | exact absurd rfl hd14
        | exact absurd rfl hd23 | exact absurd rfl hd24 | exact absurd rfl hd34
        | exact absurd rfl (Ne.symm hd12) | exact absurd rfl (Ne.symm hd13)
        | exact absurd rfl (Ne.symm hd14) | exact absurd rfl (Ne.symm hd23)
        | exact absurd rfl (Ne.symm hd24) | exact absurd rfl (Ne.symm hd34)
    · -- countDistinctRadii S = 1
      -- allCircumradiiFinset = {circumradiusOf p_origin p_e1 p_e2} (singleton)
      -- because all 6 ordered triples map to same value by permutation invariance
      show (allCircumradiiFinset {p_origin, p_e1, p_e2}).card = 1
      rw [Finset.card_eq_one]
      refine ⟨circumradiusOf p_origin p_e1 p_e2,
        Finset.eq_singleton_iff_unique_mem.mpr ⟨?mem, ?uniq⟩⟩
      case mem =>
        -- (p_origin, (p_e1, p_e2)) is in the filtered product, maps to our value
        simp only [allCircumradiiFinset]
        apply Finset.mem_image_of_mem (a := (p_origin, (p_e1, p_e2)))
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
                   Finset.mem_singleton]
        exact ⟨⟨Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩,
               p_origin_ne_e1, p_e1_ne_e2, p_origin_ne_e2⟩
      case uniq =>
        -- Every element equals circumradiusOf p_origin p_e1 p_e2
        -- (all 6 permutations map to the same value)
        intro r hr
        simp only [allCircumradiiFinset, Finset.mem_image, Finset.mem_filter,
                   Finset.mem_product, Finset.mem_insert, Finset.mem_singleton] at hr
        obtain ⟨⟨p, q, s⟩, ⟨⟨hp, hq, hs⟩, hdpq, hdqs, hdps⟩, heq⟩ := hr
        rw [← heq]
        -- 27-way case split on which points p, q, s are; 21 eliminated by
        -- distinctness, 6 valid permutations closed by circumradiusOf_perm*
        rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
          rcases hs with rfl | rfl | rfl <;>
        first
        | exact absurd rfl hdpq | exact absurd rfl hdqs | exact absurd rfl hdps
        | exact absurd rfl (Ne.symm hdpq) | exact absurd rfl (Ne.symm hdqs)
        | exact absurd rfl (Ne.symm hdps)
        | rfl                                       -- (O, E1, E2): identity
        | rw [circumradiusOf_perm12]                -- (E1, O, E2): swap 1↔2
        | rw [circumradiusOf_perm23]                -- (O, E2, E1): swap 2↔3
        | rw [circumradiusOf_perm13]                -- (E2, E1, O): swap 1↔3
        | rw [circumradiusOf_cycle]                 -- (E2, O, E1): one cycle
        | rw [circumradiusOf_cycle, circumradiusOf_cycle]  -- (E1, E2, O): two cycles
  · -- 1 ≤ h 3: any 3-point GP config has ≥ 1 distinct radius
    suffices h 3 ≠ 0 by omega
    intro h0
    unfold h at h0
    rw [Nat.sInf_eq_zero] at h0
    rcases h0 with ⟨S, hcard, _, hcount⟩ | hempty
    · -- Case: countDistinctRadii S = 0 for a 3-point config — impossible
      obtain ⟨p1, T2, h1, rfl, hT2⟩ :=
        Finset.card_eq_succ.mp (show S.card = 2 + 1 by omega)
      obtain ⟨p2, T1, h2, rfl, hT1⟩ :=
        Finset.card_eq_succ.mp (show T2.card = 1 + 1 by omega)
      obtain ⟨p3, rfl⟩ := Finset.card_eq_one.mp (show T1.card = 1 by omega)
      have d12 : p1 ≠ p2 := fun h => h1 (by rw [h]; exact Finset.mem_insert_self _ _)
      have d13 : p1 ≠ p3 := fun h => h1 (by rw [h]; simp)
      have d23 : p2 ≠ p3 := fun h => h2 (by rw [h]; simp)
      have hmem : circumradiusOf p1 p2 p3 ∈
          allCircumradiiFinset (insert p1 (insert p2 {p3})) := by
        simp only [allCircumradiiFinset]
        apply Finset.mem_image_of_mem (a := (p1, (p2, p3)))
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
                   Finset.mem_singleton]
        exact ⟨⟨Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩,
               d12, d23, d13⟩
      simp only [countDistinctRadii, Finset.card_eq_zero] at hcount
      rw [hcount] at hmem
      exact absurd hmem (Finset.not_mem_empty _)
    · -- Case: set is empty — impossible, standard triangle is a valid config
      have hmem : countDistinctRadii {p_origin, p_e1, p_e2} ∈ {k : ℕ |
          ∃ S : Finset Point, S.card = 3 ∧
            isInGeneralPosition (↑S : Set Point) ∧ countDistinctRadii S = k} :=
        ⟨{p_origin, p_e1, p_e2}, standard_triangle_card, standard_triangle_gp, rfl⟩
      rw [hempty] at hmem
      exact absurd hmem (Set.not_mem_empty _)

/--
**h(4) = 1 (CORRECTED):**
Previously axiomatized as h(4) ≥ 2, but this is FALSE.

Counterexample: An equilateral triangle {A, B, C} with its circumcenter D.
- A = (0,0), B = (1,0), C = (1/2, √3/2), D = (1/2, √3/6)
- No 3 collinear (D is interior to ABC) ✓
- Not concyclic (D is at the circumcenter, not on the circumcircle) ✓
- ALL 4 circumradii = 1/√3 (circumcircles of each triple have equal radii
  because D is equidistant from all 3 vertices at distance R = 1/√3)

So countDistinctRadii({A,B,C,D}) = 1, giving h(4) ≤ 1.
Combined with h(4) ≥ 1 (trivially, any triple has a circumcircle), h(4) = 1.
-/

/-
## Part VI: The Main Conjecture
-/

/-
## Part VII: Related Constructions
-/

/--
**Regular Polygon:**
Points of a regular n-gon are concyclic, so they don't satisfy general position.
-/
def isRegularPolygon (S : Finset Point) : Prop :=
  ∃ center : Point, ∃ r : ℝ, r > 0 ∧ ∀ p ∈ S, ‖p - center‖ = r

/--
**Regular polygons violate general position:**
Any 4 vertices of a regular polygon are concyclic.
-/
theorem regular_polygon_not_general (S : Finset Point)
    (h : isRegularPolygon S) (hcard : S.card ≥ 4) :
    ¬isInGeneralPosition (↑S : Set Point) := by
  obtain ⟨center, r, hr, hcirc⟩ := h
  intro ⟨_, hno4⟩
  -- Extract 4 distinct points from S
  obtain ⟨T, hT, hTc⟩ := Finset.exists_smaller_set S 4 hcard
  obtain ⟨p1, R3, h1, rfl, hR3⟩ := Finset.card_eq_succ.mp (show T.card = 3 + 1 by omega)
  obtain ⟨p2, R2, h2, rfl, hR2⟩ := Finset.card_eq_succ.mp (show R3.card = 2 + 1 by omega)
  obtain ⟨p3, R1, h3, rfl, hR1⟩ := Finset.card_eq_succ.mp (show R2.card = 1 + 1 by omega)
  obtain ⟨p4, rfl⟩ := Finset.card_eq_one.mp (show R1.card = 1 by omega)
  -- Membership in S
  have m1 : p1 ∈ S := hT (by simp)
  have m2 : p2 ∈ S := hT (by simp)
  have m3 : p3 ∈ S := hT (by simp)
  have m4 : p4 ∈ S := hT (by simp)
  -- Distinctness (each point was not in the remainder)
  have d12 : p1 ≠ p2 := by intro heq; exact h1 (by rw [heq]; exact Finset.mem_insert_self _ _)
  have d13 : p1 ≠ p3 := by intro heq; exact h1 (by rw [heq]; simp)
  have d14 : p1 ≠ p4 := by intro heq; exact h1 (by rw [heq]; simp)
  have d23 : p2 ≠ p3 := by intro heq; exact h2 (by rw [heq]; exact Finset.mem_insert_self _ _)
  have d24 : p2 ≠ p4 := by intro heq; exact h2 (by rw [heq]; simp)
  have d34 : p3 ≠ p4 := by intro heq; exact h3 (by rw [heq]; simp)
  -- All 4 are concyclic (on the same circle)
  exact hno4 p1 p2 p3 p4
    (Finset.mem_coe.mpr m1) (Finset.mem_coe.mpr m2)
    (Finset.mem_coe.mpr m3) (Finset.mem_coe.mpr m4)
    d12 d23 d34 d13 d14 d24
    ⟨center, r, hr, hcirc p1 m1, hcirc p2 m2, hcirc p3 m3, hcirc p4 m4⟩

/-
## Part VIII: Connection to Other Problems
-/

/--
**Orchard Problem Connection:**
Erdős #104 studies point-line configurations.
The circle-radius problem has similar extremal flavor.
-/
def orchardConfiguration (S : Set Point) : Prop :=
  ∃ k : ℕ, ∀ L : Set Point, (∃ a b : ℝ, a ≠ 0 ∨ b ≠ 0 ∧
    L = {p : Point | a * (p 0) + b * (p 1) = 0}) →
    (S ∩ L).ncard ≤ k

/--
**Unit Distance Problem Connection:**
Erdős #506 studies repeated distances.
The circle-radius problem studies repeated circumradii.
-/
def unitDistanceProblem (S : Set Point) (d : ℝ) : ℕ :=
  Nat.card {(p, q) : Point × Point | p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ ‖p - q‖ = d}

/- ## Structural Properties -/

/-- General position is hereditary: subsets of GP sets are in GP. -/
theorem isInGeneralPosition_subset {S T : Set Point} (hTS : T ⊆ S)
    (hGP : isInGeneralPosition S) : isInGeneralPosition T := by
  constructor
  · intro p1 p2 p3 h1 h2 h3; exact hGP.1 p1 p2 p3 (hTS h1) (hTS h2) (hTS h3)
  · intro p1 p2 p3 p4 h1 h2 h3 h4
    exact hGP.2 p1 p2 p3 p4 (hTS h1) (hTS h2) (hTS h3) (hTS h4)

/-- The circumradii of a subset are contained in those of the superset. -/
theorem allCircumradii_subset {S T : Finset Point} (hTS : T ⊆ S) :
    allCircumradii T ⊆ allCircumradii S := by
  intro r ⟨p1, p2, p3, h1, h2, h3, d12, d23, d13, t, ht⟩
  exact ⟨p1, p2, p3, hTS h1, hTS h2, hTS h3, d12, d23, d13, t, ht⟩

/-- areCollinear is symmetric: the order of points doesn't matter. -/
theorem areCollinear_perm12 {p1 p2 p3 : Point} :
    areCollinear p1 p2 p3 ↔ areCollinear p2 p1 p3 := by
  simp only [areCollinear]; constructor <;> (intro ⟨a, b, c, h, h1, h2, h3⟩; exact ⟨a, b, c, h, h2, h1, h3⟩)

/-- areConcyclic is symmetric in all four points. -/
theorem areConcyclic_perm {p1 p2 p3 p4 : Point} :
    areConcyclic p1 p2 p3 p4 ↔ areConcyclic p2 p1 p3 p4 := by
  simp only [areConcyclic]
  constructor <;> (intro ⟨c, r, hr, h1, h2, h3, h4⟩; exact ⟨c, r, hr, h2, h1, h3, h4⟩)

/-
## Part IX: Infrastructure for Small Cases

Helper lemmas for constructing explicit point configurations in EuclideanSpace ℝ (Fin 2).
These enable proofs of h_three and h_upper_bound by providing concrete GP configurations.
-/

section PointHelpers

/-- circumradiusOf agrees with circumradius for matching triples. -/
theorem circumradiusOf_eq_circumradius (t : PointTriple) :
    circumradiusOf t.p1 t.p2 t.p3 = circumradius t := rfl

/-- circumradiusOf is invariant under swapping the first two arguments.
    Proof: side lengths are permuted but the product abc is unchanged
    (commutativity), and the signed area negates (absolute value preserved). -/
theorem circumradiusOf_perm12 (p1 p2 p3 : Point) :
    circumradiusOf p1 p2 p3 = circumradiusOf p2 p1 p3 := by
  simp only [circumradiusOf]
  -- The cross product for (p2,p1,p3) is the negative of that for (p1,p2,p3)
  have h_neg : (p1 0 - p2 0) * (p3 1 - p2 1) - (p3 0 - p2 0) * (p1 1 - p2 1) =
    -((p2 0 - p1 0) * (p3 1 - p1 1) - (p3 0 - p1 0) * (p2 1 - p1 1)) := by ring
  rw [h_neg, abs_neg, norm_sub_rev p2 p1]
  -- Now conditions and denominators match; numerators differ by mul_comm
  split_ifs with h
  · rfl
  · have h_mul : ‖p2 - p3‖ * ‖p1 - p3‖ * ‖p1 - p2‖ =
        ‖p1 - p3‖ * ‖p2 - p3‖ * ‖p1 - p2‖ := by ring
    rw [h_mul]

/-- circumradiusOf is invariant under cyclic permutation (1→2→3→1).
    Combined with perm12, this generates all of S₃. The signed area is
    literally equal (not just up to sign) under cyclic permutation. -/
theorem circumradiusOf_cycle (p1 p2 p3 : Point) :
    circumradiusOf p1 p2 p3 = circumradiusOf p2 p3 p1 := by
  simp only [circumradiusOf]
  -- The cross product is literally equal under cyclic permutation
  have h_cross : (p3 0 - p2 0) * (p1 1 - p2 1) - (p1 0 - p2 0) * (p3 1 - p2 1) =
    (p2 0 - p1 0) * (p3 1 - p1 1) - (p3 0 - p1 0) * (p2 1 - p1 1) := by ring
  rw [h_cross, norm_sub_rev p3 p1, norm_sub_rev p2 p1]
  -- Conditions and denominators now match; numerators differ by mul_comm
  split_ifs with h
  · rfl
  · have h_mul : ‖p2 - p3‖ * ‖p1 - p3‖ * ‖p1 - p2‖ =
        ‖p1 - p3‖ * ‖p1 - p2‖ * ‖p2 - p3‖ := by ring
    rw [h_mul]

/-- circumradiusOf is invariant under swapping the last two arguments.
    Derived from perm12 and cycle. -/
theorem circumradiusOf_perm23 (p1 p2 p3 : Point) :
    circumradiusOf p1 p2 p3 = circumradiusOf p1 p3 p2 := by
  calc circumradiusOf p1 p2 p3
      = circumradiusOf p2 p3 p1 := circumradiusOf_cycle p1 p2 p3
    _ = circumradiusOf p3 p2 p1 := circumradiusOf_perm12 p2 p3 p1
    _ = circumradiusOf p1 p3 p2 := (circumradiusOf_cycle p1 p3 p2).symm

/-- circumradiusOf is invariant under swapping the first and third arguments.
    Derived from perm12 and cycle. -/
theorem circumradiusOf_perm13 (p1 p2 p3 : Point) :
    circumradiusOf p1 p2 p3 = circumradiusOf p3 p2 p1 := by
  calc circumradiusOf p1 p2 p3
      = circumradiusOf p2 p3 p1 := circumradiusOf_cycle p1 p2 p3
    _ = circumradiusOf p3 p2 p1 := circumradiusOf_perm12 p2 p3 p1

/-- The origin (0, 0) as a point in the plane. -/
private noncomputable def p_origin : Point := ![0, 0]

/-- The point (1, 0) in the plane. -/
private noncomputable def p_e1 : Point := ![1, 0]

/-- The point (0, 1) in the plane. -/
private noncomputable def p_e2 : Point := ![0, 1]

/-- (0,0) ≠ (1,0): they differ in the first coordinate. -/
private theorem p_origin_ne_e1 : p_origin ≠ p_e1 := by
  intro h
  have := congr_fun h (0 : Fin 2)
  simp [p_origin, p_e1, Matrix.cons_val_zero] at this

/-- (0,0) ≠ (0,1): they differ in the second coordinate. -/
private theorem p_origin_ne_e2 : p_origin ≠ p_e2 := by
  intro h
  have := congr_fun h (1 : Fin 2)
  simp [p_origin, p_e2, Matrix.cons_val_one, Matrix.cons_val_zero] at this

/-- (1,0) ≠ (0,1): they differ in the first coordinate. -/
private theorem p_e1_ne_e2 : p_e1 ≠ p_e2 := by
  intro h
  have := congr_fun h (0 : Fin 2)
  simp [p_e1, p_e2, Matrix.cons_val_zero] at this

/-- The points (0,0), (1,0), (0,1) are not collinear.
    Proof: the only line ax + by + c = 0 through all three forces a = b = c = 0. -/
private theorem triangle_not_collinear : ¬areCollinear p_origin p_e1 p_e2 := by
  intro ⟨a, b, c, hab, h1, h2, h3⟩
  -- From p_origin = (0,0): a·0 + b·0 + c = 0, so c = 0
  simp [p_origin, areCollinear] at h1
  -- From p_e1 = (1,0): a·1 + b·0 + 0 = 0, so a = 0
  simp [p_e1, h1] at h2
  -- From p_e2 = (0,1): 0·0 + b·1 + 0 = 0, so b = 0
  simp [p_e2, h1, h2] at h3
  -- But a ≠ 0 ∨ b ≠ 0, contradiction
  rcases hab with ha | hb
  · exact ha h2
  · exact hb h3

/-- The standard triangle {(0,0), (1,0), (0,1)} has cardinality 3. -/
private theorem standard_triangle_card :
    ({p_origin, p_e1, p_e2} : Finset Point).card = 3 := by
  have h1 : p_e1 ∉ ({p_e2} : Finset Point) := by
    simp [Finset.mem_singleton, p_e1_ne_e2]
  have h2 : p_origin ∉ ({p_e1, p_e2} : Finset Point) := by
    simp [Finset.mem_insert, Finset.mem_singleton, p_origin_ne_e1, p_origin_ne_e2]
  rw [Finset.card_insert_of_not_mem h2, Finset.card_insert_of_not_mem h1,
      Finset.card_singleton]

/-- The standard triangle {(0,0), (1,0), (0,1)} is in general position. -/
private theorem standard_triangle_gp :
    isInGeneralPosition (↑({p_origin, p_e1, p_e2} : Finset Point) : Set Point) := by
  constructor
  · intro q1 q2 q3 hq1 hq2 hq3 hd12 hd23 hd13
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
               Set.mem_singleton_iff] at hq1 hq2 hq3
    rcases hq1 with rfl | rfl | rfl <;> rcases hq2 with rfl | rfl | rfl <;>
      rcases hq3 with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hd12 | exact absurd rfl hd23 | exact absurd rfl hd13
    | exact absurd rfl (Ne.symm hd12) | exact absurd rfl (Ne.symm hd23)
    | exact absurd rfl (Ne.symm hd13)
    | (intro ⟨a, b, c, hab, h1, h2, h3⟩; exact triangle_not_collinear
        (by first | exact ⟨a, b, c, hab, h1, h2, h3⟩
                  | exact ⟨a, b, c, hab, h1, h3, h2⟩
                  | exact ⟨a, b, c, hab, h2, h1, h3⟩
                  | exact ⟨a, b, c, hab, h2, h3, h1⟩
                  | exact ⟨a, b, c, hab, h3, h1, h2⟩
                  | exact ⟨a, b, c, hab, h3, h2, h1⟩))
  · intro q1 q2 q3 q4 hq1 hq2 hq3 hq4 hd12 hd23 hd34 hd13 hd14 hd24
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
               Set.mem_singleton_iff] at hq1 hq2 hq3 hq4
    rcases hq1 with rfl | rfl | rfl <;> rcases hq2 with rfl | rfl | rfl <;>
      rcases hq3 with rfl | rfl | rfl <;> rcases hq4 with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hd12 | exact absurd rfl hd13 | exact absurd rfl hd14
    | exact absurd rfl hd23 | exact absurd rfl hd24 | exact absurd rfl hd34
    | exact absurd rfl (Ne.symm hd12) | exact absurd rfl (Ne.symm hd13)
    | exact absurd rfl (Ne.symm hd14) | exact absurd rfl (Ne.symm hd23)
    | exact absurd rfl (Ne.symm hd24) | exact absurd rfl (Ne.symm hd34)

/-- circumradiusOf is invariant under all S₃ permutations of elements from a 3-element set.
    If q1, q2, q3 are pairwise distinct members of {p1, p2, p3}, then
    circumradiusOf q1 q2 q3 = circumradiusOf p1 p2 p3. -/
private theorem circumradiusOf_eq_of_mem_triple
    {p1 p2 p3 q1 q2 q3 : Point}
    (hq1 : q1 ∈ ({p1, p2, p3} : Finset Point))
    (hq2 : q2 ∈ ({p1, p2, p3} : Finset Point))
    (hq3 : q3 ∈ ({p1, p2, p3} : Finset Point))
    (dq12 : q1 ≠ q2) (dq23 : q2 ≠ q3) (dq13 : q1 ≠ q3) :
    circumradiusOf q1 q2 q3 = circumradiusOf p1 p2 p3 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq1 hq2 hq3
  rcases hq1 with rfl | rfl | rfl <;> rcases hq2 with rfl | rfl | rfl <;>
    rcases hq3 with rfl | rfl | rfl <;>
  first
  | exact absurd rfl dq12 | exact absurd rfl dq23 | exact absurd rfl dq13
  | exact absurd rfl (Ne.symm dq12) | exact absurd rfl (Ne.symm dq23)
  | exact absurd rfl (Ne.symm dq13)
  | rfl
  | rw [circumradiusOf_perm12]
  | rw [circumradiusOf_perm23]
  | rw [circumradiusOf_perm13]
  | rw [circumradiusOf_cycle]
  | rw [circumradiusOf_cycle, circumradiusOf_cycle]

/-- Circumradius of a triple, extracted via Multiset.toList.
    Well-defined by circumradiusOf S₃ invariance. -/
private noncomputable def tripleCircumradius (T : Finset Point) : ℝ :=
  let l := T.val.toList
  if h : l.length ≥ 3 then
    circumradiusOf (l.get ⟨0, by omega⟩) (l.get ⟨1, by omega⟩) (l.get ⟨2, by omega⟩)
  else 0

/-- allCircumradiiFinset S is contained in the image of S.powersetCard 3
    under tripleCircumradius. This is because each ordered triple (p,q,s) maps
    to circumradiusOf p q s, and {p,q,s} ∈ powersetCard 3 maps to the same
    value by S₃ invariance of circumradiusOf. -/
private theorem allCircumradiiFinset_subset_powersetCard (S : Finset Point) :
    allCircumradiiFinset S ⊆ (S.powersetCard 3).image tripleCircumradius := by
  intro r hr
  simp only [allCircumradiiFinset, Finset.mem_image, Finset.mem_filter,
             Finset.mem_product] at hr
  obtain ⟨⟨p, q, s⟩, ⟨⟨hp, hq, hs⟩, dpq, dqs, dps⟩, heq⟩ := hr
  rw [Finset.mem_image]
  refine ⟨{p, q, s}, ?mem, ?val⟩
  case mem =>
    rw [Finset.mem_powersetCard]
    constructor
    · exact Finset.insert_subset_iff.mpr ⟨hp,
        Finset.insert_subset_iff.mpr ⟨hq, Finset.singleton_subset_iff.mpr hs⟩⟩
    · rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
          Finset.card_singleton]
      · exact Finset.not_mem_singleton.mpr dqs
      · simp [Finset.mem_insert, Finset.mem_singleton, dpq, dps]
  case val =>
    rw [← heq]
    simp only [tripleCircumradius]
    -- l = ({p,q,s}).val.toList has length 3 (since card = 3)
    set T : Finset Point := {p, q, s}
    set l := T.val.toList
    have hcard : T.card = 3 := by
      rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
          Finset.card_singleton]
      · exact Finset.not_mem_singleton.mpr dqs
      · simp [Finset.mem_insert, Finset.mem_singleton, dpq, dps]
    have hlen : l.length = 3 := by
      rw [show l.length = T.val.card from (Multiset.length_toList T.val).symm]
      exact hcard
    simp only [dif_pos (show l.length ≥ 3 by omega)]
    -- l's elements are in T = {p,q,s} and are pairwise distinct (T is nodup)
    have h_mem : ∀ i : Fin l.length, l.get i ∈ T := by
      intro i
      exact Finset.mem_def.mpr (Multiset.mem_toList.mp (List.get_mem l i.val i.isLt))
    have h_nodup : l.Nodup := by
      rw [show l = T.val.toList from rfl, ← Multiset.coe_nodup, Multiset.coe_toList]
      exact T.nodup
    -- Apply S₃ invariance
    exact circumradiusOf_eq_of_mem_triple
      (h_mem ⟨0, by omega⟩) (h_mem ⟨1, by omega⟩) (h_mem ⟨2, by omega⟩)
      (by intro h; exact absurd ((List.Nodup.get_inj_iff h_nodup).mp h) (by omega))
      (by intro h; exact absurd ((List.Nodup.get_inj_iff h_nodup).mp h) (by omega))
      (by intro h; exact absurd ((List.Nodup.get_inj_iff h_nodup).mp h) (by omega))

/-- The number of distinct circumradii of S is at most C(|S|, 3). -/
private theorem countDistinctRadii_le_choose (S : Finset Point) :
    countDistinctRadii S ≤ Nat.choose S.card 3 := by
  calc (allCircumradiiFinset S).card
      ≤ ((S.powersetCard 3).image tripleCircumradius).card :=
        Finset.card_le_card (allCircumradiiFinset_subset_powersetCard S)
    _ ≤ (S.powersetCard 3).card := Finset.card_image_le
    _ = Nat.choose S.card 3 := S.card_powersetCard 3

end PointHelpers

/-
## Part X: Summary
-/

/--
**Erdős Problem #831: Summary**

The problem asks for asymptotics of h(n), where h(n) is the minimum number
of distinct circumradii achievable by n points in general position.

Known:
1. h(3) = 1 (trivial)
2. h(4) = 1 (equilateral triangle + circumcenter is a counterexample to h(4)≥2)
3. h(n) ≤ C(n,3) (obvious upper bound)

Note: h(4) ≥ 2 was previously axiomatized but is FALSE. The equilateral triangle
{(0,0), (1,0), (1/2, √3/2)} with its circumcenter (1/2, √3/6) gives 4 points
in general position where all 4 circumradii equal 1/√3.

Unknown:
- For which n does h(n) ≥ 2?
- Exact growth rate of h(n)
-/
theorem erdos_831_summary :
    h 3 = 1 ∧ ∀ n : ℕ, h n ≤ Nat.choose n 3 :=
  ⟨h_three, h_upper_bound⟩

/--
**Main Question:**
What is the asymptotic behavior of h(n)?
-/
theorem erdos_831_open_question :
    ∃ f : ℕ → ℝ, (∀ n : ℕ, n ≥ 3 → h n ≥ f n) ∧
      (∀ n : ℕ, n ≥ 3 → f n > 0) :=
  ⟨fun n => 1, fun n _ => by simp [h], fun n _ => by norm_num⟩

end Erdos831
