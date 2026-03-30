/-
Erdős Problem #1082: Distinct Distances in General Position

Source: https://erdosproblems.com/1082
Status: OPEN (second question disproved)

Statement:
Let A ⊂ ℝ² be a set of n points with no three on a line.
(1) Does A determine at least ⌊n/2⌋ distinct distances?
(2) Must there exist a single point from which there are at least ⌊n/2⌋ distinct distances?

Partial Answer:
- Question (1): OPEN
- Question (2): DISPROVED by Xichuan (2020s) with 42-point counterexample

Key Results:
- Szemerédi: Proved n/3 bound (unpublished, cited in Erdős 1975)
- Szemerédi: If no k points on a line, some point determines ≫ n/k distances
- Xichuan: 42 points in ℝ² with no three collinear, each point has only 20 distances

The problem connects to the famous distinct distances problem and incidence geometry.

References:
- Erdős [Er75f]: "On some problems of elementary and combinatorial geometry"
- Szemerédi: unpublished proof for n/3 bound
- Xichuan: counterexample to question (2)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

open Finset Real

namespace Erdos1082

/-
## Part I: Points and Distances in ℝ²
-/

/-- A point in the Euclidean plane -/
abbrev Point2D := EuclideanSpace ℝ (Fin 2)

/-- Extract x-coordinate -/
def Point2D.x (p : Point2D) : ℝ := p 0

/-- Extract y-coordinate -/
def Point2D.y (p : Point2D) : ℝ := p 1

/-- Squared Euclidean distance between two points -/
noncomputable def distSq (p q : Point2D) : ℝ :=
  (p.x - q.x)^2 + (p.y - q.y)^2

/-- Euclidean distance between two points -/
noncomputable def dist' (p q : Point2D) : ℝ :=
  Real.sqrt (distSq p q)

/-
## Part II: Distance Properties
-/

/-- Squared distance is non-negative -/
theorem distSq_nonneg (p q : Point2D) : distSq p q ≥ 0 := by
  unfold distSq
  apply add_nonneg <;> apply sq_nonneg

/-- Squared distance is symmetric -/
theorem distSq_comm (p q : Point2D) : distSq p q = distSq q p := by
  unfold distSq Point2D.x Point2D.y
  ring

/-- Distance is non-negative -/
theorem dist'_nonneg (p q : Point2D) : dist' p q ≥ 0 := by
  unfold dist'
  exact Real.sqrt_nonneg _

/-- Distance is symmetric -/
theorem dist'_comm (p q : Point2D) : dist' p q = dist' q p := by
  unfold dist'
  rw [distSq_comm]

/-- Squared distance to self is zero -/
theorem distSq_self (p : Point2D) : distSq p p = 0 := by
  unfold distSq Point2D.x Point2D.y
  ring

/-- Distance to self is zero -/
theorem dist'_self (p : Point2D) : dist' p p = 0 := by
  unfold dist'
  rw [distSq_self]
  exact Real.sqrt_zero

/-- Squared distance is zero iff points are equal -/
theorem distSq_eq_zero_iff (p q : Point2D) : distSq p q = 0 ↔ p = q := by
  constructor
  · intro h
    unfold distSq Point2D.x Point2D.y at h
    have hx : (p 0 - q 0)^2 = 0 := by nlinarith [sq_nonneg (p 0 - q 0), sq_nonneg (p 1 - q 1)]
    have hy : (p 1 - q 1)^2 = 0 := by nlinarith [sq_nonneg (p 0 - q 0), sq_nonneg (p 1 - q 1)]
    have hx' : p 0 = q 0 := by nlinarith [sq_abs (p 0 - q 0)]
    have hy' : p 1 = q 1 := by nlinarith [sq_abs (p 1 - q 1)]
    ext i
    fin_cases i <;> assumption
  · intro h
    rw [h]
    exact distSq_self q

/-- Positive squared distance implies distinct points -/
theorem distSq_pos_of_ne {p q : Point2D} (h : p ≠ q) : distSq p q > 0 := by
  rcases lt_or_eq_of_le (distSq_nonneg p q) with hlt | heq
  · exact hlt
  · exfalso
    exact h ((distSq_eq_zero_iff p q).mp heq.symm)

/-- Positive distance for distinct points -/
theorem dist'_pos_of_ne {p q : Point2D} (h : p ≠ q) : dist' p q > 0 := by
  unfold dist'
  exact Real.sqrt_pos.mpr (distSq_pos_of_ne h)

/-
## Part III: General Position (No Three Collinear)
-/

/-- Three points are collinear if they lie on a common line -/
def areCollinear (p q r : Point2D) : Prop :=
  (q.x - p.x) * (r.y - p.y) = (r.x - p.x) * (q.y - p.y)

/-- Collinearity is invariant under cyclic permutation -/
theorem areCollinear_cycle {p q r : Point2D} (h : areCollinear p q r) :
    areCollinear q r p := by
  unfold areCollinear Point2D.x Point2D.y at *
  nlinarith

/-- Collinearity is invariant under transposition of last two -/
theorem areCollinear_swap23 {p q r : Point2D} (h : areCollinear p q r) :
    areCollinear p r q := by
  unfold areCollinear Point2D.x Point2D.y at *
  linarith

/-- A point set is in general position if no three points are collinear -/
def inGeneralPosition (S : Finset Point2D) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → q ≠ r → p ≠ r → ¬areCollinear p q r

/-- A subset of a set in general position is also in general position -/
theorem inGeneralPosition_subset {S T : Finset Point2D} (hST : S ⊆ T)
    (hT : inGeneralPosition T) : inGeneralPosition S := by
  intro p hp q hq r hr hpq hqr hpr
  exact hT p (hST hp) q (hST hq) r (hST hr) hpq hqr hpr

/-
## Part IV: Counting Distinct Distances
-/

/-- The set of distinct distances determined by a point set -/
noncomputable def distinctDistances (S : Finset Point2D) : Finset ℝ :=
  (S ×ˢ S).image (fun pq => dist' pq.1 pq.2)

/-- The set of distinct distances from a single point to all others -/
noncomputable def distancesFromPoint (p : Point2D) (S : Finset Point2D) : Finset ℝ :=
  (S.filter (· ≠ p)).image (fun q => dist' p q)

/-- Count of distinct distances from a point -/
noncomputable def numDistancesFromPoint (p : Point2D) (S : Finset Point2D) : ℕ :=
  (distancesFromPoint p S).card

/-- Distances from any point in S are a subset of all distinct distances -/
theorem distancesFromPoint_subset (p : Point2D) (S : Finset Point2D) (hp : p ∈ S) :
    distancesFromPoint p S ⊆ distinctDistances S := by
  intro d hd
  simp only [distancesFromPoint, distinctDistances, mem_image, mem_filter, mem_product] at hd ⊢
  obtain ⟨q, ⟨hqS, _⟩, hd_eq⟩ := hd
  exact ⟨(p, q), ⟨hp, hqS⟩, hd_eq⟩

/-- The number of distances from any point is at most the total distinct distances -/
theorem numDistancesFromPoint_le_distinctDistances (p : Point2D) (S : Finset Point2D)
    (hp : p ∈ S) :
    numDistancesFromPoint p S ≤ (distinctDistances S).card := by
  exact card_le_card (distancesFromPoint_subset p S hp)

/-
## Part V: Szemerédi's Theorem (n/3 bound)
-/

/--
**Szemerédi's Theorem (unpublished, ~1975):**
If S has n points in general position, then S determines at least n/3 distinct distances.
-/
axiom szemeredi_n_over_3 (S : Finset Point2D) (h : inGeneralPosition S) :
    (distinctDistances S).card ≥ S.card / 3

/--
**Szemerédi's Stronger Result:**
If S has n points with no k on a line, then some point determines ≫ n/k distances.
-/
/-
## Part VI: The Conjectures
-/

/--
**Conjecture 1 (OPEN):**
If S has n points in general position, then S determines at least ⌊n/2⌋ distinct distances.
-/
def Conjecture1 : Prop :=
  ∀ S : Finset Point2D, inGeneralPosition S →
    (distinctDistances S).card ≥ S.card / 2

/--
**Conjecture 2 (DISPROVED):**
If S has n points in general position, then some point determines at least ⌊n/2⌋
distinct distances to other points in S.
-/
def Conjecture2 : Prop :=
  ∀ S : Finset Point2D, inGeneralPosition S →
    ∃ p ∈ S, numDistancesFromPoint p S ≥ S.card / 2

/-- Conjecture 2 implies Conjecture 1: the single-point version is stronger -/
theorem conjecture2_implies_conjecture1 (h : Conjecture2) : Conjecture1 := by
  intro S hGen
  obtain ⟨p, hp, hDist⟩ := h S hGen
  calc (distinctDistances S).card
      ≥ numDistancesFromPoint p S :=
        numDistancesFromPoint_le_distinctDistances p S hp
    _ ≥ S.card / 2 := hDist

/-- Conjecture 1 would strengthen Szemerédi's n/3 bound -/
theorem conjecture1_strengthens_szemeredi (h : Conjecture1) :
    ∀ S : Finset Point2D, inGeneralPosition S →
      (distinctDistances S).card ≥ S.card / 3 := by
  intro S hGen
  have h2 := h S hGen
  omega

/-
## Part VII: Xichuan's Counterexample to Conjecture 2
-/

/--
**Xichuan's Counterexample:**
There exist 42 points in ℝ² with no three collinear, such that
every point determines only 20 distinct distances.
Since 20 < 42/2 = 21, this disproves Conjecture 2.
-/
axiom xichuan_counterexample :
    ∃ S : Finset Point2D, S.card = 42 ∧ inGeneralPosition S ∧
      ∀ p ∈ S, numDistancesFromPoint p S ≤ 20

/-- Conjecture 2 is FALSE -/
theorem conjecture2_false : ¬Conjecture2 := by
  intro hConj2
  obtain ⟨S, hCard, hGen, hAll⟩ := xichuan_counterexample
  obtain ⟨p, hp, hDist⟩ := hConj2 S hGen
  have h42 : S.card / 2 = 21 := by simp [hCard]
  rw [h42] at hDist
  have hBad := hAll p hp
  omega

/-- The counterexample witnesses a strict gap below n/2 -/
theorem counterexample_gap :
    ∃ S : Finset Point2D, S.card = 42 ∧ inGeneralPosition S ∧
      (∀ p ∈ S, numDistancesFromPoint p S < S.card / 2) := by
  obtain ⟨S, hCard, hGen, hAll⟩ := xichuan_counterexample
  use S, hCard, hGen
  intro p hp
  have h := hAll p hp
  simp [hCard] at *
  omega

/-- The counterexample still satisfies Szemerédi's n/3 bound (consistency check) -/
theorem counterexample_consistent_with_szemeredi :
    ∃ S : Finset Point2D, S.card = 42 ∧ inGeneralPosition S ∧
      (distinctDistances S).card ≥ S.card / 3 := by
  obtain ⟨S, hCard, hGen, _⟩ := xichuan_counterexample
  exact ⟨S, hCard, hGen, szemeredi_n_over_3 S hGen⟩

/-
## Part VIII: The Gap Between n/3 and n/2
-/

/-- For any n, ⌊n/3⌋ ≤ ⌊n/2⌋ -/
theorem div3_le_div2 (n : ℕ) : n / 3 ≤ n / 2 := by
  omega

/-- The conjectured improvement: n/2 vs proven n/3 -/
theorem szemeredi_weaker_than_conjecture1 :
    (∀ S : Finset Point2D, inGeneralPosition S →
      (distinctDistances S).card ≥ S.card / 2) →
    (∀ S : Finset Point2D, inGeneralPosition S →
      (distinctDistances S).card ≥ S.card / 3) := by
  intro h S hGen
  have h2 := h S hGen
  have h3 := div3_le_div2 S.card
  omega

/-- The falsity of Conjecture 2 does NOT logically imply the falsity of Conjecture 1.
    C2 is a per-point statement; C1 is about total distances. The counterexample shows
    no single point sees n/2 distances, but multiple points together could still produce
    n/2 total distinct distances.

    To formalize this precisely: C2 → C1 is proved above, but ¬C2 does NOT give ¬C1.
    We document this as a remark rather than a theorem, since proving C1 remains OPEN. -/
theorem conjecture2_false_does_not_imply_conjecture1_false_note :
    -- The implication C2 → C1 holds
    (Conjecture2 → Conjecture1) ∧
    -- But C2 is false
    ¬Conjecture2 := by
  exact ⟨conjecture2_implies_conjecture1, conjecture2_false⟩

/-
## Part IX: Connection to Erdős Problem #89
-/

/--
**Guth-Katz (2015):**
Every set of n points in ℝ² determines Ω(n/log n) distinct distances.
For sets in general position, this gives a lower bound independent of
the n/2 conjecture.
-/
/-
## Part X: Summary
-/

/--
**Erdős Problem #1082: Summary**

| Statement | Status | Reference |
|-----------|--------|-----------|
| Total ≥ n/3 distances | PROVED | Szemerédi |
| Total ≥ n/2 distances | OPEN | Conjecture 1 |
| Some point ≥ n/2 distances | DISPROVED | Xichuan |
| C2 → C1 | PROVED | conjecture2_implies_conjecture1 |
-/
theorem erdos_1082_status :
    -- Szemerédi's proven bound
    (∀ S : Finset Point2D, inGeneralPosition S → (distinctDistances S).card ≥ S.card / 3) ∧
    -- Conjecture 2 is false
    ¬Conjecture2 ∧
    -- C2 would have implied C1
    (Conjecture2 → Conjecture1) := by
  exact ⟨szemeredi_n_over_3, conjecture2_false, conjecture2_implies_conjecture1⟩

end Erdos1082
