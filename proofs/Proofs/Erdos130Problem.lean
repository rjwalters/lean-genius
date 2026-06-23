/-
# Erdős Problem #130 — Integer Distance Graphs with No Collinear/Cocircular Points

Given an infinite set A ⊆ ℝ² with no three points collinear and no four
points cocircular, form a graph G(A) whose vertices are A and whose edges
connect pairs at integer distance.

Questions:
1. Can the chromatic number χ(G(A)) be infinite?
2. Can the clique number ω(G(A)) be infinite?
3. How large can χ(G(A)) be?

Known: Anning–Erdős (1945) showed ω(G(A)) must be finite under these
conditions. The chromatic number question remains open.

Status: OPEN
Reference: https://erdosproblems.com/130
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

/- ## Definitions -/

/-- A point in the plane. -/
structure Point2 where
  x : ℝ
  y : ℝ

/-- Squared Euclidean distance between two points. -/
noncomputable def distSq (p q : Point2) : ℝ :=
  (p.x - q.x) ^ 2 + (p.y - q.y) ^ 2

/-- Three points are collinear. -/
def AreCollinear (p q r : Point2) : Prop :=
  (q.x - p.x) * (r.y - p.y) = (r.x - p.x) * (q.y - p.y)

/-- Four points are cocircular (lie on a common circle). -/
def AreCocircular (p q r s : Point2) : Prop :=
  ∃ cx cy rad : ℝ, rad > 0 ∧
    distSq ⟨cx, cy⟩ p = rad ^ 2 ∧
    distSq ⟨cx, cy⟩ q = rad ^ 2 ∧
    distSq ⟨cx, cy⟩ r = rad ^ 2 ∧
    distSq ⟨cx, cy⟩ s = rad ^ 2

/-- A point set is in general position: no 3 collinear, no 4 cocircular. -/
def InGeneralPosition (A : Set Point2) : Prop :=
  (∀ p q r : Point2, p ∈ A → q ∈ A → r ∈ A →
    p ≠ q → q ≠ r → p ≠ r → ¬AreCollinear p q r) ∧
  (∀ p q r s : Point2, p ∈ A → q ∈ A → r ∈ A → s ∈ A →
    p ≠ q → q ≠ r → r ≠ s → p ≠ r → p ≠ s → q ≠ s →
    ¬AreCocircular p q r s)

/-- Two points are at integer distance. -/
def IsIntegerDist (p q : Point2) : Prop :=
  ∃ n : ℕ, distSq p q = (n : ℝ) ^ 2

/-- The integer distance graph on A: edges connect pairs at integer distance. -/
def IntDistEdge (A : Set Point2) (p q : Point2) : Prop :=
  p ∈ A ∧ q ∈ A ∧ p ≠ q ∧ IsIntegerDist p q

/- ## Chromatic and Clique Numbers -/

/-- A proper coloring of the integer distance graph using k colors. -/
def IsProperColoring (A : Set Point2) (k : ℕ) (c : Point2 → Fin k) : Prop :=
  ∀ p q : Point2, IntDistEdge A p q → c p ≠ c q

/-- The chromatic number of the integer distance graph is at most k. -/
def ChromaticAtMost (A : Set Point2) (k : ℕ) : Prop :=
  ∃ c : Point2 → Fin k, IsProperColoring A k c

/-- A clique of size k in the integer distance graph. -/
def HasClique (A : Set Point2) (k : ℕ) : Prop :=
  ∃ S : Finset Point2, S.card = k ∧
    (∀ p ∈ S, p ∈ A) ∧
    ∀ p q : Point2, p ∈ S → q ∈ S → p ≠ q → IsIntegerDist p q

/- ## Main Questions -/

/-- **Question 1**: Can the chromatic number be infinite?
    That is, does there exist an infinite general-position set A
    such that χ(G(A)) > k for every k? -/
/-- **Question 2**: How large can the clique number be? -/
/- ## Known Results -/

/-- **Anning–Erdős (1945)**: An infinite set with all pairwise
    integer distances must have all points collinear. Therefore
    no infinite clique exists in general position. -/
/-- **Finite clique consequence**: In general position, the clique
    number must be finite (follows from Anning–Erdős). -/
/-- **Erdős–Anning bound**: Any set of n points with no 3 collinear
    and all pairwise distances integers has n bounded by a function
    of the diameter. -/
/- ## Observations -/

/- **Chromatic vs Clique gap**: Even though the clique number is finite,
    the chromatic number could potentially be infinite — there is no
    general relationship forcing χ ≤ f(ω) for geometric distance graphs. -/

/- **Related Problem #213**: Concerns integer distance sets without
    the cocircularity restriction. -/
