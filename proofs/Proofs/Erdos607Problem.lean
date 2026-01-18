/-
  Erdős Problem #607: Incidence Signatures of Point Configurations

  Source: https://erdosproblems.com/607
  Status: SOLVED (Szemerédi-Trotter)
  Prize: $250

  Statement:
  For a set of n points P ⊂ ℝ², let ℓ₁,...,ℓₘ be the lines determined by P,
  and let A = {|ℓ₁ ∩ P|, ..., |ℓₘ ∩ P|} be the multiset of incidence counts.

  Let F(n) count the number of possible sets A that can be constructed.

  Question: Is F(n) ≤ exp(O(√n))?

  Erdős noted it is "easy to see" this bound would be optimal.

  Solution: Szemerédi and Trotter proved F(n) ≤ exp(O(√n)).

  The key insight is that while there are many point configurations,
  the possible incidence signatures are highly constrained by
  combinatorial geometry.

  Related: Szemerédi-Trotter theorem, #606 (achievable line counts)
-/

import Mathlib

open Finset Function Set

/-! ## Point Configurations in the Plane -/

/-- A point in ℝ² -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- A point configuration is a finite set of distinct points -/
structure PointConfig (n : ℕ) where
  points : Fin n → Point
  distinct : Function.Injective points

/-- A line in ℝ² determined by two distinct points -/
structure Line where
  point1 : Point
  point2 : Point
  ne : point1 ≠ point2

/-- A point lies on a line iff it's collinear with the defining points -/
def Line.contains (l : Line) (p : Point) : Prop :=
  ∃ t : ℝ, p = l.point1 + t • (l.point2 - l.point1)

/-! ## Lines Determined by a Configuration -/

/-- Two points determine a line (if distinct) -/
def lineThroughPair (p q : Point) (h : p ≠ q) : Line :=
  ⟨p, q, h⟩

/-- The set of lines determined by a point configuration -/
noncomputable def determinedLines {n : ℕ} (config : PointConfig n) : Set Line :=
  {l : Line | ∃ i j : Fin n, i ≠ j ∧
    l = lineThroughPair (config.points i) (config.points j)
      (fun h => (Fin.ext_iff.mp (config.distinct h)) ▸ (i.ne_of_gt (lt_of_le_of_ne (Nat.zero_le _) (fun _ => by simp_all))).elim)}

/-! ## Incidence Counts -/

/-- Count of points on a line -/
noncomputable def incidenceCount {n : ℕ} (config : PointConfig n) (l : Line) : ℕ :=
  (Finset.univ.filter fun i => l.contains (config.points i)).card

/-- The incidence signature: multiset of point counts per line -/
noncomputable def incidenceSignature {n : ℕ} (config : PointConfig n) : Multiset ℕ :=
  sorry -- The multiset of incidenceCount for each determined line

/-- The set form of incidence signature (ignoring multiplicities) -/
noncomputable def incidenceSet {n : ℕ} (config : PointConfig n) : Finset ℕ :=
  sorry -- {|ℓ ∩ P| : ℓ is a determined line}

/-! ## The Function F(n) -/

/-- F(n) counts distinct incidence signatures achievable by n points -/
noncomputable def F (n : ℕ) : ℕ :=
  sorry -- Cardinality of {incidenceSignature config : config is an n-point configuration}

/-- Alternative: count distinct incidence sets (as in original problem) -/
noncomputable def F_set (n : ℕ) : ℕ :=
  sorry -- Cardinality of {incidenceSet config : config is an n-point configuration}

/-! ## The Conjecture and Solution -/

/-- The Erdős conjecture: F(n) ≤ exp(O(√n)) -/
def ErdosConjecture607 : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, (F n : ℝ) ≤ Real.exp (C * Real.sqrt n)

/-- Szemerédi-Trotter proved the conjecture -/
theorem szemeredi_trotter_607 : ErdosConjecture607 := by
  sorry

/-! ## Upper Bound Analysis -/

/-- Key constraint: every line contains at least 2 points -/
theorem incidence_at_least_two {n : ℕ} (config : PointConfig n) (l : Line)
    (hl : l ∈ determinedLines config) : incidenceCount config l ≥ 2 := by
  sorry

/-- Key constraint: at most n points total -/
theorem incidence_at_most_n {n : ℕ} (config : PointConfig n) (l : Line) :
    incidenceCount config l ≤ n := by
  sorry

/-- The number of lines is at most C(n,2) -/
theorem lines_at_most_binomial {n : ℕ} (config : PointConfig n) :
    sorry -- |determinedLines config| ≤ n.choose 2
    := by sorry

/-! ## Lower Bound: Optimality -/

/-- Erdős claimed exp(c√n) is also a lower bound -/
def LowerBoundConjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ n in Filter.atTop,
    (F n : ℝ) ≥ Real.exp (c * Real.sqrt n)

/-- The lower bound is achieved by carefully constructed configurations -/
theorem lower_bound_construction : LowerBoundConjecture := by
  sorry

/-! ## Special Configurations -/

/-- All points collinear: A = {n} (single line with all points) -/
def collinearConfig (n : ℕ) (hn : n ≥ 2) : PointConfig n :=
  ⟨fun i => ![i.val, 0], fun _ _ h => by simp_all⟩

theorem collinear_signature (n : ℕ) (hn : n ≥ 2) :
    incidenceSet (collinearConfig n hn) = {n} := by
  sorry

/-- General position: A = {2} (every line has exactly 2 points) -/
noncomputable def generalPositionConfig (n : ℕ) : PointConfig n :=
  sorry -- Points on a circle, no 3 collinear

theorem general_position_signature (n : ℕ) (hn : n ≥ 3) :
    incidenceSet (generalPositionConfig n) = {2} := by
  sorry

/-- Grid configuration: multiple incidence values -/
noncomputable def gridConfig (m : ℕ) : PointConfig (m * m) :=
  sorry -- m × m grid of points

theorem grid_signature (m : ℕ) (hm : m ≥ 2) :
    2 ∈ incidenceSet (gridConfig m) ∧ m ∈ incidenceSet (gridConfig m) := by
  sorry

/-! ## Connection to Szemerédi-Trotter Incidence Theorem -/

/-- The Szemerédi-Trotter incidence bound (background theorem) -/
axiom szemeredi_trotter_incidence :
  ∃ C : ℝ, C > 0 ∧ ∀ (n m : ℕ) (points : Fin n → Point) (lines : Fin m → Line),
    let incidences := (Finset.univ ×ˢ Finset.univ).filter
      fun (i, j) => (lines j).contains (points i)
    (incidences.card : ℝ) ≤ C * ((n : ℝ) * m) ^ (2/3 : ℝ) + n + m

/-- The incidence bound constrains possible signatures -/
theorem incidence_bound_constrains_signature {n : ℕ} (config : PointConfig n) :
    sorry -- The signature is constrained by ST bound
    := by sorry

/-! ## Counting Partitions -/

/-- A key insight: incidence signatures correspond to integer partitions -/
-- If lines have incidences k₁, k₂, ..., kₘ, then Σkᵢ(kᵢ-1)/2 = C(n,2)

/-- Sum of incidences constraint -/
theorem incidence_sum_constraint {n : ℕ} (config : PointConfig n) :
    sorry -- Related to counting pairs
    := by sorry

/-- The number of valid partitions grows as exp(√n) -/
theorem partition_count_growth :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧ ∀ᶠ n in Filter.atTop,
      Real.exp (c * Real.sqrt n) ≤ F n ∧
      (F n : ℝ) ≤ Real.exp (C * Real.sqrt n) := by
  sorry

/-! ## Main Results -/

/-- Erdős Problem #607: SOLVED

    F(n) = exp(Θ(√n))

    - Upper bound: Szemerédi-Trotter
    - Lower bound: Constructions achieving exp(c√n) distinct signatures
    - The √n growth comes from partition-theoretic considerations -/
theorem erdos_607 : ErdosConjecture607 ∧ LowerBoundConjecture := by
  exact ⟨szemeredi_trotter_607, lower_bound_construction⟩

/-- The tight asymptotic -/
theorem erdos_607_tight :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧ ∀ᶠ n in Filter.atTop,
      Real.exp (c * Real.sqrt n) ≤ F n ∧
      (F n : ℝ) ≤ Real.exp (C * Real.sqrt n) :=
  partition_count_growth

#check erdos_607
#check szemeredi_trotter_607
#check ErdosConjecture607
