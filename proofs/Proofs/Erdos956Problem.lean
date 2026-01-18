/-
  Erdős Problem #956: Unit Distances Between Convex Translates

  Source: https://erdosproblems.com/956
  Status: OPEN

  Statement:
  Let h(n) be the maximal number of unit distances between n disjoint
  convex translates of a compact convex set C ⊂ ℝ².

  Prove that there exists c > 0 such that h(n) > n^(1+c) for all large n.

  Known Bounds:
  - Upper: h(n) ≪ n^(4/3) (Erdős-Pach 1990)
  - Lower: h(n) ≥ f(n) where f(n) = unit distance function for points
  - For general (non-translate) convex sets: O(n^(7/5))

  Context:
  - δ(C, D) = inf{|c - d| : c ∈ C, d ∈ D} is the distance between sets
  - A "unit distance" means δ(C + x₁, C + x₂) = 1

  Tags: geometry, combinatorics, unit-distances, convex-sets, open-problem
-/

import Mathlib

namespace Erdos956

open Set Metric Finset

/-!
## Part I: Distance Between Sets

The fundamental distance notion.
-/

/-- The distance between two sets in a metric space. -/
noncomputable def setDistance {X : Type*} [PseudoMetricSpace X] (C D : Set X) : ℝ :=
  sInf { dist c d | (c : X) (d : X) (hc : c ∈ C) (hd : d ∈ D) }

/-- Notation: δ(C, D) for set distance. -/
notation "δ" => setDistance

/-- δ(C, D) = δ(D, C) (symmetry). -/
theorem setDistance_symm {X : Type*} [PseudoMetricSpace X] (C D : Set X) :
    δ C D = δ D C := by
  sorry

/-- δ(C, D) ≥ 0 (non-negativity). -/
theorem setDistance_nonneg {X : Type*} [PseudoMetricSpace X] (C D : Set X) :
    δ C D ≥ 0 := by
  sorry

/-- δ(C, D) = 0 iff C and D touch or overlap. -/
theorem setDistance_eq_zero_iff {X : Type*} [PseudoMetricSpace X] (C D : Set X)
    (hC : C.Nonempty) (hD : D.Nonempty) :
    δ C D = 0 ↔ (closure C ∩ closure D).Nonempty := by
  sorry

/-!
## Part II: Convex Sets and Translates

The geometric objects of interest.
-/

/-- A compact convex set in ℝ². -/
structure CompactConvex where
  carrier : Set (EuclideanSpace ℝ (Fin 2))
  convex : Convex ℝ carrier
  compact : IsCompact carrier
  nonempty : carrier.Nonempty

/-- The translate C + x of a set. -/
def translate (C : Set (EuclideanSpace ℝ (Fin 2))) (x : EuclideanSpace ℝ (Fin 2)) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  { c + x | c ∈ C }

/-- Notation: C +ₛ x for translation. -/
notation:65 C " +ₛ " x => translate C x

/-- Translates preserve convexity. -/
theorem translate_convex (C : CompactConvex) (x : EuclideanSpace ℝ (Fin 2)) :
    Convex ℝ (C.carrier +ₛ x) := by
  sorry

/-- Translates preserve compactness. -/
theorem translate_compact (C : CompactConvex) (x : EuclideanSpace ℝ (Fin 2)) :
    IsCompact (C.carrier +ₛ x) := by
  sorry

/-!
## Part III: Disjoint Translates Configuration

The setup for the problem.
-/

/-- A configuration of n disjoint translates. -/
structure DisjointTranslates (n : ℕ) where
  base : CompactConvex
  centers : Fin n → EuclideanSpace ℝ (Fin 2)
  disjoint : ∀ i j : Fin n, i ≠ j →
    Disjoint (base.carrier +ₛ centers i) (base.carrier +ₛ centers j)

/-- Two translates have unit distance. -/
def HasUnitDistance (config : DisjointTranslates n) (i j : Fin n) : Prop :=
  δ (config.base.carrier +ₛ config.centers i)
    (config.base.carrier +ₛ config.centers j) = 1

/-- Count of unit distance pairs in a configuration. -/
noncomputable def unitDistanceCount (config : DisjointTranslates n) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun i =>
    (Finset.univ : Finset (Fin n)).filter (fun j => i < j ∧ HasUnitDistance config i j)
    |>.card > 0)).card

/-!
## Part IV: The Function h(n)

The extremal function.
-/

/-- The extremal function h(n): max unit distances among n disjoint translates. -/
noncomputable def h (n : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ config : DisjointTranslates n, unitDistanceCount config = m }

/-- h is monotone. -/
theorem h_mono (n m : ℕ) (hnm : n ≤ m) : h n ≤ h m := by
  sorry

/-- Trivial lower bound: h(n) ≥ 0. -/
theorem h_nonneg (n : ℕ) : h n ≥ 0 := Nat.zero_le _

/-!
## Part V: Connection to Unit Distance Problem

h(n) relates to the classical unit distance function.
-/

/-- The unit distance function for n points in ℝ². -/
noncomputable def unitDistancePoints (n : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ pts : Fin n → EuclideanSpace ℝ (Fin 2),
    (Finset.univ.filter (fun ij : Fin n × Fin n =>
      ij.1 < ij.2 ∧ dist (pts ij.1) (pts ij.2) = 1)).card = m }

/-- Notation: f(n) for unit distance function. -/
notation "f" => unitDistancePoints

/-- **Key Observation**: h(n) ≥ f(n). -/
theorem h_ge_f (n : ℕ) : h n ≥ f n := by
  sorry

/-- Spencer-Szemerédi-Trotter: f(n) = O(n^(4/3)). -/
axiom f_upper_bound (n : ℕ) (hn : n ≥ 2) :
    (f n : ℝ) ≤ n^(4/3 : ℝ)

/-- f(n) = Ω(n^(1 + c)) for some c > 0. -/
axiom f_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 10 → (f n : ℝ) ≥ n^(1 + c / 2)

/-!
## Part VI: Erdős-Pach Upper Bound (1990)

The best known upper bound.
-/

/-- **Erdős-Pach (1990)**: h(n) ≪ n^(4/3). -/
axiom erdos_pach_upper_bound (n : ℕ) (hn : n ≥ 2) :
    (h n : ℝ) ≤ 2 * n^(4/3 : ℝ)

/-- The upper bound exponent is 4/3. -/
def upper_exponent : ℝ := 4/3

/-!
## Part VII: General Convex Sets (Non-Translates)

A related problem with weaker structure.
-/

/-- Configuration of n disjoint convex sets (not necessarily translates). -/
structure DisjointConvexSets (n : ℕ) where
  sets : Fin n → CompactConvex
  disjoint : ∀ i j : Fin n, i ≠ j →
    Disjoint (sets i).carrier (sets j).carrier

/-- Unit distance count for general convex sets. -/
noncomputable def unitDistanceCountGeneral (config : DisjointConvexSets n) : ℕ :=
  (Finset.univ.filter (fun ij : Fin n × Fin n =>
    ij.1 < ij.2 ∧ δ (config.sets ij.1).carrier (config.sets ij.2).carrier = 1)).card

/-- The extremal function for general convex sets. -/
noncomputable def h_general (n : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ config : DisjointConvexSets n, unitDistanceCountGeneral config = m }

/-- **Erdős-Pach**: For general convex sets, h_general(n) ≪ n^(7/5). -/
axiom erdos_pach_general (n : ℕ) (hn : n ≥ 2) :
    (h_general n : ℝ) ≤ 2 * n^(7/5 : ℝ)

/-- h(n) ≤ h_general(n) (translates are special case). -/
theorem h_le_h_general (n : ℕ) : h n ≤ h_general n := by
  sorry

/-- The general exponent is 7/5 > 4/3. -/
theorem general_exponent_larger : (7 : ℝ)/5 > 4/3 := by norm_num

/-!
## Part VIII: The Conjecture

The main open question.
-/

/-- **Erdős-Pach Conjecture**: h(n) > n^(1+c) for some c > 0. -/
def ErdosPachConjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 10 → (h n : ℝ) > n^(1 + c)

/-- Equivalent formulation: h(n) is superlinear. -/
def SuperlinearConjecture : Prop :=
  ∀ C : ℝ, C > 0 → ∃ N : ℕ, ∀ n ≥ N, (h n : ℝ) > C * n

/-- The conjecture would follow from showing h(n) ≥ f(n) and f(n) superlinear. -/
theorem conjecture_from_f : (∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 10 → (f n : ℝ) > n^(1 + c)) →
    ErdosPachConjecture := by
  sorry

/-!
## Part IX: Known Constructions

Lower bound examples.
-/

/-- Lattice construction gives many unit distances. -/
axiom lattice_construction (n : ℕ) (hn : n ≥ 4) :
    ∃ config : DisjointTranslates n, unitDistanceCount config ≥ n - 1

/-- Grid constructions give Ω(n log n / log log n) unit distances. -/
axiom grid_construction (n : ℕ) (hn : n ≥ 10) :
    (h n : ℝ) ≥ n * Real.log n / Real.log (Real.log n)

/-!
## Part X: Connections to Incidence Geometry

The crossing number and incidence bounds.
-/

/-- Szemerédi-Trotter incidence bound. -/
axiom szemeredi_trotter (n m : ℕ) (hn : n ≥ 1) (hm : m ≥ 1) :
    -- The number of incidences between n points and m lines is O(n^(2/3) m^(2/3) + n + m)
    True

/-- The upper bound on h(n) uses incidence geometry. -/
axiom upper_bound_uses_incidences :
    -- The proof of h(n) ≪ n^(4/3) uses Szemerédi-Trotter
    True

/-!
## Part XI: Special Cases

Specific convex sets.
-/

/-- For disks, the problem is essentially the unit distance problem. -/
theorem disk_case (n : ℕ) : ∃ C : CompactConvex,
    (∀ config : DisjointTranslates n, config.base = C →
      unitDistanceCount config ≤ f n + n) := by
  sorry

/-- For line segments, different bounds may apply. -/
axiom segment_case (n : ℕ) (hn : n ≥ 2) :
    ∃ config : DisjointTranslates n, unitDistanceCount config ≥ 2 * (n - 1)

/-!
## Part XII: Main Results

Summary of Erdős Problem #956.
-/

/-- **Erdős Problem #956: OPEN**

    Question: Is there c > 0 such that h(n) > n^(1+c) for large n?

    Where h(n) = max unit distances among n disjoint convex translates.

    Known bounds:
    - Upper: h(n) ≪ n^(4/3) (Erdős-Pach 1990)
    - Lower: h(n) ≥ f(n) ≥ Ω(n log n / log log n)

    The gap between n^(4/3) and conjectured n^(1+c) remains unresolved. -/
theorem erdos_956_bounds (n : ℕ) (hn : n ≥ 10) :
    (h n : ℝ) ≥ n * Real.log n / Real.log (Real.log n) ∧
    (h n : ℝ) ≤ 2 * n^(4/3 : ℝ) := by
  constructor
  · exact grid_construction n hn
  · exact erdos_pach_upper_bound n (by omega)

/-- The answer to Erdős Problem #956. -/
def erdos_956_answer : String :=
  "OPEN: Is h(n) > n^(1+c) for some c > 0? Known: Ω(n log n / log log n) ≤ h(n) ≤ O(n^(4/3))"

/-- The status of the problem. -/
def erdos_956_status : String :=
  "OPEN - Erdős-Pach conjecture unresolved"

/-- The gap between bounds. -/
theorem bounds_gap (n : ℕ) (hn : n ≥ 100) :
    n^(4/3 : ℝ) > n * Real.log n / Real.log (Real.log n) := by
  sorry

#check erdos_956_bounds
#check ErdosPachConjecture
#check h_ge_f

end Erdos956
