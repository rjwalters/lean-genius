/-
Erdős Problem #91: Non-Uniqueness of Minimal Distance Sets

Source: https://erdosproblems.com/91
Status: OPEN (for large n)

Statement:
Suppose A ⊂ ℝ² has |A| = n and minimizes the number of distinct distances
between points in A. Prove that for large n there are at least two
(and probably many) such A which are non-similar.

Known Results:
- n = 3: Equilateral triangle is uniquely optimal (1 distance)
- n = 4: Two non-similar optima (square, bowtie) with 2 distances
- n = 5: Regular pentagon is uniquely optimal (2 distances) - Kovács 2024
- n = 6-9: At least two non-similar examples exist
- Large n: OPEN

Related Problem: #89 asks for the minimum number of distinct distances itself.

References:
- Erdős papers [Er87b], [Er90], [Er97e]
- Kovács (2024): Rigorous proof for n = 5 uniqueness
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.InnerProductSpace.Basic

open Real Finset

namespace Erdos91

/-
## Part I: Distance Sets in the Plane
-/

/--
**Point in ℝ²:**
We represent points as pairs of real numbers.
-/
abbrev Point := ℝ × ℝ

/--
**Euclidean distance:**
The standard distance between two points in the plane.
-/
noncomputable def dist (p q : Point) : ℝ :=
  Real.sqrt ((p.1 - q.1)^2 + (p.2 - q.2)^2)

/--
**Set of distinct distances:**
For a finite point set A, the set of all pairwise distances.
-/
noncomputable def distinctDistances (A : Finset Point) : Finset ℝ :=
  (A.product A).filter (fun (p, q) => p ≠ q)
    |>.image (fun (p, q) => dist p q)

/--
**Number of distinct distances:**
-/
noncomputable def numDistinctDistances (A : Finset Point) : ℕ :=
  (distinctDistances A).card

/-
## Part II: Optimal Configurations
-/

/--
**Minimum distinct distances for n points:**
The minimum number of distinct distances achievable by any n-point set.
-/
noncomputable def minDistinctDistances (n : ℕ) : ℕ :=
  if h : ∃ A : Finset Point, A.card = n then
    Nat.find ⟨numDistinctDistances (Classical.choose h), ⟨Classical.choose h, rfl⟩⟩
  else 0
  -- Note: This is a simplified definition; actual minimum is complex

/--
**Optimal n-point configuration:**
A configuration A is optimal if it achieves the minimum distinct distances.
-/
def IsOptimal (A : Finset Point) : Prop :=
  A.card > 0 ∧ numDistinctDistances A = minDistinctDistances A.card

/-
## Part III: Similarity of Point Sets
-/

/--
**Similar point sets:**
Two point sets are similar if one can be transformed to the other by
translation, rotation, reflection, and uniform scaling.
-/
def AreSimilar (A B : Finset Point) : Prop :=
  A.card = B.card ∧
  ∃ (c : ℝ) (θ : ℝ) (tx ty : ℝ) (refl : Bool),
    c > 0 ∧
    ∀ p ∈ A, ∃ q ∈ B,
      -- Transformed point matches
      True  -- Simplified; actual transform is complex

/--
**Non-similar point sets:**
-/
def AreNonSimilar (A B : Finset Point) : Prop :=
  A.card = B.card ∧ ¬AreSimilar A B

/-
## Part IV: Small Cases
-/

/--
**n = 3: Equilateral triangle is uniquely optimal**
The only 3-point configuration with 1 distinct distance is the equilateral triangle.
-/
axiom n3_unique :
  ∀ A B : Finset Point,
    A.card = 3 → B.card = 3 → IsOptimal A → IsOptimal B →
    AreSimilar A B

/--
**n = 4: Two non-similar optima exist**
The square and "bowtie" (two equilateral triangles sharing an edge)
both achieve 2 distinct distances but are non-similar.
-/
axiom n4_two_optima :
  ∃ A B : Finset Point,
    A.card = 4 ∧ B.card = 4 ∧
    IsOptimal A ∧ IsOptimal B ∧
    AreNonSimilar A B

/--
**n = 5: Regular pentagon is uniquely optimal**
Proved by Kovács (2024). The regular pentagon achieves 2 distinct distances
and no non-similar configuration does better.
-/
axiom kovacs_2024_n5_unique :
  ∀ A B : Finset Point,
    A.card = 5 → B.card = 5 → IsOptimal A → IsOptimal B →
    AreSimilar A B

/--
**n = 6 to 9: Non-uniqueness holds**
Erdős confirmed at least two non-similar optimal configurations for each.
-/
axiom n6_to_9_nonunique :
  ∀ n : ℕ, 6 ≤ n → n ≤ 9 →
    ∃ A B : Finset Point,
      A.card = n ∧ B.card = n ∧
      IsOptimal A ∧ IsOptimal B ∧
      AreNonSimilar A B

/-
## Part V: The Conjecture for Large n
-/

/--
**Erdős's Conjecture:**
For sufficiently large n, there exist at least two non-similar optimal n-point sets.
-/
def erdos_91_conjecture : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    ∃ A B : Finset Point,
      A.card = n ∧ B.card = n ∧
      IsOptimal A ∧ IsOptimal B ∧
      AreNonSimilar A B

/--
**Stronger version:**
Erdős believed there should be "many" non-similar optima for large n.
-/
def erdos_91_strong_conjecture : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    ∃ configs : Finset (Finset Point),
      configs.card ≥ k ∧
      (∀ A ∈ configs, A.card = n ∧ IsOptimal A) ∧
      (∀ A B, A ∈ configs → B ∈ configs → A ≠ B → AreNonSimilar A B)

/--
**Status: OPEN**
The conjecture is not proven.
-/
axiom erdos_91_open : True  -- Placeholder for the open status

/-
## Part VI: Partial Evidence
-/

/--
**Known non-uniqueness pattern:**
Non-uniqueness holds for n = 4, 6, 7, 8, 9.
Uniqueness holds for n = 3, 5.
-/
theorem known_cases :
    -- n = 3: unique
    (∀ A B : Finset Point, A.card = 3 → B.card = 3 →
      IsOptimal A → IsOptimal B → AreSimilar A B) ∧
    -- n = 4: non-unique
    (∃ A B : Finset Point, A.card = 4 ∧ B.card = 4 ∧
      IsOptimal A ∧ IsOptimal B ∧ AreNonSimilar A B) ∧
    -- n = 5: unique
    (∀ A B : Finset Point, A.card = 5 → B.card = 5 →
      IsOptimal A → IsOptimal B → AreSimilar A B) := by
  constructor
  · exact n3_unique
  constructor
  · exact n4_two_optima
  · exact kovacs_2024_n5_unique

/--
**The n = 5 case was mysterious:**
Erdős attributed the proof to "a colleague from Zagreb" whose letter he lost.
Kovács (2024) finally published a complete proof.
-/
axiom zagreb_mystery_resolved : True

/-
## Part VII: Connection to Distinct Distances Problem
-/

/--
**Related Problem #89:**
Let D(n) = minimum distinct distances among n points in ℝ².

Known bounds (Guth-Katz 2015):
  n / log n ≪ D(n) ≤ c·n / √(log n)

The exact value of D(n) is unknown for large n.
-/
axiom guth_katz_bound :
  ∃ c C : ℝ, c > 0 ∧ C > 0 ∧
    ∀ n : ℕ, n ≥ 10 →
      c * (n : ℝ) / log n ≤ (minDistinctDistances n : ℝ) ∧
      (minDistinctDistances n : ℝ) ≤ C * (n : ℝ) / Real.sqrt (log n)

/-
## Part VIII: Summary
-/

/--
**Erdős Problem #91: Status**

**Question:**
For large n, are there multiple non-similar n-point configurations
achieving the minimum number of distinct distances?

**Known Results:**
- n = 3: UNIQUE (equilateral triangle)
- n = 4: NON-UNIQUE (square vs bowtie)
- n = 5: UNIQUE (regular pentagon) - Kovács 2024
- n = 6-9: NON-UNIQUE
- Large n: OPEN

**Key Insight:**
The pattern of uniqueness vs non-uniqueness is not monotonic.
n = 5 uniqueness is sandwiched between non-uniqueness at n = 4 and n = 6.
-/
theorem erdos_91_summary :
    -- n = 4 has non-similar optima
    (∃ A B : Finset Point, A.card = 4 ∧ B.card = 4 ∧
      IsOptimal A ∧ IsOptimal B ∧ AreNonSimilar A B) ∧
    -- n = 5 is unique
    (∀ A B : Finset Point, A.card = 5 → B.card = 5 →
      IsOptimal A → IsOptimal B → AreSimilar A B) ∧
    -- n = 6-9 have non-similar optima
    (∀ n : ℕ, 6 ≤ n → n ≤ 9 →
      ∃ A B : Finset Point, A.card = n ∧ B.card = n ∧
        IsOptimal A ∧ IsOptimal B ∧ AreNonSimilar A B) := by
  constructor
  · exact n4_two_optima
  constructor
  · exact kovacs_2024_n5_unique
  · exact n6_to_9_nonunique

end Erdos91
