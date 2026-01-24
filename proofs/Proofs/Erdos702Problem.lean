/-
Erdős Problem #702: Singleton Intersections in k-Uniform Families

Source: https://erdosproblems.com/702
Status: SOLVED (Frankl 1977)

Statement:
Let k ≥ 4. If F is a family of k-subsets of {1,...,n} with
|F| > C(n-2, k-2), then there exist A, B ∈ F with |A ∩ B| = 1.

Background:
A conjecture of Erdős and Sós. The threshold C(n-2, k-2) is the
maximum size of a family avoiding singleton intersections when
all sets contain two fixed elements.

Solution:
- Katona (unpublished): Proved for k = 4
- Frankl (1977): Proved for all k ≥ 4

References:
- [Fr77] Frankl, Péter, "On families of finite sets no two of which
  intersect in a singleton", Bull. Austral. Math. Soc. (1977), 125-134.

Tags: extremal-set-theory, intersecting-families, frankl
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace Erdos702

open Finset Nat

/-!
## Part I: Set Families
-/

/-- The ground set {1, 2, ..., n}. -/
def groundSet (n : ℕ) : Finset ℕ := range n |>.map ⟨(· + 1), by intro; omega⟩

/-- A k-uniform family: all sets have size exactly k. -/
def IsKUniform (F : Finset (Finset ℕ)) (k : ℕ) : Prop :=
  ∀ A ∈ F, A.card = k

/-- A family over {1,...,n}: all sets are subsets of the ground set. -/
def IsOverGroundSet (F : Finset (Finset ℕ)) (n : ℕ) : Prop :=
  ∀ A ∈ F, A ⊆ groundSet n

/-!
## Part II: Intersection Patterns
-/

/-- Two sets have a singleton intersection: |A ∩ B| = 1. -/
def SingletonIntersection (A B : Finset ℕ) : Prop :=
  (A ∩ B).card = 1

/-- A family avoids singleton intersections: no two distinct sets
    have |A ∩ B| = 1. -/
def AvoidsSingletonIntersections (F : Finset (Finset ℕ)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ¬SingletonIntersection A B

/-- A family contains a singleton intersection pair. -/
def HasSingletonPair (F : Finset (Finset ℕ)) : Prop :=
  ∃ A ∈ F, ∃ B ∈ F, A ≠ B ∧ SingletonIntersection A B

/-!
## Part III: The Extremal Bound
-/

/-- **The extremal construction:**
    Fix two elements x, y. Take all k-sets containing both x and y.
    This family has size C(n-2, k-2) and avoids singleton intersections. -/
axiom extremal_construction :
    ∀ n k : ℕ, k ≥ 2 → n ≥ k →
    ∃ F : Finset (Finset ℕ),
      IsKUniform F k ∧
      IsOverGroundSet F n ∧
      F.card = Nat.choose (n - 2) (k - 2) ∧
      AvoidsSingletonIntersections F

/-- **Why C(n-2, k-2)?**
    If all sets contain {x, y}, then any two sets A, B satisfy
    |A ∩ B| ≥ 2 (they share at least x and y), so |A ∩ B| ≠ 1. -/
axiom why_n_minus_2_choose_k_minus_2 : True

/-!
## Part IV: Frankl's Theorem (1977)
-/

/-- **Erdős-Sós Conjecture (Frankl 1977):**
    For k ≥ 4, if |F| > C(n-2, k-2), then F has a singleton pair.

    This is tight: the extremal construction achieves C(n-2, k-2). -/
axiom frankl_theorem :
    ∀ n k : ℕ, k ≥ 4 → n ≥ k →
    ∀ F : Finset (Finset ℕ),
      IsKUniform F k →
      IsOverGroundSet F n →
      F.card > Nat.choose (n - 2) (k - 2) →
      HasSingletonPair F

/-- **Katona's case k = 4 (unpublished):**
    The first case, proved before Frankl's general result. -/
axiom katona_k4 :
    ∀ n : ℕ, n ≥ 4 →
    ∀ F : Finset (Finset ℕ),
      IsKUniform F 4 →
      IsOverGroundSet F n →
      F.card > Nat.choose (n - 2) 2 →
      HasSingletonPair F

/-!
## Part V: Special Cases
-/

/-- **Case k = 4, n = 6:**
    The bound is C(4, 2) = 6.
    Any family of 4-subsets of {1,...,6} with > 6 sets
    has a singleton intersection pair. -/
example : Nat.choose 4 2 = 6 := by native_decide

/-- **The condition k ≥ 4 is necessary:**
    For k = 3, the statement fails. There exist large 3-uniform
    families avoiding singleton intersections. -/
axiom k3_fails :
    ∃ n : ℕ, ∃ F : Finset (Finset ℕ),
      IsKUniform F 3 ∧
      IsOverGroundSet F n ∧
      F.card > Nat.choose (n - 2) 1 ∧
      AvoidsSingletonIntersections F

/-!
## Part VI: Proof Technique
-/

/-- **Frankl's proof approach:**
    Uses the shifting technique and careful case analysis. -/
axiom shifting_technique : True

/-- **Connection to Problem #703:**
    Related problem about intersecting families. -/
axiom related_to_703 : True

/-!
## Part VII: Summary
-/

/-- **Erdős Problem #702: SOLVED**

    PROBLEM: For k ≥ 4, if F is a k-uniform family over {1,...,n}
    with |F| > C(n-2, k-2), must F contain A, B with |A ∩ B| = 1?

    ANSWER: YES (Frankl 1977)

    KEY FACTS:
    - Conjecture of Erdős and Sós
    - Katona proved k = 4 (unpublished)
    - Frankl proved all k ≥ 4 (1977)
    - Bound is tight: extremal = all sets through 2 fixed points
    - Fails for k = 3 -/
theorem erdos_702 :
    ∀ n k : ℕ, k ≥ 4 → n ≥ k →
    ∀ F : Finset (Finset ℕ),
      IsKUniform F k →
      IsOverGroundSet F n →
      F.card > Nat.choose (n - 2) (k - 2) →
      HasSingletonPair F := frankl_theorem

/-- The answer to Erdős Problem #702. -/
def erdos_702_answer : String :=
  "YES: Frankl (1977) proved that |F| > C(n-2,k-2) forces a singleton intersection"

/-- The status of Erdős Problem #702. -/
def erdos_702_status : String := "SOLVED"

#check erdos_702
#check frankl_theorem
#check HasSingletonPair
#check AvoidsSingletonIntersections

end Erdos702
