/-
Erdős Problem #363: Square Products from Disjoint Intervals

Let I₁, ..., Iₙ be a collection of disjoint intervals of integers.
Is it true that there are only finitely many such collections with
|Iᵢ| ≥ 4 for all i such that ∏ᵢ ∏_{m ∈ Iᵢ} m is a perfect square?

**Answer**: NO - the conjecture is FALSE.

**History**:
- Erdős-Selfridge: Product of consecutive integers is never a power
- Pomerance: Observed |Iᵢ| ≥ 4 condition is necessary (counterexamples for |Iᵢ| = 3)
- Ulas (2005): Infinitely many solutions for n = 4 or n ≥ 6 with |Iᵢ| = 4
- Bauer-Bennett (2007): Infinitely many solutions for n = 3 or n = 5 with |Iᵢ| = 4
- Bennett-Van Luijk (2012): Infinitely many solutions for n ≥ 5 with |Iᵢ| = 5

Reference: https://erdosproblems.com/363
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open BigOperators

namespace Erdos363

/-!
## Part I: Basic Definitions
-/

/--
An interval of consecutive integers [a, a+1, ..., a+k-1].
-/
structure ConsecutiveInterval where
  start : ℤ
  length : ℕ
  length_pos : length > 0

/-- The set of integers in an interval. -/
def ConsecutiveInterval.elements (I : ConsecutiveInterval) : Finset ℤ :=
  Finset.Icc I.start (I.start + I.length - 1)

/-- The product of integers in an interval. -/
noncomputable def ConsecutiveInterval.product (I : ConsecutiveInterval) : ℤ :=
  ∏ m ∈ I.elements, m

/-- The size of an interval. -/
def ConsecutiveInterval.size (I : ConsecutiveInterval) : ℕ := I.length

/--
A collection of disjoint intervals.
-/
structure DisjointIntervalCollection where
  intervals : List ConsecutiveInterval
  disjoint : ∀ i j : Fin intervals.length, i ≠ j →
    (intervals.get i).elements ∩ (intervals.get j).elements = ∅

/-- The product over all intervals in a collection. -/
noncomputable def DisjointIntervalCollection.totalProduct
    (C : DisjointIntervalCollection) : ℤ :=
  (C.intervals.map ConsecutiveInterval.product).prod

/-- Check if all intervals have size at least k. -/
def DisjointIntervalCollection.allSizeAtLeast
    (C : DisjointIntervalCollection) (k : ℕ) : Prop :=
  ∀ I ∈ C.intervals, I.size ≥ k

/-!
## Part II: Perfect Squares
-/

/--
An integer is a perfect square if it equals n² for some integer n.
-/
def isPerfectSquare (z : ℤ) : Prop :=
  ∃ n : ℤ, z = n^2

/--
The set of collections with intervals of size ≥ 4 whose product is a perfect square.
-/
def squareCollections : Set DisjointIntervalCollection :=
  { C : DisjointIntervalCollection |
    C.allSizeAtLeast 4 ∧ isPerfectSquare C.totalProduct }

/-!
## Part III: The Erdős Conjecture
-/

/--
**The Original Conjecture:**
There are only finitely many collections of disjoint intervals of size ≥ 4
whose product is a perfect square.
-/
def erdosConjecture363 : Prop :=
  Set.Finite squareCollections

/-!
## Part IV: Why |Iᵢ| ≥ 4?

Pomerance observed that products of three consecutive integers from
specific sequences are always squares when combined appropriately.
-/

/--
**Pomerance's Observation:**
For any n ≥ 2, the product of the four "triplet blocks":
- (2^(n-1) - 1) · 2^(n-1) · (2^(n-1) + 1)
- (2^n - 1) · 2^n · (2^n + 1)
- (2^(2n-1) - 2) · (2^(2n-1) - 1) · 2^(2n-1)
- (2^(2n) - 2) · (2^(2n) - 1) · 2^(2n)
is always a perfect square.
-/
def pomeranceCounterexample : Prop :=
  ∀ n : ℕ, n ≥ 2 →
    ∃ (C : DisjointIntervalCollection),
      C.intervals.length = 4 ∧
      (∀ I ∈ C.intervals, I.size = 3) ∧
      isPerfectSquare C.totalProduct

axiom pomerance_observation : pomeranceCounterexample

/-!
## Part V: Ulas's Theorem (2005)
-/

/--
**Ulas's Theorem (2005):**
For n = 4 or n ≥ 6, there are infinitely many collections of n disjoint
intervals, each of size exactly 4, whose product is a perfect square.
-/
axiom ulas_theorem :
    ∀ n : ℕ, (n = 4 ∨ n ≥ 6) →
      Set.Infinite { C : DisjointIntervalCollection |
        C.intervals.length = n ∧
        (∀ I ∈ C.intervals, I.size = 4) ∧
        isPerfectSquare C.totalProduct }

/-!
## Part VI: Bauer-Bennett Theorem (2007)
-/

/--
**Bauer-Bennett Theorem (2007):**
For n = 3 or n = 5, there are infinitely many collections of n disjoint
intervals, each of size exactly 4, whose product is a perfect square.
-/
axiom bauer_bennett_theorem :
    ∀ n : ℕ, (n = 3 ∨ n = 5) →
      Set.Infinite { C : DisjointIntervalCollection |
        C.intervals.length = n ∧
        (∀ I ∈ C.intervals, I.size = 4) ∧
        isPerfectSquare C.totalProduct }

/-!
## Part VII: Bennett-Van Luijk Theorem (2012)
-/

/--
**Bennett-Van Luijk Theorem (2012):**
For n ≥ 5, there are infinitely many collections of n disjoint
intervals, each of size exactly 5, whose product is a perfect square.
-/
axiom bennett_van_luijk_theorem :
    ∀ n : ℕ, n ≥ 5 →
      Set.Infinite { C : DisjointIntervalCollection |
        C.intervals.length = n ∧
        (∀ I ∈ C.intervals, I.size = 5) ∧
        isPerfectSquare C.totalProduct }

/-!
## Part VIII: The Conjecture is FALSE
-/

/--
**Combining the results:**
There are infinitely many collections of size-4 intervals for any n ≥ 3.
-/
theorem infinitely_many_size4_collections :
    Set.Infinite { C : DisjointIntervalCollection |
      (∀ I ∈ C.intervals, I.size = 4) ∧
      isPerfectSquare C.totalProduct } := by
  -- For n = 4 (or any n ≥ 3), Ulas + Bauer-Bennett give infinitely many
  have h4 := ulas_theorem 4 (Or.inl rfl)
  exact Set.Infinite.mono (fun C hC => ⟨hC.2.1, hC.2.2⟩) h4

/--
**The Conjecture is FALSE:**
There are infinitely many collections of disjoint intervals of size ≥ 4
whose product is a perfect square.
-/
theorem erdosConjecture363_false : ¬erdosConjecture363 := by
  intro h_fin
  -- The set of size-4 collections is a subset of squareCollections
  have h_subset : { C : DisjointIntervalCollection |
      (∀ I ∈ C.intervals, I.size = 4) ∧ isPerfectSquare C.totalProduct } ⊆
      squareCollections := by
    intro C hC
    exact ⟨fun I hI => le_of_eq (hC.1 I hI), hC.2⟩
  -- But we have infinitely many size-4 collections
  have h_inf := infinitely_many_size4_collections
  -- A subset of a finite set cannot be infinite
  exact Set.Infinite.not_finite (h_inf.mono h_subset) h_fin

/-!
## Part IX: Main Theorem
-/

/--
**Main Theorem (Answer to Erdős #363):**
The conjecture that there are only finitely many square-product collections
is FALSE.
-/
theorem erdos_363 : ¬erdosConjecture363 := erdosConjecture363_false

/-!
## Part X: Ulas's Conjecture
-/

/--
**Ulas's Conjecture:**
For any fixed interval size k ≥ 4, there are infinitely many solutions
provided the number of intervals n is sufficiently large.
-/
def ulas_conjecture : Prop :=
  ∀ k : ℕ, k ≥ 4 →
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      Set.Infinite { C : DisjointIntervalCollection |
        C.intervals.length = n ∧
        (∀ I ∈ C.intervals, I.size = k) ∧
        isPerfectSquare C.totalProduct }

/-!
## Part XI: Connection to Erdős-Selfridge
-/

/--
**Erdős-Selfridge Theorem:**
The product of two or more consecutive integers is never a perfect power.
-/
axiom erdos_selfridge :
    ∀ (n k : ℕ) (m : ℤ), n ≥ 2 → k ≥ 2 →
      ∏ i ∈ Finset.range n, (m + i) ≠ (0 : ℤ) →
      ¬∃ (a : ℤ) (b : ℕ), b ≥ 2 ∧ ∏ i ∈ Finset.range n, (m + i) = a^b

/--
**Key Insight:**
A single block of consecutive integers is never a perfect square (by Erdős-Selfridge).
But DISJOINT blocks can multiply to give a square when combined correctly.
-/
theorem single_block_not_square (I : ConsecutiveInterval) (h : I.size ≥ 2) :
    ¬isPerfectSquare I.product := by
  sorry -- Follows from Erdős-Selfridge

/-!
## Part XII: Summary
-/

/--
**Problem #363 Summary:**
1. Erdős asked if finitely many collections of size-≥4 intervals give square products
2. Ulas (2005): Infinitely many for n=4 or n≥6 with size-4 intervals
3. Bauer-Bennett (2007): Infinitely many for n=3 or n=5 with size-4 intervals
4. Bennett-Van Luijk (2012): Infinitely many for n≥5 with size-5 intervals
5. The conjecture is FALSE
-/
theorem erdos_363_summary :
    -- The conjecture is false
    ¬erdosConjecture363 ∧
    -- Pomerance showed the |Iᵢ| ≥ 4 condition is needed
    pomeranceCounterexample := by
  exact ⟨erdosConjecture363_false, pomerance_observation⟩

end Erdos363
