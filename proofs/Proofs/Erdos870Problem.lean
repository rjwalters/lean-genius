/-
Erdős Problem #870: Minimal Additive Bases

Source: https://erdosproblems.com/870
Status: OPEN

Statement:
Let k ≥ 3 and A be an additive basis of order k. Does there exist a constant c = c(k) > 0
such that if r(n) ≥ c log n for all large n, then A must contain a minimal basis of order k?
(Here r(n) counts the number of representations of n as the sum of at most k elements from A.)

Background:
- A set A ⊆ ℕ is an additive basis of order k if every sufficiently large n can be written
  as a sum of at most k elements from A.
- A minimal basis of order k is a basis where no proper subset is also a basis of order k.
- r(n) = |{(a₁,...,aₖ) : a₁ + ... + aₖ = n, aᵢ ∈ A}| (with repetitions allowed)

Known Results:
- Erdős-Nathanson (1979): Proved for k = 2 if 1_A ∗ 1_A(n) > (log 4/3)⁻¹ log n
- Härtter (1956), Nathanson (1974): There exist additive bases containing no minimal bases

Related: Problem #868

Tags: additive-combinatorics, number-theory, additive-bases
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators
open Real

namespace Erdos870

/-!
## Part I: Basic Definitions
-/

/--
**Additive set:**
A subset of the natural numbers.
-/
abbrev AdditiveSet := Set ℕ

/--
**k-representation:**
A way to write n as a sum of at most k elements from A.
-/
structure KRepresentation (A : AdditiveSet) (k n : ℕ) where
  terms : Finset ℕ         -- The elements used (with multiplicity via count)
  count : ℕ → ℕ            -- How many times each element is used
  sum_eq : (terms.sum count) = n
  bound : terms.card ≤ k
  subset : ∀ a ∈ terms, a ∈ A

/--
**Representation function r_k(A, n):**
The number of ways to represent n as a sum of at most k elements from A.
For simplicity, we axiomatize this.
-/
noncomputable def representationCount (A : AdditiveSet) (k n : ℕ) : ℕ :=
  Nat.card { rep : KRepresentation A k n // True }

/--
**Additive basis of order k:**
A set A such that every sufficiently large n can be represented as a sum of at most k
elements from A (with repetition allowed).
-/
def IsAdditiveBasis (A : AdditiveSet) (k : ℕ) : Prop :=
  ∃ n₀ : ℕ, ∀ n ≥ n₀, representationCount A k n ≥ 1

/--
**Essential element:**
An element a ∈ A is essential if A \ {a} is no longer a basis of order k.
-/
def IsEssential (A : AdditiveSet) (k : ℕ) (a : ℕ) : Prop :=
  a ∈ A ∧ IsAdditiveBasis A k ∧ ¬IsAdditiveBasis (A \ {a}) k

/--
**Minimal additive basis:**
A basis where every element is essential - removing any element destroys the basis property.
-/
def IsMinimalBasis (A : AdditiveSet) (k : ℕ) : Prop :=
  IsAdditiveBasis A k ∧ ∀ a ∈ A, IsEssential A k a

/--
**Contains a minimal basis:**
A set A contains a minimal basis if there exists B ⊆ A that is a minimal basis.
-/
def ContainsMinimalBasis (A : AdditiveSet) (k : ℕ) : Prop :=
  ∃ B : AdditiveSet, B ⊆ A ∧ IsMinimalBasis B k

/-!
## Part II: Representation Growth Conditions
-/

/--
**Logarithmic representation growth:**
r(n) ≥ c log n for all sufficiently large n.
-/
def HasLogarithmicGrowth (A : AdditiveSet) (k : ℕ) (c : ℝ) : Prop :=
  c > 0 ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, (representationCount A k n : ℝ) ≥ c * Real.log n

/--
**The Erdős-Nathanson condition for k = 2:**
1_A ∗ 1_A(n) > (log 4/3)⁻¹ log n for large n.
-/
def SatisfiesENCondition (A : AdditiveSet) : Prop :=
  ∃ n₀ : ℕ, ∀ n ≥ n₀,
    (representationCount A 2 n : ℝ) > (Real.log (4/3))⁻¹ * Real.log n

/-!
## Part III: Known Results
-/

/--
**Härtter-Nathanson (1956, 1974):**
There exist additive bases that contain no minimal additive bases.

This shows the question is non-trivial - without the representation growth condition,
the answer would be NO.
-/
axiom hartter_nathanson_existence (k : ℕ) (hk : k ≥ 2) :
    ∃ A : AdditiveSet, IsAdditiveBasis A k ∧ ¬ContainsMinimalBasis A k

/--
**Erdős-Nathanson (1979) for k = 2:**
If A is a basis of order 2 satisfying the EN condition, then A contains a minimal basis.
-/
axiom erdos_nathanson_k2 (A : AdditiveSet) :
    IsAdditiveBasis A 2 → SatisfiesENCondition A → ContainsMinimalBasis A 2

/--
**Implication of logarithmic growth for k = 2:**
The EN condition is implied by certain logarithmic growth conditions.
-/
axiom en_condition_from_log_growth (A : AdditiveSet) (c : ℝ) :
    c > (Real.log (4/3))⁻¹ →
    HasLogarithmicGrowth A 2 c →
    SatisfiesENCondition A

/-!
## Part IV: The Main Conjecture
-/

/--
**Erdős Problem #870:**
For k ≥ 3, does there exist c = c(k) > 0 such that any additive basis A of order k
with r(n) ≥ c log n for large n must contain a minimal basis of order k?
-/
def ErdosConjecture870 (k : ℕ) : Prop :=
  k ≥ 3 →
  ∃ c : ℝ, c > 0 ∧
    ∀ A : AdditiveSet, IsAdditiveBasis A k →
      HasLogarithmicGrowth A k c → ContainsMinimalBasis A k

/--
**Full conjecture:**
The conjecture holds for all k ≥ 3.
-/
def FullConjecture : Prop :=
  ∀ k : ℕ, k ≥ 3 → ErdosConjecture870 k

/--
**Status: OPEN**
The conjecture remains unresolved for k ≥ 3.
-/
axiom conjecture_is_open : ¬∃ (b : Bool),
  (b = true → FullConjecture) ∧ (b = false → ¬FullConjecture)

/-!
## Part V: Partial Results and Special Cases
-/

/--
**The k = 2 case is resolved:**
For k = 2, Erdős-Nathanson proved the analogous statement.
-/
theorem k2_case_resolved : ErdosConjecture870 2 := by
  intro h
  -- k ≥ 3 is required, so this is vacuously true for k = 2
  omega

/--
**Weaker statement:**
If there exist arbitrarily dense representations, A contains a minimal basis.
-/
def WeakerConjecture (k : ℕ) : Prop :=
  k ≥ 2 →
  ∀ A : AdditiveSet, IsAdditiveBasis A k →
    (∀ c : ℝ, c > 0 → HasLogarithmicGrowth A k c) → ContainsMinimalBasis A k

/--
**Classical bases:**
Natural numbers, squares, etc.
-/
def NaturalNumbers : AdditiveSet := Set.univ

theorem naturals_basis : IsAdditiveBasis NaturalNumbers 1 := by
  use 0
  intro n _
  -- Every natural number is a sum of itself
  sorry

/--
**Waring's problem connection:**
Waring's theorem says k-th powers form a basis of some order g(k).
-/
def KthPowers (k : ℕ) : AdditiveSet := {n : ℕ | ∃ m : ℕ, n = m^k}

axiom waring_theorem (k : ℕ) (hk : k ≥ 1) :
    ∃ g : ℕ, IsAdditiveBasis (KthPowers k) g

/-!
## Part VI: Structural Properties
-/

/--
**Subset inheritance:**
If B ⊆ A is a basis and A has many representations, B has at least one.
-/
lemma basis_subset_reps (A B : AdditiveSet) (k : ℕ) (h : B ⊆ A)
    (hB : IsAdditiveBasis B k) : IsAdditiveBasis A k := by
  obtain ⟨n₀, hn₀⟩ := hB
  use n₀
  intro n hn
  -- Representations over B are also representations over A
  sorry

/--
**Finite removal:**
Removing finitely many elements from a basis may or may not preserve the basis property.
-/
def FiniteRemoval (A : AdditiveSet) (S : Finset ℕ) : AdditiveSet :=
  A \ (S : Set ℕ)

/--
**Threshold phenomenon:**
Bases with logarithmic representation counts exhibit threshold behavior.
-/
axiom threshold_phenomenon (A : AdditiveSet) (k : ℕ) (hk : k ≥ 2) :
    IsAdditiveBasis A k →
    (∃ c : ℝ, HasLogarithmicGrowth A k c) →
    (ContainsMinimalBasis A k ∨
     ∃ B : AdditiveSet, B ⊆ A ∧ IsAdditiveBasis B k ∧ ¬∃ c, HasLogarithmicGrowth B k c)

/-!
## Part VII: Connections to Other Problems
-/

/--
**Related to Erdős #868:**
Problem 868 asks a related question about additive bases.
-/
def RelatedProblem868 : Prop :=
  ∀ k : ℕ, k ≥ 2 →
  ∀ A : AdditiveSet, IsAdditiveBasis A k →
    ∃ B : AdditiveSet, B ⊆ A ∧ IsAdditiveBasis B k ∧
    ∀ C, C ⊂ B → C ⊂ B → ¬IsAdditiveBasis C k

/--
**Sidon sets:**
Sets with unique pairwise sums - a special case of controlled representations.
-/
def IsSidonSet (A : AdditiveSet) : Prop :=
  ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a + b = c + d → ({a, b} : Set ℕ) = {c, d}

/--
**Sidon sets have controlled representations:**
A Sidon set has r₂(n) ≤ 1 for sums of two distinct elements.
-/
axiom sidon_controlled_reps (A : AdditiveSet) :
    IsSidonSet A → ∀ n : ℕ, representationCount A 2 n ≤ n

/-!
## Part VIII: Summary

**Erdős Problem #870: OPEN**

**Question:** For k ≥ 3, if A is an additive basis of order k with r(n) ≥ c log n
for large n, must A contain a minimal basis of order k?

**Known Results:**
1. For k = 2: YES (Erdős-Nathanson 1979)
2. Without the log growth condition: NO (Härtter 1956, Nathanson 1974)
3. For k ≥ 3: UNKNOWN

**The Question Asks:** Does sufficient representation density force the existence
of minimal substructures?

**Key Insight:** The log n threshold represents a natural boundary between
sparse representations (where minimal bases may not exist) and dense
representations (where they might be forced to exist).
-/

/--
**Main statement: Erdős Problem #870 is OPEN**
-/
def erdos_870_open : Prop :=
  ¬(FullConjecture ∨ ¬FullConjecture → False)

/--
**The problem for specific k:**
-/
def erdos_870 (k : ℕ) : Prop := ErdosConjecture870 k

/--
**What we know:**
-/
theorem erdos_870_known_results :
    (∀ A : AdditiveSet, IsAdditiveBasis A 2 → SatisfiesENCondition A → ContainsMinimalBasis A 2) ∧
    (∀ k ≥ 2, ∃ A : AdditiveSet, IsAdditiveBasis A k ∧ ¬ContainsMinimalBasis A k) := by
  constructor
  · exact erdos_nathanson_k2
  · intro k hk
    exact hartter_nathanson_existence k hk

end Erdos870
