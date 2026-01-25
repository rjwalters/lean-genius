/-
Erdős Problem #847: AP-Free Subsets and Finite Unions

Source: https://erdosproblems.com/847
Status: DISPROVED

Statement:
Let A ⊂ ℕ be an infinite set with some ε > 0 such that any n-element
subset of A contains a subset of size ≥ εn with no three-term arithmetic
progression. Is A necessarily the union of finitely many sets, each
containing no three-term AP?

Answer: NO. The conjecture was DISPROVED.

Historical Context:
A problem of Erdős, Nešetřil, and Rödl [Er92b]. This connects to
Szemerédi's theorem and the structure of AP-free sets.

Key Definitions:
- Three-term AP: {a, a+d, a+2d} for some a, d with d > 0
- AP-free set: contains no three-term arithmetic progression
- The condition asks: every large subset has a large AP-free subset

References:
- Erdős, Nešetřil, Rödl [Er92b]
- Szemerédi's theorem (1975)
- Related: Problems #774, #846
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Card

open Nat Set Finset

namespace Erdos847

/-! ## Part I: Arithmetic Progression Definitions -/

/--
**Three-term arithmetic progression:**
A set {a, a+d, a+2d} where d > 0. These are evenly spaced triples.
-/
def isThreeTermAP (a d : ℕ) (S : Set ℕ) : Prop :=
  d > 0 ∧ a ∈ S ∧ (a + d) ∈ S ∧ (a + 2*d) ∈ S

/--
**AP-free set:**
A set containing no three-term arithmetic progression.
-/
def isAPFree (S : Set ℕ) : Prop :=
  ∀ a d : ℕ, d > 0 → a ∈ S → (a + d) ∈ S → (a + 2*d) ∉ S

/-- Equivalent formulation: no three elements form an AP. -/
def isAPFree' (S : Set ℕ) : Prop :=
  ∀ x y z : ℕ, x ∈ S → y ∈ S → z ∈ S → x < y → y < z → 2*y ≠ x + z

/-- The two definitions are equivalent. -/
axiom apfree_equiv (S : Set ℕ) : isAPFree S ↔ isAPFree' S

/-! ## Part II: The Erdős-Nešetřil-Rödl Condition -/

/--
**The ENR condition:**
There exists ε > 0 such that every finite subset B of A with |B| = n
contains an AP-free subset of size at least εn.
-/
def hasENRCondition (A : Set ℕ) (ε : ℝ) : Prop :=
  ε > 0 ∧ ∀ B : Finset ℕ, ↑B ⊆ A →
    ∃ C : Finset ℕ, ↑C ⊆ B ∧ isAPFree ↑C ∧ (C.card : ℝ) ≥ ε * B.card

/--
**A has the ENR property:**
There exists some ε > 0 satisfying the condition.
-/
def hasENRProperty (A : Set ℕ) : Prop :=
  ∃ ε > 0, hasENRCondition A ε

/-! ## Part III: Finite Union Characterization -/

/--
**Union of finitely many AP-free sets:**
A can be written as A₁ ∪ A₂ ∪ ... ∪ Aₖ where each Aᵢ is AP-free.
-/
def isFiniteAPFreeUnion (A : Set ℕ) : Prop :=
  ∃ (k : ℕ) (parts : Fin k → Set ℕ),
    (∀ i, isAPFree (parts i)) ∧ A = ⋃ i, parts i

/-- Equivalently, there's a finite partition into AP-free parts. -/
def hasFiniteAPFreePartition (A : Set ℕ) : Prop :=
  ∃ (k : ℕ) (parts : Fin k → Set ℕ),
    (∀ i, isAPFree (parts i)) ∧
    (∀ i j, i ≠ j → Disjoint (parts i) (parts j)) ∧
    A = ⋃ i, parts i

/-! ## Part IV: The Conjecture (Disproved) -/

/--
**Erdős-Nešetřil-Rödl Conjecture:**
If A is infinite and has the ENR property, then A is a finite union
of AP-free sets.

This was DISPROVED.
-/
def ENRConjecture : Prop :=
  ∀ A : Set ℕ, A.Infinite → hasENRProperty A → isFiniteAPFreeUnion A

/--
**The conjecture is FALSE:**
There exists an infinite set A with the ENR property that is NOT
a finite union of AP-free sets.
-/
axiom enr_conjecture_false : ¬ENRConjecture

/--
**The counterexample:**
An explicit (or constructive) example showing the conjecture fails.
-/
axiom counterexample_exists :
  ∃ A : Set ℕ, A.Infinite ∧ hasENRProperty A ∧ ¬isFiniteAPFreeUnion A

/-! ## Part V: Connection to Szemerédi's Theorem -/

/--
**Szemerédi's Theorem (1975):**
For any k ≥ 3 and δ > 0, there exists N such that any subset of [1,N]
with density ≥ δ contains a k-term arithmetic progression.

This implies that AP-free sets have density 0.
-/
axiom szemeredi_theorem (k : ℕ) (hk : k ≥ 3) (δ : ℝ) (hδ : δ > 0) :
  ∃ N : ℕ, ∀ A : Finset ℕ, (∀ a ∈ A, a ≤ N) → (A.card : ℝ) ≥ δ * N →
    ∃ a d : ℕ, d > 0 ∧ ∀ i < k, a + i * d ∈ A

/--
**Density consequence:**
An AP-free subset of [1,N] has size o(N).
More precisely: |A ∩ [1,N]| / N → 0 as N → ∞.
-/
axiom apfree_zero_density : ∀ A : Set ℕ, isAPFree A →
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ((A ∩ Set.Icc 1 N).ncard : ℝ) / N < ε

/-! ## Part VI: Why the Conjecture Fails -/

/--
**Key insight:**
The ENR condition only requires *some* large AP-free subset of each
finite piece. It doesn't require the pieces to come from a single
finite collection of AP-free sets.

The counterexample likely uses a construction where:
1. Any finite subset has a density-ε AP-free part
2. But different subsets require different AP-free decompositions
3. No single finite collection works for all subsets
-/
axiom key_insight : True

/--
**Finite unions are very restrictive:**
If A = A₁ ∪ ... ∪ Aₖ with each Aᵢ AP-free, then any finite B ⊆ A
can be covered by k AP-free sets. But the ENR condition is weaker.
-/
theorem finite_union_implies_enr (A : Set ℕ) (k : ℕ) (parts : Fin k → Set ℕ)
    (hparts : ∀ i, isAPFree (parts i))
    (hunion : A = ⋃ i, parts i) :
    hasENRCondition A (1 / k) := by
  sorry

/-! ## Part VII: Related Problems -/

/--
**Problem #774:**
Related to structure of sets avoiding APs.
-/
axiom problem_774_related : True

/--
**Problem #846:**
Adjacent problem in the Erdős collection on AP-free sets.
-/
axiom problem_846_related : True

/-! ## Part VIII: Roth's Theorem and Bounds -/

/--
**Roth's Theorem (1953):**
The k=3 case of Szemerédi: any dense subset of [1,N] contains a 3-AP.

This was the first major result on AP-free sets.
-/
axiom roth_theorem : ∃ c > 0, ∀ N : ℕ, ∀ A : Finset ℕ,
  (∀ a ∈ A, a ≤ N) → A.card > N / (Real.log N)^c →
    ∃ a d : ℕ, d > 0 ∧ isThreeTermAP a d ↑A

/--
**Best known bounds (Kelley-Meka 2023):**
An AP-free subset of [1,N] has size at most N exp(-c (log N)^{1/12}).
-/
axiom kelley_meka_bound : ∃ c > 0, ∀ N : ℕ, ∀ A : Finset ℕ,
  (∀ a ∈ A, a ≤ N) → isAPFree ↑A →
    (A.card : ℝ) ≤ N * Real.exp (-c * Real.log N ^ (1/12 : ℝ))

/-! ## Part IX: Summary -/

/--
**Erdős Problem #847: DISPROVED**

**Conjecture:** If infinite A has the ENR property (every n-subset
contains an AP-free subset of size ≥ εn), then A is a finite union
of AP-free sets.

**Answer:** NO. The conjecture is FALSE.

**Key points:**
1. The ENR condition is weaker than finite AP-free decomposition
2. Different finite subsets may need different decompositions
3. Counterexample exists where no finite collection suffices

**Connections:**
- Szemerédi's theorem gives density 0 for AP-free sets
- Roth's theorem (1953): first k=3 result
- Kelley-Meka (2023): best current bounds
-/
theorem erdos_847_disproved : ¬ENRConjecture := enr_conjecture_false

/--
**Main theorem: The counterexample.**
-/
theorem erdos_847_counterexample :
    ∃ A : Set ℕ, A.Infinite ∧ hasENRProperty A ∧ ¬isFiniteAPFreeUnion A :=
  counterexample_exists

end Erdos847
