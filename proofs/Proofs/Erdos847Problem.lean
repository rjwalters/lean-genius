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

import Mathlib

open Nat Set Finset

namespace Erdos847

/- ## Part I: Arithmetic Progression Definitions -/

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

/-- Subsets of AP-free sets are AP-free. -/
theorem isAPFree_subset {S T : Set ℕ} (hT : isAPFree T) (hST : S ⊆ T) : isAPFree S :=
  fun a d hd ha had hz => hT a d hd (hST ha) (hST had) (hST hz)

/-- The two definitions of AP-free are equivalent. -/
theorem apfree_equiv (S : Set ℕ) : isAPFree S ↔ isAPFree' S := by
  unfold isAPFree isAPFree'
  constructor
  · -- Forward: no {a, a+d, a+2d} AP → no x < y < z with 2y = x+z
    intro h x y z hx hy hz hxy hyz heq
    have hd_pos : y - x > 0 := Nat.sub_pos_of_lt hxy
    have hy' : x + (y - x) ∈ S := by rwa [Nat.add_sub_cancel' (Nat.le_of_lt hxy)]
    have hnotS := h x (y - x) hd_pos hx hy'
    have h2d_eq : x + 2 * (y - x) = z := by omega
    rw [h2d_eq] at hnotS
    exact hnotS hz
  · -- Backward: no x < y < z with 2y = x+z → no {a, a+d, a+2d} AP
    intro h a d hd ha had hadd
    exact h a (a + d) (a + 2 * d) ha had hadd (by omega) (by omega) (by omega)

/- ## Part II: The Erdős-Nešetřil-Rödl Condition -/

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

/- ## Part III: Finite Union Characterization -/

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

/- ## Part IV: The Conjecture (Disproved) -/

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
Derived from the negation of the conjecture by classical logic.
¬(∀ A, Infinite A → ENR A → FiniteUnion A) gives ∃ A, ... ∧ ¬FiniteUnion A.
-/
theorem counterexample_exists :
    ∃ A : Set ℕ, A.Infinite ∧ hasENRProperty A ∧ ¬isFiniteAPFreeUnion A := by
  unfold ENRConjecture at enr_conjecture_false
  push_neg at enr_conjecture_false
  exact enr_conjecture_false

/- ## Part V: Connection to Szemerédi's Theorem -/

/--
**Szemerédi's Theorem (1975):**
For any k ≥ 3 and δ > 0, there exists N such that any subset of [1,N]
with density ≥ δ contains a k-term arithmetic progression.

This implies that AP-free sets have density 0.
-/
/--
**Density consequence:**
An AP-free subset of [1,N] has size o(N).
More precisely: |A ∩ [1,N]| / N → 0 as N → ∞.
-/
/- ## Part VI: Why the Conjecture Fails -/

/-
**Key insight:**
The ENR condition only requires *some* large AP-free subset of each
finite piece. It doesn't require the pieces to come from a single
finite collection of AP-free sets.

The counterexample likely uses a construction where:
1. Any finite subset has a density-ε AP-free part
2. But different subsets require different AP-free decompositions
3. No single finite collection works for all subsets
-/

/--
**Finite unions are very restrictive:**
If A = A₁ ∪ ... ∪ Aₖ with each Aᵢ AP-free, then any finite B ⊆ A
can be covered by k AP-free sets. But the ENR condition is weaker.

Proof sketch: Given B ⊆ A with |B| = n, by pigeonhole there exists
i such that |B ∩ parts(i)| ≥ n/k. This intersection is AP-free
(subset of AP-free set) and has the required size.
-/

/-- Pigeonhole principle for Finsets: mapping B into Fin k, some fiber
    has cardinality at least B.card / k. -/
private theorem finset_pigeonhole {α : Type*} [DecidableEq α] (B : Finset α)
    (k : ℕ) (hk : 0 < k) (f : α → Fin k) :
    ∃ i : Fin k, B.card ≤ k * (B.filter (fun x => f x = i)).card := by
  by_contra hall
  push_neg at hall
  have hsum : ∑ i : Fin k, (B.filter (fun x => f x = i)).card = B.card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext x; simp [Finset.mem_biUnion, Finset.mem_filter]
      exact ⟨fun hx => ⟨f x, hx, rfl⟩, fun ⟨_, hx, _⟩ => hx⟩
    · intro i _ j _ hij x
      simp [Finset.mem_filter]
      intro _ hi hj; exact absurd (hi ▸ hj) fun h => hij (Fin.ext h)
  have hlt : ∑ i : Fin k, k * (B.filter (fun x => f x = i)).card < k * B.card := by
    apply Finset.sum_lt_sum
    · intro i _; exact le_of_lt (hall i)
    · exact ⟨⟨0, hk⟩, Finset.mem_univ _, hall ⟨0, hk⟩⟩
  rw [← Finset.mul_sum] at hlt
  omega

theorem finite_union_implies_enr (A : Set ℕ) (k : ℕ) (hk : k > 0)
    (parts : Fin k → Set ℕ)
    (hparts : ∀ i, isAPFree (parts i))
    (hunion : A = ⋃ i, parts i) :
    hasENRCondition A (1 / k) := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  constructor
  · exact div_pos one_pos hkR
  · intro B hB
    -- Every element of B is in some parts(i)
    have hmem : ∀ x ∈ B, ∃ i : Fin k, x ∈ parts i := fun x hx =>
      Set.mem_iUnion.mp (hunion ▸ hB (Finset.mem_coe.mpr hx))
    classical
    -- Assign each element of B to a part containing it
    let assign : ℕ → Fin k :=
      fun x => if h : x ∈ B then (hmem x h).choose else ⟨0, hk⟩
    have hassign : ∀ x ∈ B, x ∈ parts (assign x) := by
      intro x hx; simp only [assign, dif_pos hx]; exact (hmem x hx).choose_spec
    -- By pigeonhole, some fiber has ≥ |B|/k elements
    obtain ⟨i, hi⟩ := finset_pigeonhole B k hk assign
    let C := B.filter (fun x => assign x = i)
    -- C ⊆ B
    have hCsub : (↑C : Set ℕ) ⊆ ↑B := by
      intro x hx; exact Finset.mem_coe.mpr (Finset.mem_of_mem_filter x (Finset.mem_coe.mp hx))
    -- C ⊆ parts i, so C is AP-free
    have hCinParts : (↑C : Set ℕ) ⊆ parts i := by
      intro x hx
      have hxf := Finset.mem_coe.mp hx
      have hxB := Finset.mem_of_mem_filter x hxf
      have hxa := (Finset.mem_filter.mp hxf).2
      rw [← hxa]; exact hassign x hxB
    refine ⟨C, hCsub, isAPFree_subset (hparts i) hCinParts, ?_⟩
    -- Show (1/k) * |B| ≤ |C|
    rw [div_mul_eq_mul_div, one_mul, le_div_iff hkR]
    exact_mod_cast hi

/- ## Part VII: Related Problems -/

/-
**Problem #774:**
Related to structure of sets avoiding APs.
-/

/-
**Problem #846:**
Adjacent problem in the Erdős collection on AP-free sets.
-/

/- ## Part VIII: Roth's Theorem and Bounds -/

/--
**Roth's Theorem (1953):**
The k=3 case of Szemerédi: any dense subset of [1,N] contains a 3-AP.

This was the first major result on AP-free sets.
-/
/--
**Best known bounds (Kelley-Meka 2023):**
An AP-free subset of [1,N] has size at most N exp(-c (log N)^{1/12}).
-/
/- ## Part IX: Summary -/

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
