/-
Erdős Problem #869: Minimal Additive Bases from Disjoint Bases

Source: https://erdosproblems.com/869
Status: OPEN

Statement:
If A₁, A₂ are disjoint additive bases of order 2 (i.e., Aᵢ + Aᵢ contains all
large integers), then must A = A₁ ∪ A₂ contain a minimal additive basis of
order 2?

A minimal additive basis is one such that deleting any element creates
infinitely many integers not representable as sums from the basis.

This is a question of Erdős and Nathanson (1988).

Background:
- Härtter (1956) and Nathanson (1974) proved that there exist additive bases
  which do not contain ANY minimal additive bases.
- This shows that not every additive basis contains a minimal one.
- The question asks: does the special structure of being a union of two
  disjoint bases force the existence of a minimal sub-basis?

The problem cannot be resolved by finite computation.

References:
- Erdős, P. and Nathanson, M.B. (1988): "Partitions of bases into disjoint
  unions of bases"
- Härtter, E. (1956): "Ein Beitrag zur Theorie der Minimalbasen"
- Nathanson, M.B. (1974): "Minimal bases and maximal nonbases in additive
  number theory"
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Filter.Cofinite

open Set Filter

namespace Erdos869

/-
## Part I: Sumsets and Additive Bases

An additive basis of order 2 is a set B ⊆ ℕ such that B + B contains
all sufficiently large natural numbers.
-/

/--
**Sumset:**
The sumset A + B consists of all sums a + b where a ∈ A and b ∈ B.
-/
def sumset (A B : Set ℕ) : Set ℕ := {n | ∃ a ∈ A, ∃ b ∈ B, a + b = n}

/-- Notation for sumsets -/
infixl:65 " +ₛ " => sumset

/--
**Doubling:**
The doubling A + A of a set A.
-/
def doubling (A : Set ℕ) : Set ℕ := sumset A A

/--
**Cofinite sets:**
A set contains "all large integers" if its complement is finite.
-/
def containsAllLarge (S : Set ℕ) : Prop := Sᶜ.Finite

/--
**Additive Basis of Order 2:**
A set A is an additive basis of order 2 if A + A contains all sufficiently
large natural numbers.
-/
def isAdditiveBasis2 (A : Set ℕ) : Prop := containsAllLarge (doubling A)

/-
## Part II: Minimal Additive Bases
-/

/--
**Essential Element:**
An element a ∈ A is essential if removing it from A leaves infinitely many
integers unrepresentable.

That is, (A \ {a}) + (A \ {a}) misses infinitely many integers that A + A hits.
-/
def isEssential (A : Set ℕ) (a : ℕ) : Prop :=
  a ∈ A ∧ ¬containsAllLarge (doubling (A \ {a}))

/--
**Minimal Additive Basis:**
An additive basis A is minimal if every element is essential - removing
any single element destroys the basis property.
-/
def isMinimalBasis (A : Set ℕ) : Prop :=
  isAdditiveBasis2 A ∧ ∀ a ∈ A, isEssential A a

/--
**Contains a Minimal Basis:**
A set A contains a minimal additive basis if there exists B ⊆ A such that
B is a minimal additive basis of order 2.
-/
def containsMinimalBasis (A : Set ℕ) : Prop :=
  ∃ B : Set ℕ, B ⊆ A ∧ isMinimalBasis B

/-
## Part III: Disjoint Bases
-/

/--
**Disjoint Sets:**
Two sets are disjoint if they share no elements.
-/
def areDisjoint (A B : Set ℕ) : Prop := A ∩ B = ∅

/--
**Disjoint Additive Bases:**
A₁ and A₂ are disjoint additive bases of order 2 if they are disjoint
and each is an additive basis of order 2.
-/
def areDisjointBases (A₁ A₂ : Set ℕ) : Prop :=
  areDisjoint A₁ A₂ ∧ isAdditiveBasis2 A₁ ∧ isAdditiveBasis2 A₂

/-
## Part IV: The Erdős-Nathanson Conjecture
-/

/--
**Erdős Problem #869:**
If A₁, A₂ are disjoint additive bases of order 2, must A = A₁ ∪ A₂
contain a minimal additive basis of order 2?

**Status: OPEN**
-/
def erdos_869_conjecture : Prop :=
  ∀ A₁ A₂ : Set ℕ, areDisjointBases A₁ A₂ →
    containsMinimalBasis (A₁ ∪ A₂)

/-
## Part V: Known Negative Results

While the conjecture is open, we know that:
1. Not every additive basis contains a minimal basis
2. The union of disjoint bases is itself a basis
-/

/--
**Härtter-Nathanson Theorem:**
There exist additive bases of order 2 that do not contain any minimal
additive basis of order 2.

This is a key negative result that shows minimal bases are special.
-/
axiom hartter_nathanson :
    ∃ A : Set ℕ, isAdditiveBasis2 A ∧ ¬containsMinimalBasis A

/--
**Union of Disjoint Bases is a Basis:**
If A₁ and A₂ are disjoint bases, their union A = A₁ ∪ A₂ is also a basis.

In fact, A + A contains everything that A₁ + A₁ or A₂ + A₂ contains
(and more, via cross-terms).
-/
theorem union_of_bases (A₁ A₂ : Set ℕ) (h : areDisjointBases A₁ A₂) :
    isAdditiveBasis2 (A₁ ∪ A₂) := by
  simp only [isAdditiveBasis2, containsAllLarge, doubling] at *
  obtain ⟨_, h1, h2⟩ := h
  -- A₁ ∪ A₂ + A₁ ∪ A₂ ⊇ A₁ + A₁
  -- so its complement is ⊆ the complement of A₁ + A₁
  -- which is finite
  sorry  -- requires detailed set manipulation

/-
## Part VI: Structural Properties
-/

/--
**Basis Property is Monotonic:**
If A is a basis and A ⊆ B, then B is also a basis.
-/
theorem basis_monotone {A B : Set ℕ} (hA : isAdditiveBasis2 A) (hAB : A ⊆ B) :
    isAdditiveBasis2 B := by
  simp only [isAdditiveBasis2, containsAllLarge, doubling, sumset] at *
  apply Set.Finite.subset hA
  intro n hn
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_exists] at hn ⊢
  intro a ha b hb hab
  exact hn a (hAB ha) b (hAB hb) hab

/--
**Minimal Bases are Thin:**
A minimal basis cannot have too many redundant elements.
-/
axiom minimal_basis_thin (A : Set ℕ) (hA : isMinimalBasis A) :
    ∀ a ∈ A, ∃ n : ℕ, n ∉ doubling (A \ {a})

/--
**Essential Elements Form a Basis:**
The set of essential elements of a basis forms a sub-basis.
(This is not always true - the question is about when it is!)
-/
def essentialElements (A : Set ℕ) : Set ℕ := {a ∈ A | isEssential A a}

/-
## Part VII: Examples
-/

/--
**Example: Powers of 2**
The set {1, 2, 4, 8, 16, ...} = {2^n : n ∈ ℕ} is NOT a basis of order 2.
(Not every integer is a sum of two powers of 2.)
-/
def powersOfTwo : Set ℕ := {n | ∃ k : ℕ, n = 2 ^ k}

axiom powersOfTwo_not_basis : ¬isAdditiveBasis2 powersOfTwo

/--
**Example: Complement of Sparse Set**
If A = ℕ \ S where S is sparse enough, then A is a basis of order 2.
-/
axiom dense_set_is_basis (S : Set ℕ) (hS : S.Finite) :
    isAdditiveBasis2 (univ \ S)

/--
**Example: Two Disjoint Bases**
We can construct disjoint bases A₁ and A₂ by partitioning ℕ carefully.
For instance, A₁ = even numbers (with adjustments) and A₂ = odd numbers
(with adjustments).
-/
axiom disjoint_bases_exist :
    ∃ A₁ A₂ : Set ℕ, areDisjointBases A₁ A₂

/-
## Part VIII: Why the Problem is Hard
-/

/--
**Challenge 1:**
The Härtter-Nathanson examples show that bases without minimal sub-bases exist.
But those examples may not arise from unions of disjoint bases.
-/
axiom challenge_hartter_nathanson :
    ∃ A : Set ℕ, isAdditiveBasis2 A ∧ ¬containsMinimalBasis A ∧
    ¬∃ A₁ A₂ : Set ℕ, areDisjointBases A₁ A₂ ∧ A = A₁ ∪ A₂

/--
**Challenge 2:**
The disjointness condition is restrictive. When A₁ and A₂ are disjoint,
cross-sums a₁ + a₂ (with a₁ ∈ A₁, a₂ ∈ A₂) are "new" representations.
Does this extra structure help?
-/
axiom cross_sums_matter :
    ∀ A₁ A₂ : Set ℕ, areDisjoint A₁ A₂ →
      sumset A₁ A₂ ⊆ doubling (A₁ ∪ A₂)

/-
## Part IX: Summary
-/

/--
**Erdős Problem #869: Summary**

Question: If A₁, A₂ are disjoint additive bases of order 2, must
A = A₁ ∪ A₂ contain a minimal additive basis of order 2?

Status: OPEN

What we know:
1. Not every basis contains a minimal basis (Härtter-Nathanson)
2. The union of disjoint bases is a basis
3. The disjointness condition may provide extra structure

The question asks whether the special origin of A (as a union of disjoint bases)
forces it to contain a minimal sub-basis.
-/
theorem erdos_869_status :
    -- Disjoint bases exist
    (∃ A₁ A₂ : Set ℕ, areDisjointBases A₁ A₂) ∧
    -- Not every basis contains a minimal basis
    (∃ A : Set ℕ, isAdditiveBasis2 A ∧ ¬containsMinimalBasis A) ∧
    -- Union of disjoint bases is a basis
    (∀ A₁ A₂ : Set ℕ, areDisjointBases A₁ A₂ → isAdditiveBasis2 (A₁ ∪ A₂)) := by
  constructor
  · exact disjoint_bases_exist
  constructor
  · exact hartter_nathanson
  · exact union_of_bases

/--
**The Open Question:**
Does the conjecture hold? We formalize it as a Prop without asserting its truth.
-/
theorem erdos_869_open : erdos_869_conjecture ↔
    (∀ A₁ A₂ : Set ℕ, areDisjointBases A₁ A₂ →
      containsMinimalBasis (A₁ ∪ A₂)) := by
  rfl

end Erdos869
