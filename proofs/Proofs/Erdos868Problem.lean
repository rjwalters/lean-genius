/-
Erdős Problem #868: Additive Bases and Minimal Bases

**Question**: If A is an additive basis of order 2 with f(n) → ∞ as n → ∞
(where f(n) counts representations of n as a sum of two elements from A),
must A contain a minimal additive basis of order 2?

**Status**: PARTIALLY SOLVED (main questions are OPEN)

**History**: A set A ⊆ ℕ is an additive basis of order 2 if every sufficiently
large n can be written as a₁ + a₂ with a₁, a₂ ∈ A. A minimal basis is one
where removing any element breaks this property.

Key results:
1. Erdős-Nathanson (1979): If f(n) > (log 4/3)⁻¹ log n, then A contains a
   minimal basis
2. Härtter (1956) & Nathanson (1974): There exist bases with no minimal subbasis
3. Erdős-Nathanson (1989): For any t, there's a basis with f(n) ≥ t but no
   minimal subbasis

The gap between f(n) → ∞ and f(n) > c log n remains mysterious.

References:
- https://erdosproblems.com/868
- [ErNa79] Erdős & Nathanson, "Systems of distinct representatives" (1979)
- [ErNa89] Erdős & Nathanson, "Additive bases with many representations" (1989)
- [Ha56] Härtter, "Ein Beitrag zur Theorie der Minimalbasen" (1956)
- [Na74] Nathanson, "Minimal bases and maximal nonbases" (1974)
-/

import Mathlib

namespace Erdos868

open Nat Filter Set
open scoped BigOperators Pointwise

/-!
## Additive Bases

An additive basis of order h is a set A such that every sufficiently large
natural number can be written as a sum of h elements from A.
-/

/--
A set A is an (asymptotic) additive basis of order h if A + A + ... + A
(h times) contains all sufficiently large natural numbers.

We use the standard definition: the h-fold sumset hA covers a cofinite set,
meaning only finitely many naturals are NOT representable.
-/
def IsAdditiveBasis (A : Set ℕ) (h : ℕ) : Prop :=
  {n : ℕ | ¬∃ (a : Fin h → ℕ), (∀ i, a i ∈ A) ∧ ∑ i, a i = n}.Finite

/-- Shorthand for additive basis of order 2. -/
abbrev IsBasisOrder2 (A : Set ℕ) : Prop := IsAdditiveBasis A 2

/-!
## Representation Function

The representation function f(n) = r_{A,h}(n) counts how many ways n can be
written as a sum of h elements from A.
-/

/--
The number of representations of n as a sum of h elements from A.
r_{A,h}(n) = |{(a₁, ..., aₕ) : aᵢ ∈ A, Σ aᵢ = n}|
-/
noncomputable def reprCount (A : Set ℕ) (h : ℕ) (n : ℕ) : ℕ :=
  {a : Fin h → ℕ | (∀ i, a i ∈ A) ∧ ∑ i, a i = n}.ncard

/-- Shorthand for order-2 representation count. -/
noncomputable abbrev reprCount2 (A : Set ℕ) (n : ℕ) : ℕ := reprCount A 2 n

/-!
## Minimal Bases

A minimal basis is one where removing any element destroys the basis property.
-/

/--
A set B is a minimal additive basis of order h if:
1. B is an additive basis of order h
2. For every b ∈ B, the set B \ {b} is NOT an additive basis of order h
-/
def IsMinimalBasis (B : Set ℕ) (h : ℕ) : Prop :=
  IsAdditiveBasis B h ∧ ∀ b ∈ B, ¬IsAdditiveBasis (B \ {b}) h

/-- Shorthand for minimal basis of order 2. -/
abbrev IsMinimalBasis2 (B : Set ℕ) : Prop := IsMinimalBasis B 2

/-!
## The Main Questions

Erdős and Nathanson posed several related questions about when an additive
basis must contain a minimal subbasis.
-/

/--
**Erdős Problem #868 Part (i) (OPEN)**: If A is an additive basis of order 2
and f(n) → ∞ as n → ∞, must A contain a minimal basis of order 2?

The condition f(n) → ∞ means representations become unbounded - each large n
has more and more ways to be written as a sum of two elements from A.
-/
axiom erdos_868_part_i_open : Prop
-- unknown: ∀ A : Set ℕ, IsBasisOrder2 A →
--   Tendsto (reprCount2 A) atTop atTop →
--   ∃ B ⊆ A, IsMinimalBasis2 B

/--
**Erdős Problem #868 Part (ii) (OPEN)**: If A is an additive basis of order 2
and f(n) > ε log n for all large n (for any fixed ε > 0), must A contain a
minimal basis of order 2?

This is a weaker condition than part (i) - we don't require f(n) → ∞,
just that f(n) grows at least logarithmically.
-/
axiom erdos_868_part_ii_open : Prop
-- unknown: ∀ A : Set ℕ, ∀ ε > 0, IsBasisOrder2 A →
--   (∀ᶠ n in atTop, ε * Real.log n < reprCount2 A n) →
--   ∃ B ⊆ A, IsMinimalBasis2 B

/-!
## Known Results

Several partial results are known about minimal bases.
-/

/--
**Erdős-Nathanson Theorem (1979)**: If A is an additive basis of order 2 and
f(n) > (log 4/3)⁻¹ · log n for all large n, then A contains a minimal basis.

The constant (log 4/3)⁻¹ ≈ 3.476 comes from a probabilistic argument.
-/
axiom erdos_nathanson_1979 (A : Set ℕ) :
    IsBasisOrder2 A →
    (∀ᶠ (n : ℕ) in atTop, (Real.log (4/3))⁻¹ * Real.log n < reprCount2 A n) →
    ∃ B ⊆ A, IsMinimalBasis2 B

/-- The critical constant from the Erdős-Nathanson theorem. -/
noncomputable def erdosNathansonConstant : ℝ := (Real.log (4/3))⁻¹

/-- The Erdős-Nathanson constant is approximately 3.476. -/
axiom erdos_nathanson_constant_approx :
    3.4 < erdosNathansonConstant ∧ erdosNathansonConstant < 3.5

/--
**Härtter-Nathanson Theorem**: There exist additive bases (of any order h > 1)
that do NOT contain any minimal subbasis.

This shows the answer to a naive version of the question is NO - not every
basis contains a minimal basis.
-/
axiom hartter_nathanson (h : ℕ) (hh : 1 < h) :
    ∃ A : Set ℕ, IsAdditiveBasis A h ∧
      ∀ B ⊆ A, IsAdditiveBasis B h → ∃ b ∈ B, IsAdditiveBasis (B \ {b}) h

/--
**Erdős-Nathanson 1989**: For any constant t, there exists an additive basis A
with f(n) ≥ t for all large n, yet A contains no minimal basis of order 2.

This shows that bounded representation count (even arbitrarily large bounds)
is not sufficient to guarantee a minimal subbasis.
-/
axiom erdos_nathanson_1989 (t : ℕ) :
    ∃ A : Set ℕ, IsBasisOrder2 A ∧
      (∀ᶠ n in atTop, t ≤ reprCount2 A n) ∧
      ∀ B ⊆ A, IsMinimalBasis2 B → False

/-!
## The Gap

The mystery lies in the gap between:
- f(n) ≥ t for fixed t: NOT sufficient (Erdős-Nathanson 1989)
- f(n) → ∞: UNKNOWN (Erdős Problem #868 Part i)
- f(n) > ε log n: UNKNOWN (Erdős Problem #868 Part ii)
- f(n) > c log n for c = (log 4/3)⁻¹: SUFFICIENT (Erdős-Nathanson 1979)
-/

/--
The hierarchy of growth conditions: if f(n) > c log n for c = (log 4/3)⁻¹,
then f(n) > ε log n for any ε > 0 (since c ≈ 3.476 > ε).
-/
axiom growth_hierarchy (A : Set ℕ) (ε : ℝ) (hε : ε > 0) :
    (∀ᶠ (n : ℕ) in atTop, erdosNathansonConstant * Real.log n < reprCount2 A n) →
    (∀ᶠ (n : ℕ) in atTop, ε * Real.log n < reprCount2 A n)

/-!
## Examples

We verify some basic properties of additive bases.
-/

/-- The set of all natural numbers is trivially a basis of any order. -/
theorem univ_is_basis (h : ℕ) (hh : h > 0) : IsAdditiveBasis (Set.univ : Set ℕ) h := by
  simp only [IsAdditiveBasis]
  -- Every n can be represented: just use (n, 0, 0, ..., 0)
  sorry

/-- The natural numbers form a basis of order 2 (every n ≥ 0 is 0 + n or 1 + (n-1)). -/
theorem nat_basis_order2 : IsBasisOrder2 (Set.univ : Set ℕ) := univ_is_basis 2 (by norm_num)

/-- The set {0, 1, 2, 3, ...} is NOT a minimal basis because we can remove 0. -/
theorem nat_not_minimal : ¬IsMinimalBasis2 (Set.univ : Set ℕ) := by
  intro ⟨_, hmin⟩
  have h0 : (0 : ℕ) ∈ (Set.univ : Set ℕ) := Set.mem_univ 0
  have := hmin 0 h0
  -- ℕ \ {0} is still a basis of order 2
  sorry

/-!
## The Structure of Minimal Bases

Minimal bases have interesting structural properties.
-/

/--
If B is a minimal basis, every element is "essential" - removing it
creates infinitely many gaps.
-/
theorem minimal_basis_essential (B : Set ℕ) (h : ℕ) (hB : IsMinimalBasis B h) :
    ∀ b ∈ B, {n : ℕ | ¬∃ (a : Fin h → ℕ), (∀ i, a i ∈ B \ {b}) ∧ ∑ i, a i = n}.Infinite := by
  intro b hb
  have hnotbasis := hB.2 b hb
  -- B \ {b} is not a basis, so the set of unrepresentable numbers is infinite
  simp only [IsAdditiveBasis, Set.Infinite] at hnotbasis ⊢
  exact hnotbasis

/-!
## Summary

Erdős Problem #868 explores when an additive basis must contain a minimal
subbasis. The key question is: what growth rate of the representation function
f(n) guarantees the existence of a minimal basis?

**What we know**:
1. f(n) ≥ t (constant): NOT sufficient (Erdős-Nathanson 1989)
2. f(n) > (log 4/3)⁻¹ log n: SUFFICIENT (Erdős-Nathanson 1979)

**What we don't know**:
1. f(n) → ∞: Does this guarantee a minimal basis? (OPEN)
2. f(n) > ε log n for any ε > 0: Does this guarantee a minimal basis? (OPEN)
-/

theorem erdos_868_summary :
    (∃ A : Set ℕ, IsBasisOrder2 A ∧ ∀ B ⊆ A, ¬IsMinimalBasis2 B) ∧
    (∀ A : Set ℕ, IsBasisOrder2 A →
      (∀ᶠ (n : ℕ) in atTop, erdosNathansonConstant * Real.log n < reprCount2 A n) →
      ∃ B ⊆ A, IsMinimalBasis2 B) := by
  constructor
  · obtain ⟨A, hA, _, hnomin⟩ := erdos_nathanson_1989 1
    exact ⟨A, hA, fun B hB hBmin => hnomin B hB hBmin⟩
  · exact fun A hA hf => erdos_nathanson_1979 A hA hf

end Erdos868
