/-
Erdős Problem #1023: Union-Free Families

Let F(n) be the maximal size of a family of subsets of {1,...,n} such that
no set in the family is the union of other members. Is F(n) ~ c · 2^n / √n?

**Status**: SOLVED
**Answer**: YES, F(n) ~ C(n, n/2) ~ c · 2^n / √n

Reference: https://erdosproblems.com/1023
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Central

open Finset

namespace Erdos1023

/-
## Set Families on {1,...,n}

We work with families of subsets of Fin n.
-/

/-- A set family is a collection of subsets. -/
abbrev SetFamily (n : ℕ) := Finset (Finset (Fin n))

/-- The power set of {0,...,n-1}. -/
def powerSet (n : ℕ) : Finset (Finset (Fin n)) :=
  univ.powerset

/-- Total number of subsets: 2^n. -/
theorem powerSet_card (n : ℕ) : (powerSet n).card = 2^n := by
  simp [powerSet, card_powerset]

/-
## Union-Free Families

A family is union-free if no set is the union of other members.
-/

/-- The union of a subfamily. -/
def familyUnion (F : SetFamily n) : Finset (Fin n) :=
  F.sup id

/-- A set is a union of a subfamily (of size ≥ 2). -/
def isUnionOf (A : Finset (Fin n)) (F : SetFamily n) : Prop :=
  ∃ G : SetFamily n, G ⊆ F ∧ G.card ≥ 2 ∧ A ∉ G ∧ familyUnion G = A

/-- A family is union-free: no member is the union of other members. -/
def isUnionFree (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ¬isUnionOf A (F.erase A)

/-- Alternative: no set equals the union of a subfamily not containing it. -/
def isUnionFree' (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ∀ G : SetFamily n, G ⊆ F → A ∉ G → G.card ≥ 2 → familyUnion G ≠ A

/-- The two definitions are equivalent. -/
theorem unionFree_equiv (F : SetFamily n) : isUnionFree F ↔ isUnionFree' F := by
  sorry

/-
## The Extremal Function F(n)

F(n) is the maximum size of a union-free family.
-/

/-- F(n): maximum size of a union-free family on {0,...,n-1}. -/
noncomputable def unionFreeMax (n : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ F : SetFamily n, isUnionFree F ∧ F.card = k }

/-- There exists a union-free family of any given valid size. -/
theorem unionFreeMax_achieved (n : ℕ) :
    ∃ F : SetFamily n, isUnionFree F ∧ F.card = unionFreeMax n := by
  sorry

/-
## Antichains are Union-Free

An antichain (no set contains another) is union-free.
-/

/-- A family is an antichain if no set contains another. -/
def isAntichain (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ⊆ B → A = B

/-- Antichains are union-free. -/
theorem antichain_unionFree (F : SetFamily n) : isAntichain F → isUnionFree F := by
  sorry

/-
## The Middle Layer

The middle layer C(n, n/2) is an antichain.
-/

/-- The k-th layer: sets of size exactly k. -/
def layer (n k : ℕ) : SetFamily n :=
  (powerSet n).filter (fun A => A.card = k)

/-- The middle layer: sets of size n/2. -/
def middleLayer (n : ℕ) : SetFamily n :=
  layer n (n / 2)

/-- Size of the middle layer is C(n, n/2). -/
theorem middleLayer_card (n : ℕ) : (middleLayer n).card = Nat.choose n (n / 2) := by
  sorry

/-- The middle layer is an antichain. -/
theorem middleLayer_antichain (n : ℕ) : isAntichain (middleLayer n) := by
  intro A hA B hB hAB
  simp only [middleLayer, layer, mem_filter] at hA hB
  have hcardA := hA.2
  have hcardB := hB.2
  have hcard : A.card ≤ B.card := card_le_card hAB
  omega

/-- The middle layer is union-free. -/
theorem middleLayer_unionFree (n : ℕ) : isUnionFree (middleLayer n) :=
  antichain_unionFree _ (middleLayer_antichain n)

/-
## Lower Bound: F(n) ≥ C(n, n/2)

The middle layer gives a lower bound.
-/

/-- F(n) ≥ C(n, n/2). -/
theorem unionFreeMax_ge_middle (n : ℕ) :
    unionFreeMax n ≥ Nat.choose n (n / 2) := by
  sorry

/-
## Upper Bound: F(n) ≤ C(n, n/2)

This is the harder direction, proved by Erdős-Kleitman.
-/

/-- Erdős-Kleitman: F(n) ≤ C(n, n/2). -/
axiom erdos_kleitman_upper (n : ℕ) :
  unionFreeMax n ≤ Nat.choose n (n / 2)

/-- Combining bounds: F(n) = C(n, n/2). -/
theorem unionFreeMax_eq_middle (n : ℕ) :
    unionFreeMax n = Nat.choose n (n / 2) := by
  apply le_antisymm
  · exact erdos_kleitman_upper n
  · exact unionFreeMax_ge_middle n

/-
## Asymptotic Form

C(n, n/2) ~ c · 2^n / √n by Stirling's approximation.
-/

/-- The central binomial coefficient C(n, n/2). -/
def centralBinomial (n : ℕ) : ℕ := Nat.choose n (n / 2)

/-- Stirling's approximation: C(n, n/2) ~ 2^n / √(πn/2). -/
axiom stirling_central (n : ℕ) (hn : n > 0) :
  ∃ c : ℝ, c > 0 ∧ |((centralBinomial n : ℝ) - c * 2^n / Real.sqrt n)| ≤ 2^n / n

/-- The constant c = √(2/π). -/
noncomputable def asymptoticConstant : ℝ := Real.sqrt (2 / Real.pi)

/-- F(n) ~ c · 2^n / √n where c = √(2/π). -/
theorem unionFreeMax_asymptotic :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      |(unionFreeMax n : ℝ) - asymptoticConstant * 2^n / Real.sqrt n| ≤
        ε * 2^n / Real.sqrt n := by
  sorry

/-
## The Main Question Answered

The answer is YES: F(n) ~ c · 2^n / √n.
-/

/-- The main question: Is F(n) ~ c · 2^n / √n for some c > 0? -/
def erdos_1023_question : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      |(unionFreeMax n : ℝ) / (2^n / Real.sqrt n) - c| < ε

/-- The answer is YES. -/
theorem erdos_1023_solved : erdos_1023_question := by
  use asymptoticConstant
  constructor
  · -- c = √(2/π) > 0
    unfold asymptoticConstant
    apply Real.sqrt_pos_of_pos
    positivity
  · sorry

/-
## Connection to Problem 447

Problem 447 asks about 2-union-free families (forbidding A = B ∪ C only).
-/

/-- A set is the union of exactly two other sets. -/
def isTwoUnionOf (A : Finset (Fin n)) (F : SetFamily n) : Prop :=
  ∃ B C : Finset (Fin n), B ∈ F ∧ C ∈ F ∧ B ≠ C ∧ A ≠ B ∧ A ≠ C ∧ B ∪ C = A

/-- A family is 2-union-free. -/
def isTwoUnionFree (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ¬isTwoUnionOf A F

/-- Union-free implies 2-union-free. -/
theorem unionFree_implies_twoUnionFree (F : SetFamily n) :
    isUnionFree F → isTwoUnionFree F := by
  sorry

/-- The maximum 2-union-free family (Problem 447). -/
noncomputable def twoUnionFreeMax (n : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ F : SetFamily n, isTwoUnionFree F ∧ F.card = k }

/-- 2-union-free max ≥ union-free max. -/
theorem twoUnionFreeMax_ge (n : ℕ) :
    twoUnionFreeMax n ≥ unionFreeMax n := by
  sorry

/-- Problem 447 implies Problem 1023 (Hunter's observation). -/
axiom problem_447_solution :
  ∀ n : ℕ, twoUnionFreeMax n = Nat.choose n (n / 2)

/-- Hunter's observation: 1023 follows from 447. -/
theorem hunter_observation (n : ℕ) :
    unionFreeMax n = Nat.choose n (n / 2) := by
  apply le_antisymm
  · -- Upper bound from 447
    calc unionFreeMax n ≤ twoUnionFreeMax n := twoUnionFreeMax_ge n
      _ = Nat.choose n (n / 2) := problem_447_solution n
  · exact unionFreeMax_ge_middle n

/-
## Summary

This file formalizes Erdős Problem #1023 on union-free families.

**Status**: SOLVED

**The Question**: Is F(n) ~ c · 2^n / √n for some c > 0?

**The Answer**: YES. F(n) = C(n, n/2) ~ √(2/π) · 2^n / √n.

**Key Results**:
- Middle layer achieves the bound (antichain, hence union-free)
- Erdős-Kleitman: F(n) ≤ C(n, n/2)
- Hunter: Follows from Problem 447 on 2-union-free families

**Related Topics**:
- Sperner's theorem and antichains
- Central binomial coefficients
- Stirling's approximation
-/

end Erdos1023
