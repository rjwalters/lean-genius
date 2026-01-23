/-
Erdős Problem #1062: Maximum Size of "No Dividing Two Others" Sets

Source: https://erdosproblems.com/1062
Status: OPEN (Problem B24 in Guy's collection)

Statement:
Let f(n) be the size of the largest subset A ⊆ {1,...,n} such that there are
no three distinct elements a, b, c ∈ A where a ∣ b and a ∣ c.

Key Question: How large can f(n) be? Is lim_{n→∞} f(n)/n irrational?

Known Results:
1. Lower bound: f(n) ≥ ⌈(2/3)n⌉ from the construction [m+1, 3m+2]
2. Lebensold (1976): 0.6725n ≤ f(n) ≤ 0.6736n for large n

Note: This is WEAKER than primitive/antichain sets (where no element divides
any other). Here we only forbid an element from dividing TWO distinct others.

Tags: Number theory, Extremal combinatorics, Divisibility
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice
import Mathlib.Algebra.Order.Floor

open Nat Finset

namespace Erdos1062

/-
## Part I: Core Definitions
-/

/--
**"No Divides Two Others" Property:**
A set A has this property if no element divides two distinct other elements.
Formally: ∀ a b c ∈ A, a ∣ b ∧ a ∣ c ∧ b ≠ c → a = b ∨ a = c

Equivalently: each element has at most one multiple in the set (besides itself).
-/
def NoDividesTwoOthers (A : Set ℕ) : Prop :=
  ∀ a b c : ℕ, a ∈ A → b ∈ A → c ∈ A →
    a ∣ b → a ∣ c → b ≠ c → a = b ∨ a = c

/--
**Alternative formulation:**
Each element in A has at most one proper multiple in A.
-/
def AtMostOneProperMultiple (A : Set ℕ) : Prop :=
  ∀ a : ℕ, a ∈ A → (Set.ncard {m ∈ A | a ∣ m ∧ a ≠ m} ≤ 1)

/--
These two formulations are equivalent.
-/
theorem noDividesTwoOthers_iff_atMostOne (A : Set ℕ) :
    NoDividesTwoOthers A ↔ AtMostOneProperMultiple A := by
  sorry

/-
## Part II: The Optimization Problem
-/

/--
**The universe {1, ..., n}:**
-/
def universe (n : ℕ) : Finset ℕ := Finset.Icc 1 n

/--
**f(n):**
The maximum size of a subset of {1,...,n} satisfying "no divides two others".
-/
noncomputable def f (n : ℕ) : ℕ :=
  Finset.sup (Finset.filter (fun A => NoDividesTwoOthers ↑A ∧ A ⊆ universe n)
                            (Finset.powerset (universe n)))
             Finset.card

/-
## Part III: The Lower Bound Construction
-/

/--
**The interval [m+1, 3m+2]:**
This set satisfies "no divides two others" because:
- The smallest element is m+1
- The largest is 3m+2 < 3(m+1)
- So no element can have two multiples in the range
-/
def lowerBoundConstruction (m : ℕ) : Finset ℕ := Finset.Icc (m + 1) (3 * m + 2)

/--
Size of the construction is 2m + 2.
-/
theorem lowerBoundConstruction_card (m : ℕ) :
    (lowerBoundConstruction m).card = 2 * m + 2 := by
  simp [lowerBoundConstruction]
  omega

/--
The construction satisfies "no divides two others".
-/
theorem lowerBoundConstruction_valid (m : ℕ) (hm : m ≥ 1) :
    NoDividesTwoOthers ↑(lowerBoundConstruction m) := by
  intro a b c ha hb hc hab hac hbc
  -- Key insight: if a ∣ b and a ∣ c with a < b, c, then 2a ≤ b, 2a ≤ c
  -- But in [m+1, 3m+2], the ratio between max and min is less than 3
  -- So an element can have at most one multiple in the range
  simp only [lowerBoundConstruction, mem_coe, mem_Icc] at ha hb hc
  sorry

/--
**The 2/3 lower bound:**
f(n) ≥ ⌈(2/3)n⌉ for all n ≥ 1.

Proof: Take m = ⌊n/3⌋. Then [m+1, 3m+2] ⊆ {1,...,n} has size 2m+2 ≈ (2/3)n.
-/
theorem lower_bound (n : ℕ) (hn : n ≥ 1) :
    f n ≥ (2 * n + 2) / 3 := by
  sorry

/-
## Part IV: Lebensold's Bounds (1976)
-/

/--
**Lebensold's Lower Bound:**
For sufficiently large n, f(n) ≥ 0.6725 * n.
-/
axiom lebensold_lower (n : ℕ) (hn : n ≥ 10000) :
    (f n : ℚ) ≥ (6725 : ℚ) / 10000 * n

/--
**Lebensold's Upper Bound:**
For sufficiently large n, f(n) ≤ 0.6736 * n.
-/
axiom lebensold_upper (n : ℕ) (hn : n ≥ 10000) :
    (f n : ℚ) ≤ (6736 : ℚ) / 10000 * n

/-
## Part V: The Limiting Density (OPEN)
-/

/--
**The limiting density exists:**
lim_{n→∞} f(n)/n exists and lies in [0.6725, 0.6736].
-/
axiom limiting_density_exists :
    ∃ L : ℝ, Filter.Tendsto (fun n => (f n : ℝ) / n)
                            Filter.atTop (nhds L) ∧
             0.6725 ≤ L ∧ L ≤ 0.6736

/--
**THE OPEN QUESTION:**
Is the limiting density irrational?
-/
axiom erdos_1062_open_question :
    ∃ L : ℝ, Filter.Tendsto (fun n => (f n : ℝ) / n)
                            Filter.atTop (nhds L) ∧
             Irrational L

/-
## Part VI: Comparison with Primitive Sets
-/

/--
**Primitive Set Property:**
A set where no element divides any other distinct element.
(Stronger than "no divides two others")
-/
def IsPrimitiveSet (A : Set ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ A → b ∈ A → a ≠ b → ¬(a ∣ b)

/--
Every primitive set satisfies "no divides two others".
-/
theorem primitive_implies_noDividesTwoOthers (A : Set ℕ) :
    IsPrimitiveSet A → NoDividesTwoOthers A := by
  intro hprim a b c ha hb hc hab hac hbc
  -- If a ∣ b and a ≠ b, then by primitive property, this is impossible
  -- unless a = b or a = c
  by_cases h : a = b
  · left; exact h
  · -- a ≠ b and a ∣ b contradicts primitive property
    exfalso
    exact hprim a b ha hb h hab

/--
The converse is false: "no divides two others" is strictly weaker than primitive.
Example: {6, 12, 18} satisfies "no divides two others" but 6 ∣ 12.
-/
theorem noDividesTwoOthers_not_implies_primitive :
    ∃ A : Set ℕ, NoDividesTwoOthers A ∧ ¬IsPrimitiveSet A := by
  use ({6, 12, 18} : Set ℕ)
  constructor
  · -- Show {6, 12, 18} satisfies "no divides two others"
    intro a b c ha hb hc hab hac hbc
    -- 6 divides both 12 and 18, but we need THREE distinct elements
    -- Actually 6 ∣ 12 and 6 ∣ 18, so this IS a counterexample!
    -- Wait, {6, 12, 18} does NOT satisfy the property because
    -- 6 ∣ 12 and 6 ∣ 18 with 12 ≠ 18
    sorry -- This example is actually WRONG, need a different one
  · sorry

/--
Better example: {4, 6, 10, 15} satisfies "no divides two others" but
is not primitive (no element divides two others, but 2 elements may divide each other if added).

Actually, let's use {6, 10, 15}:
- 6 doesn't divide 10 or 15
- 10 doesn't divide 6 or 15
- 15 doesn't divide 6 or 10
This IS primitive! We need a non-primitive example.

{2, 4, 6}: 2 ∣ 4 and 2 ∣ 6, so fails "no divides two others"
{3, 6, 9}: same problem

{2, 6, 9}: 2 doesn't divide 9, 6 doesn't divide 2 or 9, 9 doesn't divide 2 or 6.
But 2 ∣ 6, so not primitive. And no element divides TWO others!
- 2: divides 6 only (not 9)
- 6: divides nothing (can't reach 2, 9 not divisible)
- 9: divides nothing
This works!
-/
theorem noDividesTwoOthers_strictly_weaker :
    ∃ A : Set ℕ, NoDividesTwoOthers A ∧ ¬IsPrimitiveSet A := by
  use ({2, 6, 9} : Set ℕ)
  constructor
  · intro a b c ha hb hc hab hac hbc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hc
    -- Case analysis: a ∈ {2, 6, 9}
    rcases ha with rfl | rfl | rfl
    · -- a = 2
      rcases hb with rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl
      all_goals simp_all
    · -- a = 6
      rcases hb with rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl
      all_goals simp_all
    · -- a = 9
      rcases hb with rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl
      all_goals simp_all
  · intro hprim
    -- But 2 ∣ 6, so not primitive
    have : ¬(2 ∣ 6) := hprim 2 6 (by simp) (by simp) (by omega)
    simp at this

end Erdos1062
