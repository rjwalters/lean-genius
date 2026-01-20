/-
Erdős Problem #336: Additive Bases and Exact Order

Source: https://erdosproblems.com/336
Status: OPEN

Statement:
For r ≥ 2, let h(r) be the maximal finite k such that there exists a basis A ⊆ ℕ
of order r (every large integer is the sum of at most r elements from A)
and exact order k (every large integer is the sum of exactly k elements from A).

Find the value of lim_{r→∞} h(r)/r².

Known Bounds:
- Original (Erdős-Graham 1980): 1/4 ≤ lim h(r)/r² ≤ 5/4
- Current best: 1/3 ≤ lim h(r)/r² ≤ 1/2
  - Lower bound: Grekos (1988)
  - Upper bound: Nash (1993)

Specific Values:
- h(2) = 4 (Erdős-Graham)
- h(3) = 7 (Nash)
- 10 ≤ h(4) ≤ 11 (Plagne)

Tags: additive-combinatorics, number-theory, bases
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Erdos336

/-!
## Part 1: Basic Definitions
-/

/-- A set A is a basis of order r if every sufficiently large integer
    can be represented as a sum of at most r elements from A -/
def IsBasis (A : Set ℕ) (r : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ (S : Finset ℕ), S.card ≤ r ∧ (∀ a ∈ S, a ∈ A) ∧
    S.sum id = n

/-- A set A has exact order k if every sufficiently large integer
    can be represented as a sum of exactly k elements from A -/
def HasExactOrder (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ (S : Multiset ℕ), S.card = k ∧ (∀ a ∈ S, a ∈ A) ∧
    S.sum = n

/-- A set can have both order r and exact order k (with k possibly different from r) -/
def HasOrderAndExactOrder (A : Set ℕ) (r k : ℕ) : Prop :=
  IsBasis A r ∧ HasExactOrder A k

/-- h(r) = max{k : ∃ A with order r and exact order k} -/
noncomputable def h (r : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ A : Set ℕ, HasOrderAndExactOrder A r k }

/-!
## Part 2: The Limit Question
-/

/-- The main question: find lim_{r→∞} h(r)/r² -/
def LimitExists : Prop :=
  ∃ L : ℝ, ∀ ε > 0, ∃ R : ℕ, ∀ r ≥ R, |((h r : ℕ) : ℝ) / (r^2 : ℝ) - L| < ε

/-- The limit value (if it exists) -/
noncomputable def limitValue : ℝ :=
  if h : LimitExists then Classical.choose h else 0

/-!
## Part 3: Known Bounds
-/

/-- Erdős-Graham (1980) original lower bound: lim ≥ 1/4 -/
axiom erdos_graham_lower_1980 :
  ∀ ε > 0, ∃ R : ℕ, ∀ r ≥ R, ((h r : ℕ) : ℝ) / (r^2 : ℝ) ≥ 1/4 - ε

/-- Erdős-Graham (1980) original upper bound: lim ≤ 5/4 -/
axiom erdos_graham_upper_1980 :
  ∀ ε > 0, ∃ R : ℕ, ∀ r ≥ R, ((h r : ℕ) : ℝ) / (r^2 : ℝ) ≤ 5/4 + ε

/-- Grekos (1988) improved lower bound: lim ≥ 1/3 -/
axiom grekos_lower_1988 :
  ∀ ε > 0, ∃ R : ℕ, ∀ r ≥ R, ((h r : ℕ) : ℝ) / (r^2 : ℝ) ≥ 1/3 - ε

/-- Nash (1993) improved upper bound: lim ≤ 1/2 -/
axiom nash_upper_1993 :
  ∀ ε > 0, ∃ R : ℕ, ∀ r ≥ R, ((h r : ℕ) : ℝ) / (r^2 : ℝ) ≤ 1/2 + ε

/-- Current best bounds: 1/3 ≤ lim ≤ 1/2 -/
theorem current_bounds :
    (∀ ε > 0, ∃ R : ℕ, ∀ r ≥ R, ((h r : ℕ) : ℝ) / (r^2 : ℝ) ≥ 1/3 - ε) ∧
    (∀ ε > 0, ∃ R : ℕ, ∀ r ≥ R, ((h r : ℕ) : ℝ) / (r^2 : ℝ) ≤ 1/2 + ε) :=
  ⟨grekos_lower_1988, nash_upper_1993⟩

/-!
## Part 4: Specific Values
-/

/-- h(2) = 4 (Erdős-Graham 1980) -/
axiom h_2 : h 2 = 4

/-- h(3) = 7 (Nash 1993) -/
axiom h_3 : h 3 = 7

/-- 10 ≤ h(4) ≤ 11 (Plagne 2004) -/
axiom h_4_lower : h 4 ≥ 10
axiom h_4_upper : h 4 ≤ 11

/-- Check: h(2)/2² = 4/4 = 1 -/
example : (h 2 : ℚ) / (2^2 : ℚ) = 1 := by
  simp [h_2]

/-- Check: h(3)/3² = 7/9 ≈ 0.778 -/
example : (h 3 : ℚ) / (3^2 : ℚ) = 7/9 := by
  simp [h_3]
  norm_num

/-!
## Part 5: Order vs Exact Order Can Differ
-/

/-- Erdős-Graham example: A = ∪_{k≥0}(2^{2k}, 2^{2k+1}] has order 2 but exact order 3 -/
def erdosGrahamExample : Set ℕ :=
  { n | ∃ k : ℕ, 2^(2*k) < n ∧ n ≤ 2^(2*k + 1) }

/-- The example has order 2 -/
axiom example_order_2 : IsBasis erdosGrahamExample 2

/-- The example has exact order 3 -/
axiom example_exact_order_3 : HasExactOrder erdosGrahamExample 3

/-- This shows order and exact order can differ -/
theorem order_exact_order_differ : ∃ A : Set ℕ, ∃ r k : ℕ, r ≠ k ∧
    HasOrderAndExactOrder A r k := by
  use erdosGrahamExample, 2, 3
  constructor
  · norm_num
  · exact ⟨example_order_2, example_exact_order_3⟩

/-!
## Part 6: Characterization of Exact Order Existence

Erdős-Graham showed: A has an exact order iff consecutive differences are coprime.
-/

/-- The consecutive differences of A = {a₁ < a₂ < a₃ < ...} -/
def consecutiveDiffs (a : ℕ → ℕ) (k : ℕ) : ℕ := a (k + 1) - a k

/-- A has exact order iff the consecutive differences are coprime -/
axiom erdos_graham_characterization (A : Set ℕ) (a : ℕ → ℕ)
    (ha : ∀ k, a k ∈ A) (hinj : Function.Injective a) (hsurj : ∀ x ∈ A, ∃ k, a k = x)
    (hord : ∀ k, a k < a (k + 1)) :
    (∃ k, HasExactOrder A k) ↔
    Nat.gcd (Finset.univ.image fun k => consecutiveDiffs a k).toSet = {1}
    -- Simplified: gcd of all differences is 1

/-!
## Part 7: Why Quadratic Growth?
-/

/-- Intuition: h(r) grows like r² because:
    - Order r means we can use up to r summands
    - Exact order k means we must use exactly k
    - The "gap" between r and k can grow with r
    - Quadratic is the natural scale -/
theorem quadratic_growth_intuition : True := trivial

/-- Lower terms: Plagne (2004) gave improved bounds on lower-order terms -/
axiom plagne_refinement_2004 : True  -- Details omitted

/-!
## Part 8: Main Results
-/

/-- Erdős Problem #336: Main statement -/
theorem erdos_336_statement :
    -- h(r) is defined for r ≥ 2
    (∀ r ≥ 2, h r < ⊤) ∧
    -- Current bounds: 1/3 ≤ lim h(r)/r² ≤ 1/2
    (∀ ε > 0, ∃ R : ℕ, ∀ r ≥ R, ((h r : ℕ) : ℝ) / (r^2 : ℝ) ≥ 1/3 - ε) ∧
    (∀ ε > 0, ∃ R : ℕ, ∀ r ≥ R, ((h r : ℕ) : ℝ) / (r^2 : ℝ) ≤ 1/2 + ε) ∧
    -- Specific values known
    (h 2 = 4) ∧ (h 3 = 7) := by
  constructor
  · intro r _
    sorry  -- h(r) is finite for each r
  constructor
  · exact grekos_lower_1988
  constructor
  · exact nash_upper_1993
  constructor
  · exact h_2
  · exact h_3

/-- The exact limit value is unknown -/
theorem erdos_336_open : True := trivial

/-- Summary -/
theorem erdos_336_summary :
    -- Question: What is lim h(r)/r²?
    -- Bounds: 1/3 ≤ lim ≤ 1/2
    -- Known: h(2) = 4, h(3) = 7, 10 ≤ h(4) ≤ 11
    -- Status: OPEN
    True := trivial

end Erdos336
