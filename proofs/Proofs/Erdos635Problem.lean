/-
Erdős Problem #635: Non-Divisibility Condition on Differences

Source: https://erdosproblems.com/635
Status: OPEN

Statement:
For t ≥ 1 and A ⊆ {1,...,N}, suppose that whenever a, b ∈ A with
b - a ≥ t, we have (b - a) ∤ b. How large can |A| be?

Is it true that |A| ≤ (1/2 + o_t(1)) · N?

Known:
- For t = 1, the maximum is ⌊(N+1)/2⌋ (all odd numbers)
- For t = 2, Erdős showed |A| ≥ N/2 + c·log(N) for some c > 0

References: [Gu83], [Ru99], Erdős letter to Ruzsa (~1980)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Nat Finset

namespace Erdos635

/-! ## Part I: The Non-Divisibility Condition -/

/-- A set A ⊆ {1,...,N} satisfies the t-non-divisibility condition
    if whenever a, b ∈ A with b - a ≥ t, then (b - a) does not divide b. -/
def IsNonDivisible (A : Finset ℕ) (t : ℕ) : Prop :=
  ∀ a b, a ∈ A → b ∈ A → a < b → b - a ≥ t → ¬(b - a ∣ b)

/-- A t-admissible set in {1,...,N}. -/
def IsAdmissible (A : Finset ℕ) (N t : ℕ) : Prop :=
  (∀ x ∈ A, 1 ≤ x ∧ x ≤ N) ∧ IsNonDivisible A t

/-! ## Part II: The Extremal Function -/

/-- f(N, t) = the maximum size of a t-admissible set in {1,...,N}. -/
noncomputable def f (N t : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A.card = k ∧ IsAdmissible A N t}

/-! ## Part III: The Case t = 1 -/

/-- The odd numbers in {1,...,N}. -/
def oddSet (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => n % 2 = 1)

/-- The odd set is 1-admissible: if b - a ≥ 1 and b is odd,
    then b - a is even, so (b-a) ∤ b since b is odd. -/
axiom oddSet_admissible (N : ℕ) (hN : N ≥ 1) :
    IsAdmissible (oddSet N) N 1

/-- The odd set has size ⌊(N+1)/2⌋. -/
axiom oddSet_card (N : ℕ) : (oddSet N).card = (N + 1) / 2

/-- For t = 1, the maximum is exactly ⌊(N+1)/2⌋. -/
axiom f_t1 (N : ℕ) (hN : N ≥ 1) : f N 1 = (N + 1) / 2

/-! ## Part IV: The Case t = 2 -/

/-- For t = 2, one can do slightly better than N/2. -/
axiom f_t2_lower (N : ℕ) (hN : N ≥ 2) :
    ∃ c : ℝ, c > 0 ∧ (f N 2 : ℝ) ≥ N / 2 + c * Real.log N

/-- The construction: odd numbers plus certain powers of 2. -/
axiom erdos_construction_t2 (N : ℕ) (hN : N ≥ 2) :
    ∃ A : Finset ℕ, IsAdmissible A N 2 ∧
    ∃ c : ℝ, c > 0 ∧ (A.card : ℝ) ≥ N / 2 + c * Real.log N

/-! ## Part V: The Main Conjecture -/

/--
**Erdős Problem #635 (OPEN):**
For any fixed t, |A| ≤ (1/2 + o_t(1)) · N.

Formally: for every ε > 0 and every t ≥ 1, there exists N₀ such that
for all N ≥ N₀, f(N, t) ≤ (1/2 + ε) · N.
-/
def ErdosConjecture635 : Prop :=
  ∀ ε : ℝ, ε > 0 → ∀ t : ℕ, t ≥ 1 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (f N t : ℝ) ≤ (1 / 2 + ε) * N

/-- The conjecture is axiomatized. -/
axiom erdos_635 : ErdosConjecture635

/-! ## Part VI: Upper Bound -/

/-- Trivial upper bound: f(N, t) ≤ N for all t. -/
axiom f_upper_trivial (N t : ℕ) : f N t ≤ N

/-- The density is at most 1/2 + o(1) for t = 1. -/
axiom f_t1_density :
    Filter.Tendsto (fun N => (f N 1 : ℝ) / N) Filter.atTop (nhds (1 / 2))

/-! ## Part VII: Summary -/

/--
**Erdős Problem #635: Summary**

PROBLEM: For A ⊆ {1,...,N} with b - a ≥ t ⟹ (b-a) ∤ b,
is |A| ≤ (1/2 + o_t(1)) · N?

STATUS: OPEN

KNOWN:
- t = 1: maximum is ⌊(N+1)/2⌋ (all odd numbers)
- t = 2: |A| ≥ N/2 + c·log(N) (Erdős construction)
- Conjecture: density approaches 1/2 for all t
-/
theorem erdos_635_t1_solved (N : ℕ) (hN : N ≥ 1) :
    f N 1 = (N + 1) / 2 := f_t1 N hN

/-- The problem remains OPEN. -/
theorem erdos_635_status : True := trivial

end Erdos635
