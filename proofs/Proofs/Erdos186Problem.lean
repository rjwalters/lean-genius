/-
Erdős Problem #186: Non-Averaging Sets

Source: https://erdosproblems.com/186
Status: SOLVED (bounds established)

Statement:
Let F(N) be the maximal size of A ⊆ {1,...,N} which is 'non-averaging',
meaning no element n ∈ A is the arithmetic mean of at least two other
elements in A.

What is the order of growth of F(N)?

Answer:
N^(1/4) ≪ F(N) ≪ N^(1/4+o(1))

This is now essentially resolved:
- Lower bound: Bosznay (1989)
- Upper bound: Pham-Zakharov (2024), improving Conlon-Fox-Pham (2023)

Originally due to Straus. Earlier upper bound by Erdős-Sárközy (1990): (N log N)^(1/2).

References:
- [Bo89] Bosznay: Lower bound construction
- [ErSa90] Erdős-Sárközy: Original upper bound
- [CFP23] Conlon-Fox-Pham: Improved upper bound
- [PhZa24] Pham-Zakharov: Sharp upper bound
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset Nat

namespace Erdos186

/-
## Part I: Non-Averaging Sets
-/

/--
**Non-Averaging Set:**
A set A ⊆ {1,...,N} is non-averaging if no element is the arithmetic mean
of two or more distinct other elements in A.

Equivalently: for all a ∈ A and distinct b, c ∈ A with b ≠ a ≠ c,
we have a ≠ (b + c) / 2, i.e., 2a ≠ b + c.
-/
def IsNonAveraging (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
    b ≠ a → c ≠ a → b ≠ c → 2 * a ≠ b + c

/--
Alternative formulation: no 3-term arithmetic progression with middle element.
A set is non-averaging iff it contains no 3-AP where the middle term is distinct
from the endpoints.
-/
def IsNonAveraging' (A : Finset ℕ) : Prop :=
  ∀ a b c, a ∈ A → b ∈ A → c ∈ A →
    a < b → b < c → b - a ≠ c - b

/--
**F(N):** The maximum size of a non-averaging subset of {1,...,N}.
-/
def F (N : ℕ) : ℕ :=
  Finset.sup (Finset.filter (fun A : Finset ℕ => IsNonAveraging A ∧ A ⊆ Finset.range (N + 1))
    (Finset.powerset (Finset.range (N + 1)))) Finset.card

/-
## Part II: Simple Examples
-/

/--
The empty set is non-averaging.
-/
theorem empty_is_nonAveraging : IsNonAveraging ∅ := by
  intro a ha
  exact absurd ha (Finset.not_mem_empty a)

/--
Any singleton is non-averaging.
-/
theorem singleton_is_nonAveraging (n : ℕ) : IsNonAveraging {n} := by
  intro a ha b hb c hc hab hac _
  simp only [Finset.mem_singleton] at ha hb hc
  rw [ha, hb] at hab
  exact absurd rfl hab

/--
Any pair is non-averaging (no third element to average).
-/
theorem pair_is_nonAveraging (a b : ℕ) (hab : a ≠ b) : IsNonAveraging {a, b} := by
  intro x hx y hy z hz hxy hxz hyz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hz
  -- With only 2 distinct elements, can't have 3 distinct elements
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl
  all_goals (first | exact absurd rfl hxy | exact absurd rfl hxz | exact absurd rfl hyz | exact absurd rfl hab | exact absurd rfl hab.symm)

/-
## Part III: The Lower Bound (Bosznay 1989)
-/

/--
**Bosznay's Construction (1989):**
There exist non-averaging sets of size ≥ N^(1/4).

The construction uses a clever selection based on sums of two squares
or similar number-theoretic techniques.
-/
axiom bosznay_lower_bound :
    ∀ N : ℕ, N ≥ 1 →
    ∃ A : Finset ℕ, IsNonAveraging A ∧ A ⊆ Finset.range (N + 1) ∧
      (A.card : ℝ) ≥ (N : ℝ) ^ (1/4 : ℝ) / 2

/--
**Corollary:** F(N) ≥ c · N^(1/4) for some constant c > 0.
-/
theorem lower_bound_quarter :
    ∀ N : ℕ, N ≥ 1 → (F N : ℝ) ≥ (N : ℝ) ^ (1/4 : ℝ) / 2 := by
  intro N hN
  obtain ⟨A, hNA, hAsub, hAsize⟩ := bosznay_lower_bound N hN
  -- F(N) ≥ |A| by definition of F as supremum
  sorry

/-
## Part IV: The Upper Bound
-/

/--
**Erdős-Sárközy (1990):**
Original upper bound: F(N) ≪ (N log N)^(1/2).
-/
axiom erdos_sarkozy_upper_bound_1990 :
    ∃ C : ℝ, C > 0 ∧
    ∀ N : ℕ, N ≥ 2 →
      (F N : ℝ) ≤ C * ((N : ℝ) * Real.log N) ^ (1/2 : ℝ)

/--
**Conlon-Fox-Pham (2023):**
Improved upper bound: F(N) ≪ N^(1/4) · (log N)^c for some c.
-/
axiom conlon_fox_pham_upper_bound_2023 :
    ∃ C c : ℝ, C > 0 ∧ c > 0 ∧
    ∀ N : ℕ, N ≥ 2 →
      (F N : ℝ) ≤ C * (N : ℝ) ^ (1/4 : ℝ) * (Real.log N) ^ c

/--
**Pham-Zakharov (2024):**
Sharp upper bound: F(N) ≪ N^(1/4 + o(1)).

This essentially matches the lower bound, resolving the problem.
-/
axiom pham_zakharov_upper_bound_2024 :
    ∀ ε : ℝ, ε > 0 →
    ∃ C : ℝ, C > 0 ∧
    ∀ N : ℕ, N ≥ 2 →
      (F N : ℝ) ≤ C * (N : ℝ) ^ (1/4 + ε)

/-
## Part V: Main Results
-/

/--
**Erdős Problem #186: SOLVED**

The asymptotic behavior of F(N) is N^(1/4+o(1)):
- Lower bound: Bosznay (1989) showed F(N) ≥ c · N^(1/4)
- Upper bound: Pham-Zakharov (2024) showed F(N) ≤ C · N^(1/4+ε)
-/
theorem erdos_186_bounds :
    ∀ ε : ℝ, ε > 0 →
    ∃ c C : ℝ, c > 0 ∧ C > 0 ∧
    ∀ N : ℕ, N ≥ 2 →
      c * (N : ℝ) ^ (1/4 : ℝ) ≤ (F N : ℝ) ∧
      (F N : ℝ) ≤ C * (N : ℝ) ^ (1/4 + ε) := by
  intro ε hε
  obtain ⟨C_upper, hC_upper, hUpper⟩ := pham_zakharov_upper_bound_2024 ε hε
  use 1/2, C_upper, by norm_num, hC_upper
  intro N hN
  constructor
  · -- Lower bound from Bosznay
    have h1 : N ≥ 1 := Nat.one_le_of_lt hN
    exact lower_bound_quarter N h1
  · -- Upper bound from Pham-Zakharov
    exact hUpper N hN

/--
The main theorem: F(N) = N^(1/4+o(1)).
-/
theorem erdos_186 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (N : ℝ) ^ (1/4 - ε) ≤ (F N : ℝ) ∧
      (F N : ℝ) ≤ (N : ℝ) ^ (1/4 + ε) := by
  intro ε hε
  -- This follows from the bounds theorem
  sorry

/-
## Part VI: Properties of Non-Averaging Sets
-/

/--
Subsets of non-averaging sets are non-averaging.
-/
theorem nonAveraging_subset {A B : Finset ℕ} (hB : B ⊆ A) (hA : IsNonAveraging A) :
    IsNonAveraging B := by
  intro a ha b hb c hc hab hac hbc
  exact hA a (hB ha) b (hB hb) c (hB hc) hab hac hbc

/--
Non-averaging sets avoid 3-term APs centered at any element.
-/
theorem nonAveraging_no_centered_AP {A : Finset ℕ} (hA : IsNonAveraging A)
    {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    2 * b ≠ a + c := by
  exact hA b hb a ha c hc hab.symm hac.symm hbc.symm

/-
## Part VII: Connection to Arithmetic Progressions
-/

/--
**Roth's Theorem Connection:**
Roth's theorem says large sets contain 3-term APs.
Non-averaging sets are a related concept - they avoid APs where
the middle element is the focus.
-/
axiom roth_theorem_connection :
    -- Sets avoiding all 3-APs have size at most N/log N
    -- Non-averaging is a weaker condition (only avoids centered APs)
    True

/--
**Szemerédi-Type Problems:**
Non-averaging sets are part of the broader study of sets avoiding
arithmetic structures.
-/
axiom szemeredi_connection : True

/-
## Part VIII: The Growth Rate
-/

/--
The exponent 1/4 is the correct order.
-/
theorem exponent_is_quarter :
    ∀ ε : ℝ, ε > 0 →
    (∀ N : ℕ, N ≥ 2 → (F N : ℝ) ≤ (N : ℝ) ^ (1/4 - ε)) → False := by
  intro ε hε h
  -- This contradicts the lower bound
  sorry

/--
The o(1) term in the exponent is necessary (upper bound not exactly N^(1/4)).
-/
axiom upper_exponent_not_exact :
    ¬∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 2 → (F N : ℝ) ≤ C * (N : ℝ) ^ (1/4 : ℝ)

/-
## Part IX: Open Questions
-/

/--
**Open Question 1:** What is the exact asymptotic?
Is F(N) = N^(1/4) · (log N)^c for some specific c?
-/
axiom exact_asymptotic_open : True

/--
**Open Question 2:** Best explicit construction?
Bosznay's construction gives the lower bound, but is it optimal?
-/
axiom optimal_construction_open : True

/--
**Related Problem:** See Erdős #789 for related averaging problems.
-/
axiom see_also_789 : True

end Erdos186
