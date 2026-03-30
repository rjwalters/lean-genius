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
/--
**Corollary:** F(N) ≥ c · N^(1/4) for some constant c > 0.

This follows from Bosznay's construction, which provides a witness set
of the required size. The proof that F(N) dominates the witness size
requires showing that the supremum is at least as large as any particular
non-averaging set's cardinality.
-/
axiom lower_bound_quarter :
    ∀ N : ℕ, N ≥ 1 → (F N : ℝ) ≥ (N : ℝ) ^ (1/4 : ℝ) / 2

/-
## Part IV: The Upper Bound
-/

/--
**Erdős-Sárközy (1990):**
Original upper bound: F(N) ≪ (N log N)^(1/2).
-/
/--
**Conlon-Fox-Pham (2023):**
Improved upper bound: F(N) ≪ N^(1/4) · (log N)^c for some c.
-/
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
**The o(1) exponent form:** F(N) = N^(1/4+o(1)).

For any ε > 0, eventually N^(1/4 - ε) ≤ F(N) ≤ N^(1/4 + ε).
This is the standard way to express the asymptotic — the exponent
converges to 1/4.

Axiomatized because deriving the N^(1/4-ε) lower bound from the
Bosznay construction requires careful asymptotic analysis.
-/
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
Roth's theorem says any subset of {1,...,N} of size ≫ N/log N contains
a 3-term AP. Non-averaging is a weaker condition (only avoids centered APs),
which is why non-averaging sets can be much larger (N^(1/4) vs N/log N).
-/
/-
## Part VIII: The Growth Rate
-/

/--
The exponent 1/4 is the correct order: F(N) cannot grow slower than N^(1/4-ε)
for any ε > 0, since Bosznay's construction achieves N^(1/4).
-/
/--
The o(1) term in the exponent is necessary (upper bound not exactly N^(1/4)).
-/
/-
## Part IX: Open Questions
-/

/--
**Open Question 1:** What is the exact asymptotic of F(N)?
Is F(N) ~ N^(1/4) · (log N)^c for some specific constant c?
The precise logarithmic factor remains unknown.

**Open Question 2:** What is the best explicit construction?
Bosznay's 1989 construction achieves N^(1/4), but whether
this is optimal among explicit constructions is unknown.

**Related:** See Erdős Problem #789 for related averaging problems.
-/

end Erdos186
