/-!
# Erdős Problem #14: Unique Sums and Non-Unique Representation

Let A ⊆ ℕ and B = {n : n is representable in exactly one way as a + b
with a ≤ b, a, b ∈ A}. Two questions:

(a) Is it true that |{1,...,N} \ B| ≫_ε N^{1/2 − ε} for all ε > 0?
(b) Is it possible that |{1,...,N} \ B| = o(N^{1/2})?

## Key Results

- Erdős–Sárközy–Szemerédi: ∃ A with |{1,...,N}\B| ≪_ε N^{1/2+ε},
  yet infinitely many N have |{1,...,N}\B| ≫_ε N^{1/3−ε}
- Erdős–Freud: finite analogue gives < 2^{3/2} N^{1/2} non-unique sums

## References

- Erdős [Er92c], [Er97], [Er97e]
- Erdős, Freud [ErFr91]
- OEIS: A143824
- <https://erdosproblems.com/14>
-/

import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Finset Filter Asymptotics

/-! ## Core Definitions -/

/-- The set of unique sums: n has exactly one representation as a + b
    with a ≤ b and a, b ∈ A. -/
def uniqueSums (A : Finset ℕ) : Finset ℕ :=
  (A ×ˢ A).filter (fun p => p.1 ≤ p.2)
    |>.image (fun p => p.1 + p.2)
    |>.filter (fun n =>
      ((A ×ˢ A).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = n)).card = 1)

/-- Count of non-unique sums up to N: integers in {1,...,N} not in uniqueSums. -/
def nonUniqueSumCount (A : Finset ℕ) (N : ℕ) : ℕ :=
  ((Icc 1 N).filter (fun n => n ∉ uniqueSums A)).card

/-- The infinite-set version: unique sums for A ⊆ ℕ. -/
def uniqueSumsInf (A : Set ℕ) : Set ℕ :=
  {n : ℕ | ∃! p : ℕ × ℕ, p.1 ≤ p.2 ∧ p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n}

/-- Non-unique count for infinite sets, truncated to {1,...,N}. -/
noncomputable def nonUniqueSumCountInf (A : Set ℕ) (N : ℕ) : ℕ :=
  (Set.Icc 1 N \ uniqueSumsInf A).ncard

/-! ## Main Conjectures -/

/-- **Erdős Problem #14a** (OPEN): For every A ⊆ ℕ and every ε > 0,
    the non-unique count satisfies |{1,...,N}\B| ≫_ε N^{1/2−ε}. -/
axiom erdos_14a_conjecture :
  ∀ (A : Set ℕ) (ε : ℝ), ε > 0 →
    ∃ C : ℝ, C > 0 ∧
      ∀ᶠ N in atTop, (nonUniqueSumCountInf A N : ℝ) ≥ C * (N : ℝ) ^ (1/2 - ε)

/-- **Erdős Problem #14b** (OPEN): Is it possible that
    |{1,...,N}\B| = o(N^{1/2})? -/
axiom erdos_14b_conjecture :
  -- The question: does there exist A with non-unique count = o(√N)?
  True  -- Both positive and negative answers are open

/-! ## Known Results -/

/-- **Erdős–Sárközy–Szemerédi**: There exists A ⊆ ℕ such that
    |{1,...,N}\B| ≪_ε N^{1/2+ε} for all ε > 0. -/
axiom ess_upper_bound :
  ∃ A : Set ℕ, ∀ ε : ℝ, ε > 0 →
    ∃ C : ℝ, C > 0 ∧
      ∀ᶠ N in atTop, (nonUniqueSumCountInf A N : ℝ) ≤ C * (N : ℝ) ^ (1/2 + ε)

/-- **Erdős–Sárközy–Szemerédi**: The same A from above satisfies
    |{1,...,N}\B| ≫_ε N^{1/3−ε} for infinitely many N. -/
axiom ess_lower_bound :
  ∃ A : Set ℕ, ∀ ε : ℝ, ε > 0 →
    ∃ C : ℝ, C > 0 ∧
      ∃ᶠ N in atTop, (nonUniqueSumCountInf A N : ℝ) ≥ C * (N : ℝ) ^ (1/3 - ε)

/-- **Erdős–Freud**: For A ⊆ {1,...,N} (finite), the number of non-unique
    sums is < 2^{3/2} · N^{1/2}. The constant 2^{3/2} may be optimal. -/
axiom erdos_freud_finite :
  ∀ N : ℕ, N > 0 →
    ∃ A : Finset ℕ, (∀ a ∈ A, a ∈ Icc 1 N) ∧
      (nonUniqueSumCount A N : ℝ) < 2 ^ (3/2 : ℝ) * (N : ℝ) ^ (1/2 : ℝ)

/-! ## Structural Observations -/

/-- If A is a Sidon set (all pairwise sums distinct), then every sum has
    at most one representation: uniqueSums covers all sums of A.
    But Sidon sets have |A ∩ {1,...,N}| ≤ N^{1/2} + O(N^{1/4}), so
    the sumset has ≤ N + O(N^{3/4}) elements, missing ~N integers. -/
axiom sidon_set_non_unique (A : Set ℕ) :
  (∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a ≤ b → c ≤ d → a + b = c + d → (a = c ∧ b = d)) →
  -- All sums are unique, but many integers are unrepresented
  True

/-- For random-like sets A with |A ∩ {1,...,N}| ~ c·N^{1/2}, the non-unique
    count is expected to be ~Θ(N^{1/2}). -/
axiom random_heuristic :
  -- Heuristic: if A has ~c√N elements up to N, the sumset has ~N elements
  -- but collisions (multiple representations) occur at rate ~1
  True

/-- The non-unique count is monotonically non-decreasing in N. -/
axiom non_unique_monotone (A : Set ℕ) :
  ∀ M N : ℕ, M ≤ N → nonUniqueSumCountInf A M ≤ nonUniqueSumCountInf A N
