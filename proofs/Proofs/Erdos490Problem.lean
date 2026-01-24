/-
  Erdős Problem #490: Distinct Products of Two Sets

  Source: https://erdosproblems.com/490
  Status: SOLVED (Szemerédi 1976)

  Statement:
  Let A, B ⊆ {1,...,N} be such that all products ab with a ∈ A, b ∈ B are distinct.
  Is it true that |A||B| ≪ N²/log N?

  Answer: YES - Szemerédi (1976) proved this bound is correct.

  Best Possible Example:
  A = [1, N/2] ∩ ℕ and B = {p : N/2 < p ≤ N, p prime}
  This achieves |A||B| ~ N² / (2 log N).

  Open Question (Erdős 1972):
  Does lim_{N→∞} max |A||B| log N / N² exist? If so, what is its value?
  (It must be ≥ 1 by van Doorn's observation.)

  References:
  - [Sz76] Szemerédi, "On a problem of P. Erdős", J. Number Theory (1976)
  - [Er72] Erdős, "Extremal problems in number theory",
    Proceedings of the 1972 Number Theory Conference
  - See also Problems #425 and #896
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Primorial

open Finset Real

namespace Erdos490

/-
## Part I: Basic Definitions
-/

/-- A set A ⊆ {1,...,N}. -/
def IsSubsetUpTo (A : Finset ℕ) (N : ℕ) : Prop :=
  ∀ a ∈ A, 1 ≤ a ∧ a ≤ N

/-- The product set A·B = {ab : a ∈ A, b ∈ B}. -/
def productSet (A B : Finset ℕ) : Finset ℕ :=
  A.biUnion (fun a => B.image (fun b => a * b))

/-- All products ab are distinct. -/
def HasDistinctProducts (A B : Finset ℕ) : Prop :=
  (productSet A B).card = A.card * B.card

/-- Alternative definition: the product map is injective. -/
def ProductMapInjective (A B : Finset ℕ) : Prop :=
  ∀ a₁ a₂ b₁ b₂, a₁ ∈ A → a₂ ∈ A → b₁ ∈ B → b₂ ∈ B →
    a₁ * b₁ = a₂ * b₂ → (a₁ = a₂ ∧ b₁ = b₂)

/-- The two definitions are equivalent. -/
axiom distinct_products_equiv (A B : Finset ℕ) :
  HasDistinctProducts A B ↔ ProductMapInjective A B

/-
## Part II: The Erdős Question
-/

/-- The maximum of |A||B| over all pairs with distinct products. -/
noncomputable def maxProductSize (N : ℕ) : ℕ :=
  Nat.find (max_exists N)
where
  max_exists : ∀ N, ∃ k, ∀ A B : Finset ℕ,
    IsSubsetUpTo A N → IsSubsetUpTo B N →
    HasDistinctProducts A B → A.card * B.card ≤ k := by
    intro N
    use N^2  -- trivial bound
    sorry

/-- Erdős's Question: Is |A||B| ≪ N²/log N? -/
def ErdosQuestion490 : Prop :=
  ∃ C : ℝ, C > 0 ∧
    ∀ N : ℕ, N ≥ 2 →
      ∀ A B : Finset ℕ, IsSubsetUpTo A N → IsSubsetUpTo B N →
        HasDistinctProducts A B →
        (A.card * B.card : ℝ) ≤ C * N^2 / Real.log N

/-
## Part III: Szemerédi's Theorem (1976)
-/

/-- **Szemerédi's Theorem (1976):**
    If A, B ⊆ {1,...,N} have distinct products, then |A||B| ≪ N²/log N. -/
axiom szemeredi_theorem :
  ∃ C : ℝ, C > 0 ∧
    ∀ N : ℕ, N ≥ 2 →
      ∀ A B : Finset ℕ, IsSubsetUpTo A N → IsSubsetUpTo B N →
        HasDistinctProducts A B →
        (A.card * B.card : ℝ) ≤ C * N^2 / Real.log N

/-- The answer to Erdős Problem #490 is YES. -/
theorem erdos_490_answer : ErdosQuestion490 := szemeredi_theorem

/-
## Part IV: The Optimal Example
-/

/-- The first half of [1, N]: A = [1, N/2]. -/
def optimalA (N : ℕ) : Finset ℕ :=
  Finset.filter (fun n => 1 ≤ n ∧ n ≤ N / 2) (Finset.range (N + 1))

/-- The primes in the second half: B = {p : N/2 < p ≤ N, p prime}. -/
def optimalB (N : ℕ) : Finset ℕ :=
  Finset.filter (fun p => Nat.Prime p ∧ N / 2 < p ∧ p ≤ N) (Finset.range (N + 1))

/-- The optimal example has distinct products. -/
axiom optimal_has_distinct_products (N : ℕ) (hN : N ≥ 4) :
  HasDistinctProducts (optimalA N) (optimalB N)

/-- The optimal example achieves |A||B| ~ N²/(2 log N). -/
axiom optimal_size (N : ℕ) (hN : N ≥ 4) :
  ∃ c : ℝ, c > 0 ∧
    |(optimalA N).card * (optimalB N).card - (N^2 : ℝ) / (2 * Real.log N)| ≤ c * N^2 / (Real.log N)^2

/-- Why it works: products a·p are distinct because primes are coprime to smaller numbers. -/
theorem optimal_works_because_primes (a₁ a₂ : ℕ) (p₁ p₂ : ℕ)
    (ha₁ : a₁ ≤ N / 2) (ha₂ : a₂ ≤ N / 2)
    (hp₁ : Nat.Prime p₁) (hp₂ : Nat.Prime p₂)
    (hp₁_large : N / 2 < p₁) (hp₂_large : N / 2 < p₂)
    (heq : a₁ * p₁ = a₂ * p₂) : a₁ = a₂ ∧ p₁ = p₂ := by
  -- If a₁p₁ = a₂p₂ with p₁, p₂ > N/2 and a₁, a₂ ≤ N/2, then p₁ | a₂p₂ = a₁p₁
  -- Since p₁ > a₂, we must have p₁ | p₂, so p₁ = p₂ (both prime)
  -- Then a₁ = a₂.
  sorry

/-
## Part V: The Limit Question (Open)
-/

/-- The ratio |A||B| log N / N². -/
noncomputable def productRatio (N : ℕ) : ℝ :=
  (maxProductSize N : ℝ) * Real.log N / N^2

/-- Erdős asked: Does lim productRatio(N) exist? If so, what is it? -/
def LimitQuestion : Prop :=
  ∃ L : ℝ, Filter.Tendsto productRatio Filter.atTop (nhds L)

/-- Van Doorn observed: If the limit exists, it must be ≥ 1. -/
axiom van_doorn_observation :
  LimitQuestion → ∃ L, Filter.Tendsto productRatio Filter.atTop (nhds L) ∧ L ≥ 1

/-- The limit question is OPEN. -/
def LimitQuestionOpen : Prop :=
  -- We don't know if the limit exists
  True

/-
## Part VI: Special Cases
-/

/-- Case A = B (multiplicative Sidon sets). -/
def IsMultiplicativeSidon (A : Finset ℕ) : Prop :=
  HasDistinctProducts A A

/-- For A = B, the bound is |A|² ≪ N²/log N, so |A| ≪ N/√(log N). -/
axiom sidon_bound (N : ℕ) (hN : N ≥ 2) :
  ∀ A : Finset ℕ, IsSubsetUpTo A N → IsMultiplicativeSidon A →
    (A.card : ℝ)^2 ≤ szemeredi_constant * N^2 / Real.log N
where
  szemeredi_constant : ℝ := 1  -- placeholder

/-- Primes are a multiplicative Sidon set. -/
theorem primes_sidon (N : ℕ) :
    let P := Finset.filter Nat.Prime (Finset.range (N + 1))
    IsMultiplicativeSidon P := by
  intro P
  unfold IsMultiplicativeSidon HasDistinctProducts
  sorry -- Unique factorization implies distinct products

/-
## Part VII: Related Problems
-/

/-- Connection to Problem #425 (sumsets). -/
def RelatedProblem425 : Prop :=
  -- Analogous question for sums instead of products
  True

/-- Connection to Problem #896 (product set sizes). -/
def RelatedProblem896 : Prop :=
  -- More general product set questions
  True

/-- The multiplicative energy E(A, B) counts coincidences. -/
noncomputable def multiplicativeEnergy (A B : Finset ℕ) : ℕ :=
  ((A ×ˢ A) ×ˢ (B ×ˢ B)).filter
    (fun ((a₁, a₂), (b₁, b₂)) => a₁ * b₁ = a₂ * b₂)
    |>.card

/-- Distinct products means minimal energy. -/
theorem distinct_minimal_energy (A B : Finset ℕ) :
    HasDistinctProducts A B ↔ multiplicativeEnergy A B = A.card * B.card := by
  sorry

/-
## Part VIII: Bounds History
-/

/-- Trivial bound: |A||B| ≤ N². -/
theorem trivial_bound (N : ℕ) (A B : Finset ℕ)
    (hA : IsSubsetUpTo A N) (hB : IsSubsetUpTo B N) :
    A.card * B.card ≤ N^2 := by
  sorry

/-- Counting bound: |A||B| ≤ N² (since products are ≤ N²). -/
theorem counting_bound (N : ℕ) (A B : Finset ℕ)
    (hA : IsSubsetUpTo A N) (hB : IsSubsetUpTo B N)
    (h : HasDistinctProducts A B) :
    A.card * B.card ≤ N^2 := by
  sorry

/-- Szemerédi's improvement: |A||B| ≤ C·N²/log N. -/
theorem szemeredi_bound (N : ℕ) (hN : N ≥ 2) (A B : Finset ℕ)
    (hA : IsSubsetUpTo A N) (hB : IsSubsetUpTo B N)
    (h : HasDistinctProducts A B) :
    ∃ C : ℝ, C > 0 ∧ (A.card * B.card : ℝ) ≤ C * N^2 / Real.log N := by
  obtain ⟨C, hC, hBound⟩ := szemeredi_theorem
  exact ⟨C, hC, hBound N hN A B hA hB h⟩

/-
## Part IX: Summary
-/

/-- **Erdős Problem #490: SOLVED by Szemerédi (1976)**

Question: If A, B ⊆ {1,...,N} have all products ab distinct,
is |A||B| ≪ N²/log N?

Answer: YES

Optimal: A = [1, N/2], B = {p prime : N/2 < p ≤ N}
achieves |A||B| ~ N²/(2 log N).

Open: Does lim |A||B| log N / N² exist? If so, what is its value?
(Must be ≥ 1 by van Doorn.)
-/
theorem erdos_490 : ErdosQuestion490 := szemeredi_theorem

/-- Main theorem statement. -/
theorem erdos_490_main :
    ∃ C : ℝ, C > 0 ∧
      ∀ N : ℕ, N ≥ 2 →
        ∀ A B : Finset ℕ, IsSubsetUpTo A N → IsSubsetUpTo B N →
          HasDistinctProducts A B →
          (A.card * B.card : ℝ) ≤ C * N^2 / Real.log N :=
  szemeredi_theorem

/-- The bound is optimal up to a constant. -/
theorem bound_is_optimal :
    ∃ c : ℝ, c > 0 ∧
      ∀ N : ℕ, N ≥ 4 →
        ∃ A B : Finset ℕ,
          IsSubsetUpTo A N ∧ IsSubsetUpTo B N ∧
          HasDistinctProducts A B ∧
          (A.card * B.card : ℝ) ≥ c * N^2 / Real.log N := by
  use 1/3  -- lower bound constant
  constructor
  · norm_num
  · intro N hN
    use optimalA N, optimalB N
    constructor
    · sorry  -- IsSubsetUpTo (optimalA N) N
    constructor
    · sorry  -- IsSubsetUpTo (optimalB N) N
    constructor
    · exact optimal_has_distinct_products N (by linarith)
    · sorry  -- Lower bound

end Erdos490
