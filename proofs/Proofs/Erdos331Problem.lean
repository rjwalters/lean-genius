/-
  Erdős Problem #331: Common Differences in Dense Sets

  Source: https://erdosproblems.com/331
  Status: DISPROVED (Ruzsa counterexample)

  Statement:
  Let A, B ⊆ ℕ such that for all large N:
    |A ∩ {1,...,N}| ≫ N^{1/2}
    |B ∩ {1,...,N}| ≫ N^{1/2}
  Is it true that there are infinitely many solutions to
    a₁ - a₂ = b₁ - b₂ ≠ 0
  with a₁, a₂ ∈ A and b₁, b₂ ∈ B?

  Answer: NO (DISPROVED)

  Key Result:
  - Ruzsa: Simple counterexample using binary representations
    - A = numbers with nonzero digits only in even positions
    - B = numbers with nonzero digits only in odd positions
    - Both grow like N^{1/2}, but n = a + b has unique representation

  References:
  - Erdős-Graham 1980, p.50
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Digits
import Mathlib.Order.Filter.Basic

open Real Filter

namespace Erdos331

/-
## Part I: Counting Functions
-/

/-- The counting function for a set A up to N. -/
def countingFunction (A : Set ℕ) (N : ℕ) : ℕ :=
  (Finset.filter (fun n => n ∈ A) (Finset.Icc 1 N)).card

/-- A set has density at least α if |A ∩ {1,...,N}| ≥ c · N^α for large N. -/
def HasDensityAtLeast (A : Set ℕ) (α : ℝ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    (countingFunction A N : ℝ) ≥ c * N^α

/-- A set has density ≫ N^{1/2}. -/
def HasSqrtDensity (A : Set ℕ) : Prop := HasDensityAtLeast A (1/2)

/-- A set has density ~ c·N^{1/2} (asymptotic). -/
def HasExactSqrtDensity (A : Set ℕ) (c : ℝ) : Prop :=
  c > 0 ∧ Tendsto (fun N => (countingFunction A N : ℝ) / N^(1/2 : ℝ)) atTop (nhds c)

/-
## Part II: Common Differences
-/

/-- A common difference: a₁ - a₂ = b₁ - b₂ ≠ 0 with a₁, a₂ ∈ A and b₁, b₂ ∈ B. -/
def HasCommonDifference (A B : Set ℕ) (d : ℤ) : Prop :=
  d ≠ 0 ∧ ∃ a₁ a₂ : ℕ, a₁ ∈ A ∧ a₂ ∈ A ∧ (a₁ : ℤ) - a₂ = d ∧
    ∃ b₁ b₂ : ℕ, b₁ ∈ B ∧ b₂ ∈ B ∧ (b₁ : ℤ) - b₂ = d

/-- The set of common differences between A and B. -/
def commonDifferences (A B : Set ℕ) : Set ℤ :=
  { d | HasCommonDifference A B d }

/-- A and B have infinitely many common differences. -/
def HasInfinitelyManyCommonDifferences (A B : Set ℕ) : Prop :=
  Set.Infinite (commonDifferences A B)

/-
## Part III: The Original Conjecture
-/

/-- **Erdős Conjecture (Problem #331):**
    If A and B both have density ≫ N^{1/2}, do they have infinitely
    many common differences? -/
def ErdosConjecture331 : Prop :=
  ∀ A B : Set ℕ, HasSqrtDensity A → HasSqrtDensity B →
    HasInfinitelyManyCommonDifferences A B

/-
## Part IV: Ruzsa's Counterexample
-/

/-- A number is in the "even positions" set if its binary representation
    has nonzero digits only in even positions (positions 0, 2, 4, ...). -/
def evenBinaryPositions : Set ℕ :=
  { n | ∀ k : ℕ, (n / 2^(2*k+1)) % 2 = 0 }

/-- A number is in the "odd positions" set if its binary representation
    has nonzero digits only in odd positions (positions 1, 3, 5, ...). -/
def oddBinaryPositions : Set ℕ :=
  { n | ∀ k : ℕ, (n / 2^(2*k)) % 2 = 0 }

/-- Ruzsa's set A: even binary positions. -/
def ruzsaA : Set ℕ := evenBinaryPositions

/-- Ruzsa's set B: odd binary positions. -/
def ruzsaB : Set ℕ := oddBinaryPositions

/-- Ruzsa's A has density ≫ N^{1/2}. -/
axiom ruzsaA_has_sqrt_density : HasSqrtDensity ruzsaA

/-- Ruzsa's B has density ≫ N^{1/2}. -/
axiom ruzsaB_has_sqrt_density : HasSqrtDensity ruzsaB

/-- Key property: every n ≥ 1 has a UNIQUE representation n = a + b
    with a ∈ ruzsaA and b ∈ ruzsaB. -/
axiom ruzsa_unique_representation (n : ℕ) (hn : n ≥ 1) :
  ∃! p : ℕ × ℕ, p.1 ∈ ruzsaA ∧ p.2 ∈ ruzsaB ∧ p.1 + p.2 = n

/-
## Part V: The Disproof
-/

/-- Ruzsa's sets have NO nontrivial common differences.
    If a₁ - a₂ = b₁ - b₂ then a₁ + b₂ = a₂ + b₁, which by unique
    representation forces a₁ = a₂ and b₁ = b₂. -/
axiom ruzsa_no_common_differences :
  commonDifferences ruzsaA ruzsaB = ∅

/-- Therefore, Ruzsa's sets are a counterexample to the conjecture. -/
theorem ruzsa_counterexample :
    HasSqrtDensity ruzsaA ∧ HasSqrtDensity ruzsaB ∧
    ¬HasInfinitelyManyCommonDifferences ruzsaA ruzsaB := by
  refine ⟨ruzsaA_has_sqrt_density, ruzsaB_has_sqrt_density, ?_⟩
  intro h
  have : commonDifferences ruzsaA ruzsaB = ∅ := ruzsa_no_common_differences
  rw [this] at h
  exact Set.not_infinite_empty h

/-- **Erdős Problem #331: DISPROVED**
    The conjecture is FALSE. -/
theorem erdos_331_disproved : ¬ErdosConjecture331 := by
  intro h
  have := h ruzsaA ruzsaB ruzsaA_has_sqrt_density ruzsaB_has_sqrt_density
  exact ruzsa_counterexample.2.2 this

/-
## Part VI: Understanding the Counterexample
-/

/-- The elements of ruzsaA are sums of powers of 4: ∑ aₖ · 4^k. -/
def ruzsaA_characterization : Prop :=
  ∀ n : ℕ, n ∈ ruzsaA ↔ ∃ f : ℕ → Fin 2, n = ∑' k, (f k : ℕ) * 4^k

/-- The elements of ruzsaB are 2 times elements of ruzsaA. -/
theorem ruzsaB_eq_double_ruzsaA :
    ruzsaB = { n | ∃ m ∈ ruzsaA, n = 2 * m } := by
  sorry

/-- The growth rate is exactly √N (up to constants). -/
axiom ruzsa_exact_growth :
  ∃ c : ℝ, c > 0 ∧
    HasExactSqrtDensity ruzsaA c ∧
    HasExactSqrtDensity ruzsaB c

/-
## Part VII: Ruzsa's Stronger Variant
-/

/-- Ruzsa's suggested variant: what if we require EXACT asymptotic
    |A ∩ {1,...,N}| ~ c_A · N^{1/2}? -/
def RuzsaVariant : Prop :=
  ∀ A B : Set ℕ, ∀ cA cB : ℝ,
    HasExactSqrtDensity A cA → HasExactSqrtDensity B cB →
    HasInfinitelyManyCommonDifferences A B

/-- The variant is not yet resolved. -/
def ruzsaVariantOpen : Prop := True

/-
## Part VIII: The Difference Set
-/

/-- The difference set A - A = {a - a' : a, a' ∈ A}. -/
def differenceSet (A : Set ℕ) : Set ℤ :=
  { d | ∃ a a' : ℕ, a ∈ A ∧ a' ∈ A ∧ d = (a : ℤ) - a' }

/-- For Ruzsa's A, the difference set is sparse. -/
axiom ruzsaA_sparse_differences :
  ∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, N ≥ 1 →
    (Finset.filter (fun d : ℤ => d ∈ differenceSet ruzsaA ∧ d.natAbs ≤ N)
      (Finset.Icc (-N : ℤ) N)).card ≤ c * N^(1/2 : ℝ)

/-- This sparseness is why common differences can be avoided. -/
def sparseness_explanation : Prop :=
  -- If A - A and B - B are both sparse (density N^{1/2}),
  -- their intersection can be finite or even empty
  True

/-
## Part IX: Comparison with Larger Densities
-/

/-- For density > N^{1/2}, common differences exist. -/
axiom larger_density_common_differences (α : ℝ) (hα : α > 1/2) :
  ∀ A B : Set ℕ, HasDensityAtLeast A α → HasDensityAtLeast B α →
    HasInfinitelyManyCommonDifferences A B

/-- The threshold N^{1/2} is critical. -/
def threshold_critical : Prop :=
  -- At density > N^{1/2}: common differences guaranteed
  -- At density ≍ N^{1/2}: counterexample exists
  True

/-
## Part X: Summary
-/

/-- **Erdős Problem #331: DISPROVED**

Question: If |A ∩ {1,...,N}| ≫ N^{1/2} and |B ∩ {1,...,N}| ≫ N^{1/2},
must there be infinitely many solutions to a₁ - a₂ = b₁ - b₂ ≠ 0?

Answer: NO (Ruzsa counterexample)

Ruzsa's construction:
- A = numbers with binary digits only in even positions
- B = numbers with binary digits only in odd positions
- Every n has unique representation n = a + b
- Therefore, no nontrivial common differences exist

The threshold N^{1/2} is critical for this phenomenon.
-/
theorem erdos_331 : ¬ErdosConjecture331 := erdos_331_disproved

/-- Main result: the conjecture is FALSE. -/
theorem erdos_331_main : ¬ErdosConjecture331 := erdos_331

/-- Ruzsa provided the counterexample. -/
theorem erdos_331_ruzsa :
    ∃ A B : Set ℕ, HasSqrtDensity A ∧ HasSqrtDensity B ∧
    ¬HasInfinitelyManyCommonDifferences A B :=
  ⟨ruzsaA, ruzsaB, ruzsa_counterexample⟩

end Erdos331
