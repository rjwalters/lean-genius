/-
Erdős Problem #955: Sum of Proper Divisors and Density

Source: https://erdosproblems.com/955
Status: OPEN

Statement:
Let s(n) = σ(n) - n = Σ_{d|n, d<n} d be the sum of proper divisors.
If A ⊂ ℕ has density 0, then s⁻¹(A) must also have density 0.

Known Results:
- Pollack (2014): True if A is the set of primes
- Troupe (2015): True if A is integers with unusually many prime factors
- Troupe (2020): True if A is sums of two squares
- Pollack-Pomerance-Thompson (2018): True if |A ∩ [1,x]| ≤ x^{1/2+o(1)}

Conjecture of Erdős-Granville-Pomerance-Spiro (1990).

References:
- [EGPS90] Erdős-Granville-Pomerance-Spiro: On the normal behavior of iterates
- [Po14b] Pollack: Some arithmetic properties of the sum of proper divisors
- [Tr15] Troupe: On prime factors of sum-of-proper-divisors values
- [PPT18] Pollack-Pomerance-Thompson: Divisor-sum fibers

Tags: number-theory, divisor-functions, density, arithmetic-functions
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic

open Nat Finset Real Filter

namespace Erdos955

/-
## Part I: The Sum of Proper Divisors Function
-/

/-- **Sum of Divisors σ(n):** The sum of all positive divisors of n. -/
noncomputable def sigma (n : ℕ) : ℕ :=
  n.divisors.sum id

/-- **Sum of Proper Divisors s(n):**
s(n) = σ(n) - n = Σ_{d|n, d<n} d. Also called the "aliquot sum". -/
noncomputable def s (n : ℕ) : ℕ :=
  sigma n - n

/-- **Alternative definition of s(n):**
Sum only over proper divisors (d | n and d < n). -/
noncomputable def s_alt (n : ℕ) : ℕ :=
  (n.properDivisors).sum id

/-
## Part II: Perfect, Deficient, and Abundant Numbers
-/

/-- **Perfect Number:** n is perfect if s(n) = n. -/
def IsPerfect (n : ℕ) : Prop := s n = n

/-- **Deficient Number:** n is deficient if s(n) < n. -/
def IsDeficient (n : ℕ) : Prop := s n < n

/-- **Abundant Number:** n is abundant if s(n) > n. -/
def IsAbundant (n : ℕ) : Prop := s n > n

/-
## Part III: Natural Density
-/

/-- **Counting Function:** |A ∩ [1, x]| for a set A ⊆ ℕ. -/
noncomputable def countUpTo (A : Set ℕ) (x : ℕ) : ℕ :=
  (Finset.range (x + 1)).filter (fun n => n ∈ A ∧ n > 0) |>.card

/-- **Natural Density:** A has density d if |A ∩ [1,x]|/x → d as x → ∞. -/
def HasDensity (A : Set ℕ) (d : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ x in atTop, |((countUpTo A x : ℝ) / x) - d| < ε

/-- **Zero Density:** A has density 0. -/
def HasZeroDensity (A : Set ℕ) : Prop := HasDensity A 0

/-- **Positive Density:** A has positive density. -/
def HasPositiveDensity (A : Set ℕ) : Prop :=
  ∃ d : ℝ, d > 0 ∧ HasDensity A d

/-
## Part IV: The Preimage s⁻¹(A)
-/

/-- **Preimage of s:** s⁻¹(A) = {n ∈ ℕ : s(n) ∈ A} -/
def preimage_s (A : Set ℕ) : Set ℕ :=
  { n : ℕ | s n ∈ A }

/-
## Part V: The EGPS Conjecture
-/

/-- **Erdős-Granville-Pomerance-Spiro Conjecture (1990):**
If A ⊂ ℕ has density 0, then s⁻¹(A) must also have density 0.
This is the main conjecture, still OPEN in general. -/
def EGPSConjecture : Prop :=
  ∀ A : Set ℕ, HasZeroDensity A → HasZeroDensity (preimage_s A)

/-
## Part VI: Contrasting Behaviors
-/

/-- **Forward direction fails:**
s(A) can have positive density even if A has zero density.
Example: Let A = {n : n = pq for distinct primes p, q}. -/

/-- **Erdős (1973):**
There exist sets A with positive density such that s⁻¹(A) = ∅. -/

/-- **Untouchable Numbers:**
k is "untouchable" if s(n) = k has no solutions. Examples: 2, 5, 52, 88, 96, ... -/
def IsUntouchable (k : ℕ) : Prop :=
  ¬∃ n : ℕ, n > 0 ∧ s n = k

/-
## Part VII: Partial Results
-/

/-- **Pollack (2014):**
If A is the set of primes, then s⁻¹(A) has density 0. -/

/-- **Troupe (2015):**
If A is the set of integers with unusually many prime factors
(ω(n) > k log log n for some k), then s⁻¹(A) has density 0. -/

/-- **Troupe (2020):**
If A is the set of sums of two squares, then s⁻¹(A) has density 0. -/
def IsSumOfTwoSquares (n : ℕ) : Prop :=
  ∃ a b : ℕ, a^2 + b^2 = n

/-
## Part VIII: The PPT Bound
-/

/-- **Pollack-Pomerance-Thompson (2018):**
If |A ∩ [1,x]| ≤ x^{1/2 + ε(x)} with ε(x) → 0,
then #{n ≤ x : s(n) ∈ A} = o(x). -/
axiom ppt_bound :
  ∀ A : Set ℕ,
    (∀ ε > 0, ∀ᶠ x in atTop, (countUpTo A x : ℝ) ≤ x^(1/2 + ε)) →
    HasZeroDensity (preimage_s A)

/-- **Corollary:** Any "sparse enough" set satisfies the conjecture. -/
theorem sparse_sets_work (A : Set ℕ)
    (hA : ∀ ε > 0, ∀ᶠ x in atTop, (countUpTo A x : ℝ) ≤ x^(1/2 + ε)) :
    HasZeroDensity (preimage_s A) :=
  ppt_bound A hA

/-
## Part IX: Growth Bound on s(n)
-/

/-- **Growth bound on s(n):** s(n) ≪ n log log n for most n.
The exponent 1/2 in PPT appears because s maps [1, x] to [1, O(x log log x)].
If A grows like x^α with α < 1/2, the argument applies. -/

/-
## Part X: Summary
-/

/-- **Erdős Problem #955 Summary:**
Combines the known partial results and the main conjecture statement.

**Known:** Pollack (primes), Troupe (two squares), PPT (sparse sets).
**Open:** General sets of density 0. -/
axiom erdos_955_summary :
    -- Pollack: primes case
    (HasZeroDensity (preimage_s { p : ℕ | p.Prime })) ∧
    -- Troupe: sums of two squares case
    (HasZeroDensity (preimage_s { n : ℕ | IsSumOfTwoSquares n })) ∧
    -- PPT: sparse sets
    (∀ A : Set ℕ,
      (∀ ε > 0, ∀ᶠ x in atTop, (countUpTo A x : ℝ) ≤ x^(1/2 + ε)) →
      HasZeroDensity (preimage_s A))

/-- Main theorem combining known partial results. -/
theorem erdos_955 :
    (HasZeroDensity (preimage_s { p : ℕ | p.Prime })) ∧
    (HasZeroDensity (preimage_s { n : ℕ | IsSumOfTwoSquares n })) ∧
    (∀ A : Set ℕ,
      (∀ ε > 0, ∀ᶠ x in atTop, (countUpTo A x : ℝ) ≤ x^(1/2 + ε)) →
      HasZeroDensity (preimage_s A)) :=
  erdos_955_summary

end Erdos955
