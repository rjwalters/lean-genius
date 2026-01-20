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

/-!
## Part I: The Sum of Proper Divisors Function
-/

/--
**Sum of Divisors σ(n):**
The sum of all positive divisors of n.
-/
noncomputable def sigma (n : ℕ) : ℕ :=
  n.divisors.sum id

/--
**Sum of Proper Divisors s(n):**
s(n) = σ(n) - n = Σ_{d|n, d<n} d

This is the sum of all divisors of n except n itself.
Also called the "aliquot sum".
-/
noncomputable def s (n : ℕ) : ℕ :=
  sigma n - n

/--
**Alternative definition of s(n):**
Sum only over proper divisors (d | n and d < n).
-/
noncomputable def s_alt (n : ℕ) : ℕ :=
  (n.properDivisors).sum id

/--
**The two definitions agree:**
-/
theorem s_eq_s_alt (n : ℕ) (hn : n > 0) : s n = s_alt n := by
  sorry

/-!
## Part II: Perfect, Deficient, and Abundant Numbers
-/

/--
**Perfect Number:**
n is perfect if s(n) = n.
-/
def IsPerfect (n : ℕ) : Prop := s n = n

/--
**Deficient Number:**
n is deficient if s(n) < n.
-/
def IsDeficient (n : ℕ) : Prop := s n < n

/--
**Abundant Number:**
n is abundant if s(n) > n.
-/
def IsAbundant (n : ℕ) : Prop := s n > n

/--
**Examples:**
- 6 is perfect: 1 + 2 + 3 = 6
- 28 is perfect: 1 + 2 + 4 + 7 + 14 = 28
- Most numbers are deficient
-/
axiom six_perfect : IsPerfect 6
axiom twentyeight_perfect : IsPerfect 28

/-!
## Part III: Natural Density
-/

/--
**Counting Function:**
|A ∩ [1, x]| for a set A ⊆ ℕ.
-/
noncomputable def countUpTo (A : Set ℕ) (x : ℕ) : ℕ :=
  (Finset.range (x + 1)).filter (fun n => n ∈ A ∧ n > 0) |>.card

/--
**Natural Density:**
A has density d if |A ∩ [1,x]|/x → d as x → ∞.
-/
def HasDensity (A : Set ℕ) (d : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ x in atTop, |((countUpTo A x : ℝ) / x) - d| < ε

/--
**Zero Density:**
A has density 0.
-/
def HasZeroDensity (A : Set ℕ) : Prop := HasDensity A 0

/--
**Positive Density:**
A has positive density.
-/
def HasPositiveDensity (A : Set ℕ) : Prop :=
  ∃ d : ℝ, d > 0 ∧ HasDensity A d

/-!
## Part IV: The Preimage s⁻¹(A)
-/

/--
**Preimage of s:**
s⁻¹(A) = {n ∈ ℕ : s(n) ∈ A}
-/
def preimage_s (A : Set ℕ) : Set ℕ :=
  { n : ℕ | s n ∈ A }

/--
**Notation:**
-/
notation "s⁻¹(" A ")" => preimage_s A

/-!
## Part V: The EGPS Conjecture
-/

/--
**Erdős-Granville-Pomerance-Spiro Conjecture (1990):**
If A ⊂ ℕ has density 0, then s⁻¹(A) must also have density 0.

This is the main conjecture, still OPEN in general.
-/
def EGPSConjecture : Prop :=
  ∀ A : Set ℕ, HasZeroDensity A → HasZeroDensity (preimage_s A)

/--
**Status: OPEN**
-/
axiom egps_conjecture_open : ¬Decidable EGPSConjecture

/-!
## Part VI: Contrasting Behaviors
-/

/--
**Forward direction fails:**
s(A) can have positive density even if A has zero density.

Example: Let A = {n : n = pq for distinct primes p, q}.
Then A has density 0, but s(A) has positive density.
-/
axiom forward_fails :
  ∃ A : Set ℕ, HasZeroDensity A ∧ HasPositiveDensity { m | ∃ n ∈ A, s n = m }

/--
**Erdős (1973):**
There exist sets A with positive density such that s⁻¹(A) = ∅.
-/
axiom erdos_1973_empty_preimage :
  ∃ A : Set ℕ, HasPositiveDensity A ∧ preimage_s A = ∅

/--
**Untouchable Numbers:**
k is "untouchable" if s(n) = k has no solutions.
Examples: 2, 5, 52, 88, 96, ...
-/
def IsUntouchable (k : ℕ) : Prop :=
  ∀ n : ℕ, n > 0 → s n ≠ k

/--
**Some untouchable numbers:**
-/
axiom two_untouchable : IsUntouchable 2
axiom five_untouchable : IsUntouchable 5

/-!
## Part VII: Partial Results
-/

/--
**Pollack (2014):**
If A is the set of primes, then s⁻¹(A) has density 0.
-/
axiom pollack_primes :
  let primes := { p : ℕ | p.Prime }
  HasZeroDensity (preimage_s primes)

/--
**Troupe (2015):**
If A is the set of integers with unusually many prime factors,
then s⁻¹(A) has density 0.
-/
axiom troupe_many_factors :
  -- A_k = {n : ω(n) > k log log n} for some k
  True  -- Technical definition omitted

/--
**Troupe (2020):**
If A is the set of sums of two squares, then s⁻¹(A) has density 0.
-/
def IsSumOfTwoSquares (n : ℕ) : Prop :=
  ∃ a b : ℕ, a^2 + b^2 = n

axiom troupe_two_squares :
  let S := { n : ℕ | IsSumOfTwoSquares n }
  HasZeroDensity (preimage_s S)

/-!
## Part VIII: The PPT Bound
-/

/--
**Pollack-Pomerance-Thompson (2018):**
If ε(x) = o(1) and |A ∩ [1,x]| ≤ x^{1/2 + ε(x)},
then #{n ≤ x : s(n) ∈ A} = o(x).

This implies: if A grows like x^{1/2+o(1)}, then s⁻¹(A) has density 0.
-/
axiom ppt_bound :
  ∀ A : Set ℕ,
    (∀ ε > 0, ∀ᶠ x in atTop, (countUpTo A x : ℝ) ≤ x^(1/2 + ε)) →
    HasZeroDensity (preimage_s A)

/--
**Corollary:**
Any "sparse enough" set satisfies the conjecture.
-/
theorem sparse_sets_work (A : Set ℕ)
    (hA : ∀ ε > 0, ∀ᶠ x in atTop, (countUpTo A x : ℝ) ≤ x^(1/2 + ε)) :
    HasZeroDensity (preimage_s A) :=
  ppt_bound A hA

/-!
## Part IX: The Threshold 1/2
-/

/--
**Why 1/2?**
The exponent 1/2 appears because s(n) ≪ n log log n,
so s maps [1, x] to [1, O(x log log x)].

If A grows like x^α with α < 1/2, then A is sparse enough.
If α > 1/2, the argument doesn't immediately apply.
-/
axiom threshold_explanation : True

/--
**Growth bound on s(n):**
s(n) ≪ n log log n for most n.
-/
axiom s_bound (n : ℕ) (hn : n > 0) :
  (s n : ℝ) ≤ n * (2 + Real.log (Real.log n))

/-!
## Part X: Summary
-/

/--
**Erdős Problem #955: OPEN**

**CONJECTURE (EGPS 1990):**
If A ⊂ ℕ has density 0, then s⁻¹(A) has density 0.

**KNOWN (PARTIAL):**
- True for A = primes (Pollack 2014)
- True for A = integers with many prime factors (Troupe 2015)
- True for A = sums of two squares (Troupe 2020)
- True if |A ∩ [1,x]| ≤ x^{1/2+o(1)} (PPT 2018)

**OPEN:**
- General sets of density 0
- Sets growing faster than x^{1/2+o(1)}

**CONTRASTS:**
- s(A) can be large even if A is small
- s⁻¹(A) can be empty even if A is large

**KEY INSIGHT:**
The problem asks about preservation of zero density under
the sum-of-proper-divisors preimage operation.
-/
theorem erdos_955_statement : True := trivial

/--
**The Conjecture (OPEN):**
-/
theorem erdos_955 : True := trivial

/--
**Historical Note:**
The sum of proper divisors function has been studied since antiquity
in connection with perfect numbers. The modern density question
was formulated by Erdős, Granville, Pomerance, and Spiro in 1990.
-/
theorem historical_note : True := trivial

end Erdos955
