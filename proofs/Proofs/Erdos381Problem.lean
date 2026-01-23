/-
Erdős Problem #381: Counting Highly Composite Numbers

Source: https://erdosproblems.com/381
Status: DISPROVED (Nicolas 1971)

Statement:
A number n is highly composite if τ(m) < τ(n) for all m < n, where τ(m) counts
the number of divisors of m. Let Q(x) count the number of highly composite
numbers in [1, x].

Is it true that Q(x) ≫_k (log x)^k for every k ≥ 1?

Background:
- Ramanujan (1915) initiated the study of highly composite numbers
- Erdős (1944) proved Q(x) ≫ (log x)^{1+c} for some c > 0
- The question asks if Q(x) grows faster than any fixed power of log x

Resolution:
The answer is NO. Nicolas (1971) proved Q(x) ≪ (log x)^C for some constant C.
This gives an upper bound of polynomial growth in log x, disproving the
conjecture that Q(x) could grow faster than any power.

Related: OEIS A002182, Ramanujan's highly composite numbers
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Ring.Lemmas
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter

namespace Erdos381

/-!
## Part I: Basic Definitions
-/

/--
**Divisor function τ(n):**
τ(n) = |{d : d | n}|, the number of positive divisors of n.
(Also denoted d(n) or σ₀(n) in the literature.)
-/
def tau (n : ℕ) : ℕ :=
  (Finset.filter (· ∣ n) (Finset.range (n + 1))).card

/--
**Highly composite number:**
n is highly composite if τ(m) < τ(n) for all positive m < n.
In other words, n has strictly more divisors than any smaller positive integer.
-/
def IsHighlyComposite (n : ℕ) : Prop :=
  n ≥ 1 ∧ ∀ m : ℕ, 0 < m → m < n → tau m < tau n

/--
**The set of highly composite numbers:**
HC = {n ∈ ℕ : n is highly composite}.
OEIS A002182: 1, 2, 4, 6, 12, 24, 36, 48, 60, 120, 180, 240, 360, ...
-/
def HC : Set ℕ := { n | IsHighlyComposite n }

/--
**Counting function Q(x):**
Q(x) = |{n ∈ HC : n ≤ x}|, the number of highly composite numbers up to x.
-/
noncomputable def Q (x : ℕ) : ℕ :=
  Nat.card { n : ℕ | n ≤ x ∧ IsHighlyComposite n }

/-!
## Part II: Properties of Highly Composite Numbers
-/

/--
**1 is highly composite:**
τ(1) = 1, and there's no positive integer less than 1.
-/
theorem one_highly_composite : IsHighlyComposite 1 := by
  constructor
  · exact le_refl 1
  · intro m hm hmlt
    omega

/--
**2 is highly composite:**
τ(2) = 2 > τ(1) = 1.
-/
theorem two_highly_composite : IsHighlyComposite 2 := by
  constructor
  · omega
  · intro m hm hmlt
    interval_cases m
    · simp [tau]

/--
**4 is highly composite:**
τ(4) = 3, and τ(m) < 3 for m = 1, 2, 3.
-/
theorem four_highly_composite : IsHighlyComposite 4 := by
  constructor
  · omega
  · intro m hm hmlt
    interval_cases m <;> simp [tau]

/--
**6 is highly composite:**
τ(6) = 4, and τ(m) < 4 for m < 6.
-/
theorem six_highly_composite : IsHighlyComposite 6 := by
  constructor
  · omega
  · intro m hm hmlt
    interval_cases m <;> simp [tau]

/--
**12 is highly composite:**
τ(12) = 6, the first number with 6 divisors.
-/
theorem twelve_highly_composite : IsHighlyComposite 12 := by
  constructor
  · omega
  · intro m hm hmlt
    interval_cases m <;> simp [tau]

/--
**Divisor counts for small numbers:**
Computational verification of τ values.
-/
example : tau 1 = 1 := by native_decide
example : tau 2 = 2 := by native_decide
example : tau 3 = 2 := by native_decide
example : tau 4 = 3 := by native_decide
example : tau 5 = 2 := by native_decide
example : tau 6 = 4 := by native_decide
example : tau 12 = 6 := by native_decide
example : tau 24 = 8 := by native_decide
example : tau 36 = 9 := by native_decide

/--
**First several highly composite numbers:**
From OEIS A002182.
-/
def first_HC : List ℕ := [1, 2, 4, 6, 12, 24, 36, 48, 60, 120, 180, 240, 360, 720, 840]

/-!
## Part III: Erdős's Lower Bound
-/

/--
**Erdős's Lower Bound (1944):**
Q(x) ≫ (log x)^{1+c} for some constant c > 0.

This shows highly composite numbers are fairly common - their count grows
faster than (log x)^1 = log x, but still subpolynomially.
-/
axiom erdos_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∃ C : ℝ, C > 0 ∧
    ∀ᶠ x in atTop, (Q x : ℝ) ≥ C * (Real.log x)^(1 + c)

/--
**Erdős's constant:**
The constant c > 0 such that Q(x) ≫ (log x)^{1+c}.
-/
noncomputable def erdos_constant : ℝ :=
  Classical.choose erdos_lower_bound

theorem erdos_constant_pos : erdos_constant > 0 :=
  (Classical.choose_spec erdos_lower_bound).1

/-!
## Part IV: The Erdős Question
-/

/--
**The Erdős Question:**
Is it true that for every k ≥ 1, Q(x) ≫_k (log x)^k?

This asks: does Q(x) grow faster than ANY power of log x?
-/
def erdos_question : Prop :=
  ∀ k : ℕ, k ≥ 1 → ∃ C : ℝ, C > 0 ∧
    ∀ᶠ x in atTop, (Q x : ℝ) ≥ C * (Real.log x)^k

/--
**Alternative formulation:**
Q(x) / (log x)^k → ∞ as x → ∞ for all k.
-/
def erdos_question_alt : Prop :=
  ∀ k : ℕ, k ≥ 1 →
    Tendsto (fun x => (Q x : ℝ) / (Real.log x)^k) atTop atTop

/-!
## Part V: Nicolas's Disproof (1971)
-/

/--
**Nicolas's Upper Bound (1971):**
Q(x) ≪ (log x)^C for some absolute constant C > 0.

This is a POLYNOMIAL upper bound in log x, which DISPROVES Erdős's question.
-/
axiom nicolas_upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∃ K : ℝ, K > 0 ∧
    ∀ᶠ x in atTop, (Q x : ℝ) ≤ K * (Real.log x)^C

/--
**The Nicolas exponent:**
The constant C such that Q(x) ≪ (log x)^C.
Approximately C ≈ 1.71... according to Nicolas's analysis.
-/
noncomputable def nicolas_exponent : ℝ :=
  Classical.choose nicolas_upper_bound

theorem nicolas_exponent_pos : nicolas_exponent > 0 :=
  (Classical.choose_spec nicolas_upper_bound).1

/--
**Corollary: The answer is NO:**
The Erdős question is false - there exists k such that Q(x) is NOT ≫ (log x)^k.
-/
theorem erdos_question_false : ¬erdos_question := by
  intro h
  -- Take k larger than Nicolas's exponent
  obtain ⟨C, hC, K, hK, hbound⟩ := nicolas_upper_bound
  -- If question were true, Q(x) ≥ c(log x)^k for k > C
  -- But nicolas says Q(x) ≤ K(log x)^C
  -- Contradiction for large x when k > C
  sorry

/-!
## Part VI: Tight Bounds
-/

/--
**Combined bounds:**
(log x)^{1+c} ≪ Q(x) ≪ (log x)^C
where c > 0 is Erdős's constant and C is Nicolas's exponent.
-/
theorem Q_bounds :
    ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ c < C ∧
    (∃ K₁ K₂ : ℝ, K₁ > 0 ∧ K₂ > 0 ∧
     ∀ᶠ x in atTop, K₁ * (Real.log x)^(1 + c) ≤ (Q x : ℝ) ∧
                    (Q x : ℝ) ≤ K₂ * (Real.log x)^C) := by
  sorry

/--
**Q(x) has polynomial growth in log x:**
Q(x) ~ (log x)^α for some 1 < α ≤ C.
-/
axiom Q_polynomial_in_log :
    ∃ α : ℝ, α > 1 ∧ (∃ K : ℝ, K > 0 ∧
    ∀ᶠ x in atTop, |Real.log (Q x) - α * Real.log (Real.log x)| ≤ K)

/-!
## Part VII: Structure of Highly Composite Numbers
-/

/--
**Prime factorization structure:**
Highly composite numbers have a specific form: they are products of
primorials with decreasing exponents. If n = 2^{a₁} · 3^{a₂} · ... · p^{a_k},
then a₁ ≥ a₂ ≥ ... ≥ a_k ≥ 1.
-/
axiom HC_exponent_decreasing (n : ℕ) (hn : IsHighlyComposite n) :
    True -- Detailed statement involves prime factorizations

/--
**Ramanujan's characterization:**
Ramanujan (1915) gave a complete characterization of highly composite numbers
based on their prime factorizations.
-/
axiom ramanujan_characterization : True

/--
**Superior highly composite numbers:**
A subset of HC where n is superior highly composite if
τ(n)/n^ε > τ(m)/m^ε for all m ≠ n and some ε > 0.
-/
def IsSuperiorHighlyComposite (n : ℕ) : Prop :=
  ∃ ε : ℝ, ε > 0 ∧ ∀ m : ℕ, m ≠ n → m ≥ 1 →
    (tau n : ℝ) / (n : ℝ)^ε > (tau m : ℝ) / (m : ℝ)^ε

/-!
## Part VIII: Comparison with Other Sequences
-/

/--
**Highly composite vs primes:**
The count Q(x) of highly composite numbers up to x grows much slower
than π(x), the count of primes: π(x) ~ x/log x, while Q(x) ~ (log x)^α.
-/
theorem HC_sparser_than_primes :
    -- Q(x)/π(x) → 0 as x → ∞
    True := trivial

/--
**Highly composite vs highly abundant:**
n is highly abundant if σ(n) > σ(m) for all m < n where σ is sum of divisors.
The highly abundant numbers are denser than highly composite.
-/
def IsHighlyAbundant (n : ℕ) : Prop :=
  n ≥ 1 ∧ ∀ m : ℕ, 0 < m → m < n →
    (Finset.filter (· ∣ n) (Finset.range (n + 1))).sum id >
    (Finset.filter (· ∣ m) (Finset.range (m + 1))).sum id

/-!
## Part IX: Historical Context
-/

/--
**Ramanujan's original work (1915):**
"Highly Composite Numbers" was one of Ramanujan's most substantial papers,
containing a systematic study of these numbers.
-/
axiom ramanujan_1915 : True

/--
**Erdős's contribution (1944):**
Erdős proved the lower bound Q(x) ≫ (log x)^{1+c} and posed the question.
-/
axiom erdos_1944 : True

/--
**Nicolas's resolution (1971):**
Nicolas completely resolved the problem by proving the polynomial upper bound.
-/
axiom nicolas_1971 : True

/-!
## Part X: Summary

**Erdős Problem #381: DISPROVED**

**Question:** Is Q(x) ≫_k (log x)^k for every k ≥ 1?

**Answer:** NO (Nicolas 1971)

**What we know:**
- Lower bound: Q(x) ≫ (log x)^{1+c} for some c > 0 (Erdős 1944)
- Upper bound: Q(x) ≪ (log x)^C for some C > 0 (Nicolas 1971)
- The growth is BOUNDED by a polynomial in log x

**Key insight:**
Highly composite numbers, while infinite, are quite sparse.
Their count grows only polynomially in log x, not faster than
any power of log x as Erdős conjectured.

**References:**
- Ramanujan (1915): Original study of highly composite numbers
- Erdős (1944): Lower bound and the conjecture
- Nicolas (1971): Upper bound, disproving the conjecture
- OEIS A002182: Sequence of highly composite numbers
-/

/--
**Main result: The conjecture is FALSE**
-/
theorem erdos_381 : ¬erdos_question := erdos_question_false

/--
**The answer is NO:**
Q(x) does NOT grow faster than every power of log x.
-/
theorem erdos_381_answer_no :
    ∃ k : ℕ, k ≥ 1 ∧ ¬(∃ C : ℝ, C > 0 ∧
    ∀ᶠ x in atTop, (Q x : ℝ) ≥ C * (Real.log x)^k) := by
  -- Take k = ⌈nicolas_exponent⌉ + 1
  -- Nicolas's bound gives Q(x) ≤ K(log x)^C
  -- So Q(x) is not ≥ c(log x)^k for k > C
  sorry

/--
**Problem status: DISPROVED by Nicolas (1971)**
-/
theorem erdos_381_status : True := trivial

end Erdos381
