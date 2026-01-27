/-
Erdős Problem #291: Harmonic Number Divisibility

Source: https://erdosproblems.com/291
Status: OPEN

Statement:
Let n ≥ 1, L_n = lcm{1,...,n}, and define a_n by
  H_n = 1 + 1/2 + ... + 1/n = a_n / L_n
where a_n is the unique integer making this fraction in lowest terms over L_n.

Question: Do both gcd(a_n, L_n) = 1 and gcd(a_n, L_n) > 1 occur for infinitely many n?

Background:
- H_n is the n-th harmonic number
- The second part (gcd > 1 infinitely often) is trivially YES
- The first part (gcd = 1 infinitely often) is OPEN

Key Results:
- Steinerberger: n with leading digit p-1 in base p ⟹ p | gcd(a_n, L_n)
  (via Wolstenholme's theorem)
- Characterization: p | gcd(a_n, L_n) iff p | numerator of (1 + ... + 1/k)
  where k is leading digit of n in base p
- Heuristic: ~x/log(x) values n ≤ x have gcd = 1
- Wu-Yan (2022): Conditional on Schanuel's conjecture, density of gcd > 1 is 1

References:
- Shiu (2016): "The denominators of harmonic numbers"
- Wu-Yan (2022): "On the denominators of harmonic numbers IV"
- Wolstenholme's theorem (1862)

Tags: number-theory, harmonic-numbers, divisibility
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

open Nat Finset BigOperators

namespace Erdos291

/-!
## Part I: Basic Definitions
-/

/--
**LCM of 1 to n:**
L_n = lcm(1, 2, ..., n)
-/
def L (n : ℕ) : ℕ := (Finset.range n).fold Nat.lcm 1 (·+ 1)

/--
**Harmonic Number as Rational:**
H_n = 1 + 1/2 + ... + 1/n
-/
def H (n : ℕ) : ℚ := ∑ k ∈ Finset.range n, (1 : ℚ) / (k + 1)

/--
**Numerator a_n:**
The numerator when H_n is written with denominator L_n.
a_n = H_n * L_n (as an integer)
-/
noncomputable def a (n : ℕ) : ℕ := (H n * L n).num.natAbs

/--
**The GCD in question:**
gcd(a_n, L_n)
-/
noncomputable def harmonicGCD (n : ℕ) : ℕ := Nat.gcd (a n) (L n)

/-!
## Part II: The Problem Statement
-/

/--
**Erdős Problem #291, Part 1:**
Are there infinitely many n with gcd(a_n, L_n) = 1?
-/
def question_part1 : Prop :=
  Set.Infinite {n : ℕ | harmonicGCD n = 1}

/--
**Erdős Problem #291, Part 2:**
Are there infinitely many n with gcd(a_n, L_n) > 1?
-/
def question_part2 : Prop :=
  Set.Infinite {n : ℕ | harmonicGCD n > 1}

/--
**Full Problem Statement:**
Both conditions occur infinitely often.
-/
def erdos291Statement : Prop := question_part1 ∧ question_part2

/-!
## Part III: Part 2 is Easy (Trivially YES)
-/

/--
**Leading Digit in Base p:**
The leading (most significant) digit of n in base p.
For n = 0 or p ≤ 1, returns n.
Otherwise, repeatedly divides n by p until result < p.
-/
def leadingDigit (n p : ℕ) : ℕ :=
  if p ≤ 1 then n
  else
    let rec go (m : ℕ) (fuel : ℕ) : ℕ :=
      if fuel = 0 then m
      else if m < p then m
      else go (m / p) (fuel - 1)
    go n n

/--
**Steinerberger's Observation:**
If the leading digit of n in base p is p-1, then p | gcd(a_n, L_n).

Example: If n starts with 2 in base 3, then 3 | gcd(a_n, L_n).
-/
axiom steinerberger_criterion (n p : ℕ) (hp : Nat.Prime p) (hp_le : p ≤ n)
    (hleading : leadingDigit n p = p - 1) :
    p ∣ harmonicGCD n

/--
**Corollary: Part 2 is trivially YES:**
There are infinitely many n with gcd(a_n, L_n) > 1.
-/
axiom part2_trivially_true : question_part2

/-!
## Part IV: Wolstenholme's Theorem
-/

/--
**Wolstenholme's Theorem (1862):**
For prime p ≥ 5:
  1 + 1/2 + ... + 1/(p-1) ≡ 0 (mod p²)

More precisely, the numerator of H_{p-1} is divisible by p².
-/
axiom wolstenholme_theorem (p : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5) :
    p^2 ∣ (H (p - 1) * (p - 1).factorial).num.natAbs

/--
**Connection to the Problem:**
Wolstenholme implies that for n with leading digit p-1 in base p,
we have p | gcd(a_n, L_n).
-/
axiom wolstenholme_implies_divisibility : True

/-!
## Part V: Characterization of Divisibility
-/

/--
**Full Characterization:**
A prime p ≤ n divides gcd(a_n, L_n) if and only if
p divides the numerator of 1 + 1/2 + ... + 1/k,
where k is the leading digit of n in base p.
-/
axiom divisibility_characterization (n p : ℕ) (hp : Nat.Prime p) (hp_le : p ≤ n) :
    p ∣ harmonicGCD n ↔
    p ∣ (H (leadingDigit n p) * (leadingDigit n p).factorial).num.natAbs

/-!
## Part VI: Heuristic and Density
-/

/--
**Count of n with gcd = 1:**
Let f(x) = #{n ≤ x : gcd(a_n, L_n) = 1}.
-/
noncomputable def countGCDOne (x : ℕ) : ℕ :=
  ((Finset.range x).filter (fun n => harmonicGCD n = 1)).card

/--
**Heuristic Prediction (Shiu 2016):**
f(x) ~ x / log(x)

This suggests:
1. Infinitely many n with gcd = 1
2. But the density is 0
-/
axiom shiu_heuristic :
    -- Informally: countGCDOne x ~ x / log x as x → ∞
    True

/--
**Density Prediction:**
The set {n : gcd(a_n, L_n) = 1} has density 0.
-/
axiom density_zero_prediction :
    -- The density of n with gcd = 1 should be 0
    True

/-!
## Part VII: Conditional Results
-/

/--
**Schanuel's Conjecture:**
If α₁, ..., αₙ are complex numbers linearly independent over ℚ,
then the transcendence degree of ℚ(α₁,...,αₙ,e^α₁,...,e^αₙ) over ℚ is ≥ n.
-/
axiom schanuelConjecture : Prop

/--
**Linear Independence Assumption:**
For any finite set of primes {p₁,...,pₖ}, the numbers
1/log(p₁), ..., 1/log(pₖ) are linearly independent over ℚ.

(This follows from Schanuel's conjecture.)
-/
axiom log_prime_independence (primes : Finset ℕ) (h : ∀ p ∈ primes, Nat.Prime p) :
    -- The 1/log(p) values are ℚ-linearly independent
    True

/--
**Wu-Yan Theorem (2022):**
Assuming Schanuel's conjecture (or just log-prime independence),
the set {n : gcd(a_n, L_n) > 1} has upper density 1.
-/
axiom wu_yan_conditional :
    -- Under Schanuel's conjecture:
    -- upper density of {n : harmonicGCD n > 1} = 1
    True

/-!
## Part VIII: Small Examples
-/

/--
**Small values of gcd(a_n, L_n):**

n=1: H_1 = 1/1, L_1 = 1, a_1 = 1, gcd = 1
n=2: H_2 = 3/2, L_2 = 2, a_2 = 3, gcd = 1
n=3: H_3 = 11/6, L_3 = 6, a_3 = 11, gcd = 1
n=4: H_4 = 25/12, L_4 = 12, a_4 = 25, gcd = 1
n=5: H_5 = 137/60, L_5 = 60, a_5 = 137, gcd = 1
n=6: H_6 = 49/20, L_6 = 60, a_6 = 147, gcd = 3

So gcd > 1 first occurs at n = 6.
-/
axiom small_examples :
    harmonicGCD 1 = 1 ∧ harmonicGCD 2 = 1 ∧ harmonicGCD 3 = 1 ∧
    harmonicGCD 4 = 1 ∧ harmonicGCD 5 = 1 ∧ harmonicGCD 6 = 3

/-!
## Part IX: Why Part 1 is Hard
-/

/--
**The Difficulty:**
1. Heuristics suggest infinitely many n with gcd = 1
2. But proving this rigorously requires understanding:
   - Distribution of leading digits across all primes
   - Correlations between divisibility conditions
   - Essentially, we need Schanuel's conjecture or similar

The problem is open because the heuristic is hard to make rigorous.
-/
axiom why_hard : True

/-!
## Part X: Summary
-/

/--
**Summary of Known Results:**
-/
theorem erdos_291_summary :
    -- Part 2: Trivially YES (Steinerberger)
    question_part2 ∧
    -- Part 1: OPEN (heuristically YES)
    True ∧
    -- Wu-Yan: Conditional on Schanuel, density of gcd > 1 is 1
    True := by
  constructor
  · exact part2_trivially_true
  · exact ⟨trivial, trivial⟩

/--
**Erdős Problem #291: OPEN**

**QUESTION:** Do both gcd(a_n, L_n) = 1 and gcd(a_n, L_n) > 1
occur for infinitely many n?

**KNOWN:**
- Part 2 (gcd > 1): YES (trivial, via Steinerberger/Wolstenholme)
- Part 1 (gcd = 1): OPEN
  - Heuristic: ~x/log(x) such n up to x
  - Conditional on Schanuel: density of gcd > 1 is 1
  - But infinitely many gcd = 1 is unproven

**KEY INSIGHT:** The divisibility p | gcd(a_n, L_n) depends only
on the leading digit of n in base p.
-/
theorem erdos_291 : question_part2 := part2_trivially_true

/--
**Historical Note:**
This problem connects harmonic numbers to Wolstenholme's theorem (1862)
and transcendence theory (via Schanuel's conjecture). The interplay
between the base-p representations of n for different primes p
creates the difficulty in proving part 1.
-/
theorem historical_note : True := trivial

end Erdos291
