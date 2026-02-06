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

/-
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

/-
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

/-
## Part III: Part 2 is Easy (Trivially YES)
-/

/--
**Leading digit helper:**
Repeatedly divides m by p, decrementing fuel each step.
Returns when m < p or fuel runs out.
-/
def leadingDigitAux (p m fuel : ℕ) : ℕ :=
  if fuel = 0 then m
  else if m < p then m
  else leadingDigitAux p (m / p) (fuel - 1)

/--
**Leading Digit in Base p:**
The leading (most significant) digit of n in base p.
For n = 0 or p ≤ 1, returns n.
Otherwise, repeatedly divides n by p until result < p.
-/
def leadingDigit (n p : ℕ) : ℕ :=
  if p ≤ 1 then n
  else leadingDigitAux p n n

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

/-
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

/-
**Connection to the Problem:**
Wolstenholme implies that for n with leading digit p-1 in base p,
we have p | gcd(a_n, L_n). This follows from the characterization theorem.
-/

/-
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

/-
## Part VI: Heuristic and Density
-/

/--
**Count of n with gcd = 1:**
Let f(x) = #{n ≤ x : gcd(a_n, L_n) = 1}.
-/
noncomputable def countGCDOne (x : ℕ) : ℕ :=
  ((Finset.range x).filter (fun n => harmonicGCD n = 1)).card

/-
**Heuristic Prediction (Shiu 2016):**
f(x) ~ x / log(x)

This suggests:
1. Infinitely many n with gcd = 1
2. But the density is 0

Note: This is a heuristic argument, not a theorem.
-/

/-
## Part VII: Conditional Results
-/

/--
**Schanuel's Conjecture:**
If α₁, ..., αₙ are complex numbers linearly independent over ℚ,
then the transcendence degree of ℚ(α₁,...,αₙ,e^α₁,...,e^αₙ) over ℚ is ≥ n.
-/
axiom schanuelConjecture : Prop

/-
**Wu-Yan Theorem (2022):**
Assuming Schanuel's conjecture (which implies that 1/log(p) are
ℚ-linearly independent over distinct primes p), the set
{n : gcd(a_n, L_n) > 1} has upper density 1.

This uses the fact that for "most" n, at least one prime p has
leading digit p-1 in base p, making p | gcd(a_n, L_n).
-/

/-
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

These are axiomatized because harmonicGCD is noncomputable
(involves rational arithmetic and .num.natAbs extraction).
-/
axiom small_examples :
    harmonicGCD 1 = 1 ∧ harmonicGCD 2 = 1 ∧ harmonicGCD 3 = 1 ∧
    harmonicGCD 4 = 1 ∧ harmonicGCD 5 = 1 ∧ harmonicGCD 6 = 3

/-
## Part IX: Why Part 1 is Hard
-/

/-
**The Difficulty:**
1. Heuristics suggest infinitely many n with gcd = 1
2. But proving this rigorously requires understanding:
   - Distribution of leading digits across all primes
   - Correlations between divisibility conditions
   - Essentially, we need Schanuel's conjecture or similar

The problem is open because the heuristic is hard to make rigorous.
-/

/-
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

/-
## Part XI: Structural Properties of L
-/

/-- L(0) = 1 (empty LCM) -/
theorem L_zero : L 0 = 1 := by
  simp [L]

/-- L(1) = 1 (lcm of {1}) -/
theorem L_one : L 1 = 1 := by
  simp [L]

/-- L(2) = 2 (lcm of {1, 2}) -/
theorem L_two : L 2 = 2 := by native_decide

/-- L(3) = 6 -/
theorem L_three : L 3 = 6 := by native_decide

/-- L(4) = 12 -/
theorem L_four : L 4 = 12 := by native_decide

/-- L(5) = 60 -/
theorem L_five : L 5 = 60 := by native_decide

/-- L(6) = 60 -/
theorem L_six : L 6 = 60 := by native_decide

/-- L(n) > 0 for all n -/
theorem L_pos (n : ℕ) : L n > 0 := by
  induction n with
  | zero => simp [L]
  | succ k ih =>
    simp only [L] at ih ⊢
    rw [Finset.range_add_one, Finset.fold_insert (Finset.notMem_range_self)]
    exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega))

/-- L(n) divides n! -/
theorem L_dvd_factorial (n : ℕ) : L n ∣ n.factorial := by
  simp only [L]
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.range_add_one, Finset.fold_insert (Finset.notMem_range_self)]
    rw [Nat.factorial_succ]
    apply Nat.lcm_dvd
    · exact Nat.dvd_mul_right (k + 1) k.factorial
    · exact dvd_trans ih (Nat.dvd_mul_left k.factorial (k + 1))

/-- Every k in {1,...,n} divides L(n) -/
theorem dvd_L (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) : k ∣ L n := by
  -- Strategy: k divides k!, k! divides n! (since k ≤ n), and L(n) divides n!
  -- Actually we need k | L(n), not n! | L(n).
  -- Use induction on n, building up lcm step by step.
  induction n with
  | zero => omega
  | succ m ih =>
    simp only [L] at *
    rw [Finset.range_add_one, Finset.fold_insert (Finset.notMem_range_self)]
    by_cases hkm : k = m + 1
    · -- k = m+1, so k divides lcm(k, L(m))
      subst hkm
      exact Nat.dvd_lcm_left _ _
    · -- k ≤ m, use IH
      have hkm' : k ≤ m := by omega
      exact dvd_trans (ih hkm') (Nat.dvd_lcm_right _ _)

/-
## Part XII: Structural Properties of H
-/

/-- H(0) = 0 (empty sum) -/
theorem H_zero : H 0 = 0 := by
  simp [H]

/-- H(1) = 1 -/
theorem H_one : H 1 = 1 := by
  simp [H]

/-- H(2) = 3/2 -/
theorem H_two : H 2 = 3 / 2 := by
  simp [H, Finset.sum_range_succ]
  norm_num

/-- H(3) = 11/6 -/
theorem H_three : H 3 = 11 / 6 := by
  simp [H, Finset.sum_range_succ]
  norm_num

/-- H(4) = 25/12 -/
theorem H_four : H 4 = 25 / 12 := by
  simp [H, Finset.sum_range_succ]
  norm_num

/-- H(5) = 137/60 -/
theorem H_five : H 5 = 137 / 60 := by
  simp [H, Finset.sum_range_succ]
  norm_num

/-- H(6) = 49/20 -/
theorem H_six : H 6 = 49 / 20 := by
  simp [H, Finset.sum_range_succ]
  norm_num

/-- H(n+1) = H(n) + 1/(n+1) -/
theorem H_succ (n : ℕ) : H (n + 1) = H n + 1 / (↑n + 1 : ℚ) := by
  simp [H, Finset.sum_range_succ]

/-- H(n) > 0 for n ≥ 1 -/
theorem H_pos (n : ℕ) (hn : n ≥ 1) : H n > 0 := by
  simp only [H]
  apply Finset.sum_pos
  · intro i _
    positivity
  · exact ⟨0, Finset.mem_range.mpr (by omega)⟩

/-- H is strictly increasing: H(n+1) > H(n) -/
theorem H_strict_mono (n : ℕ) : H (n + 1) > H n := by
  simp only [H, Finset.sum_range_succ]
  linarith [show (1 : ℚ) / (↑n + 1) > 0 from by positivity]

/-- H is monotone: m ≤ n → H(m) ≤ H(n) -/
theorem H_mono (m n : ℕ) (hmn : m ≤ n) : H m ≤ H n := by
  simp only [H]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
  intro i _ _
  positivity

/-
## Part XIII: Leading Digit Properties
-/

/-- leadingDigit of 0 is 0 -/
theorem leadingDigit_zero (p : ℕ) (hp : p > 1) : leadingDigit 0 p = 0 := by
  unfold leadingDigit
  simp only [show ¬(p ≤ 1) from by omega, ↓reduceIte]
  unfold leadingDigitAux
  simp

/-- Helper: leadingDigitAux returns < p when fuel ≥ m and p > 1 -/
theorem leadingDigitAux_lt (p m fuel : ℕ) (hp : p > 1) (hfuel : fuel ≥ m) :
    leadingDigitAux p m fuel < p := by
  induction fuel generalizing m with
  | zero =>
    have : m = 0 := by omega
    subst this
    unfold leadingDigitAux
    simp; omega
  | succ k ih =>
    unfold leadingDigitAux
    simp only [show k + 1 ≠ 0 from Nat.succ_ne_zero k, ↓reduceIte]
    split
    · assumption
    · push_neg at *
      rename_i hmp
      apply ih
      have h1 : m / p < m := Nat.div_lt_self (by omega) hp
      omega

/-- leadingDigit returns a value < p for p > 1 and n > 0 -/
theorem leadingDigit_lt_base (n p : ℕ) (hp : p > 1) (_hn : n > 0) :
    leadingDigit n p < p := by
  unfold leadingDigit
  simp only [show ¬(p ≤ 1) from by omega, ↓reduceIte]
  exact leadingDigitAux_lt p n n hp (le_refl n)

/-- leadingDigit of 2 in base 3 is 2 -/
theorem leadingDigit_two_three : leadingDigit 2 3 = 2 := by native_decide

/-- leadingDigit of 5 in base 3 is 1 (5 = 1·3 + 2) -/
theorem leadingDigit_five_three : leadingDigit 5 3 = 1 := by native_decide

/-- leadingDigit of 6 in base 3 is 2 (6 = 2·3) -/
theorem leadingDigit_six_three : leadingDigit 6 3 = 2 := by native_decide

/-- leadingDigit of 8 in base 3 is 2 (8 = 2·3 + 2) -/
theorem leadingDigit_eight_three : leadingDigit 8 3 = 2 := by native_decide

/-- leadingDigit of 4 in base 5 is 4 -/
theorem leadingDigit_four_five : leadingDigit 4 5 = 4 := by native_decide

/-- leadingDigit of 24 in base 5 is 4 (24 = 4·5 + 4) -/
theorem leadingDigit_24_five : leadingDigit 24 5 = 4 := by native_decide

/-
## Part XIV: GCD Structure
-/

/-- The GCD divides L_n -/
theorem harmonicGCD_dvd_L (n : ℕ) : harmonicGCD n ∣ L n :=
  Nat.gcd_dvd_right (a n) (L n)

/-- The GCD divides a_n -/
theorem harmonicGCD_dvd_a (n : ℕ) : harmonicGCD n ∣ a n :=
  Nat.gcd_dvd_left (a n) (L n)

/-- A prime larger than n does not divide n! -/
theorem prime_not_dvd_factorial_of_gt (p n : ℕ) (hp : Nat.Prime p) (hpn : n < p) :
    ¬(p ∣ n.factorial) := by
  induction n with
  | zero => simp; exact hp.one_lt.ne'
  | succ m ih =>
    rw [Nat.factorial_succ]
    intro hdvd
    rcases hp.dvd_mul.mp hdvd with h5 | h5
    · exact absurd (Nat.le_of_dvd (by omega) h5) (by omega)
    · exact ih (by omega) h5

/-- If prime p divides L(n), then p ≤ n -/
theorem prime_dvd_L_le (n p : ℕ) (hp : Nat.Prime p) (hpdvd : p ∣ L n) : p ≤ n := by
  by_contra h
  push_neg at h
  have h1 : p ∣ n.factorial := dvd_trans hpdvd (L_dvd_factorial n)
  exact prime_not_dvd_factorial_of_gt p n hp h h1

/--
**If p | gcd(a_n, L_n), then p ≤ n.**
A prime dividing the GCD must divide L_n = lcm(1,...,n), hence p ≤ n.
-/
theorem prime_div_gcd_le (n p : ℕ) (hp : Nat.Prime p) (hpdvd : p ∣ harmonicGCD n) :
    p ≤ n :=
  prime_dvd_L_le n p hp (dvd_trans hpdvd (harmonicGCD_dvd_L n))

/-- From small_examples: the first occurrence of gcd > 1 is at n = 6 -/
theorem first_gcd_gt_one : harmonicGCD 6 = 3 := small_examples.2.2.2.2.2

/-- From small_examples: H_1 through H_5 all have gcd = 1 -/
theorem small_gcd_one (n : ℕ) (hn : 1 ≤ n) (hn5 : n ≤ 5) : harmonicGCD n = 1 := by
  interval_cases n
  · exact small_examples.1
  · exact small_examples.2.1
  · exact small_examples.2.2.1
  · exact small_examples.2.2.2.1
  · exact small_examples.2.2.2.2.1

/-
## Part XV: Applying Steinerberger to Concrete Cases
-/

/-- 3 divides gcd(a_6, L_6): since leadingDigit 6 3 = 2 = 3-1 -/
theorem three_dvd_gcd_six : 3 ∣ harmonicGCD 6 := by
  apply steinerberger_criterion 6 3 (by decide) (by omega)
  native_decide

/-- 3 divides gcd(a_8, L_8): since leadingDigit 8 3 = 2 = 3-1 -/
theorem three_dvd_gcd_eight : 3 ∣ harmonicGCD 8 := by
  apply steinerberger_criterion 8 3 (by decide) (by omega)
  native_decide

/-- 5 divides gcd(a_24, L_24): since leadingDigit 24 5 = 4 = 5-1 -/
theorem five_dvd_gcd_24 : 5 ∣ harmonicGCD 24 := by
  apply steinerberger_criterion 24 5 (by decide) (by omega)
  native_decide

/-- Helper: leadingDigitAux 3 (2 * 3^k) fuel = 2 when fuel ≥ k -/
private theorem leadingDigitAux_two_pow_three (k fuel : ℕ) (hfuel : fuel ≥ k) :
    leadingDigitAux 3 (2 * 3^k) fuel = 2 := by
  induction k generalizing fuel with
  | zero =>
    simp only [pow_zero, mul_one]
    unfold leadingDigitAux
    simp
  | succ j ih =>
    -- 2 * 3^(j+1) ≥ 3, so we recurse
    have h_ge_3 : 2 * 3^(j+1) ≥ 3 := by
      have : 3^(j+1) ≥ 1 := Nat.one_le_pow (j+1) 3 (by omega)
      omega
    have h_not_lt_3 : ¬ (2 * 3^(j+1) < 3) := by omega
    have h_fuel_pos : fuel ≠ 0 := by omega
    unfold leadingDigitAux
    simp only [h_fuel_pos, ↓reduceIte, h_not_lt_3]
    -- recurse: (2 * 3^(j+1)) / 3 = 2 * 3^j
    have hdiv : 2 * 3^(j+1) / 3 = 2 * 3^j := by
      have : 2 * 3^(j+1) = 2 * 3^j * 3 := by ring
      rw [this]
      exact Nat.mul_div_cancel _ (by omega)
    rw [hdiv]
    exact ih (fuel - 1) (by omega)

/-- 3^k ≥ k for all k (exponential dominates linear) -/
private theorem pow_three_ge (k : ℕ) : 3^k ≥ k := by
  induction k with
  | zero => simp
  | succ j ih =>
    have h1 : 3^(j+1) = 3^j * 3 := pow_succ 3 j
    rw [h1]
    have h2 : 3^j ≥ 1 := Nat.one_le_pow j 3 (by omega)
    have h3 : 3^j * 3 = 3 * 3^j := by ring
    rw [h3]
    have h4 : 3 * 3^j ≥ 3 * j := Nat.mul_le_mul_left 3 ih
    -- 3 * 3^j ≥ 3 * j ≥ 3 * 0 = 0 for j ≥ 0
    -- We need 3 * 3^j ≥ j + 1
    -- Since 3^j ≥ 1, we have 3 * 3^j ≥ 3 ≥ 1
    -- Since 3 * 3^j ≥ 3 * j and 3 * j + 3 ≥ j + 1 (i.e. 2*j + 3 ≥ 1), we have
    -- 3 * 3^j ≥ 3 * j ≥ max(j, 1) and 3*3^j ≥ 3 ≥ 1
    -- So 3 * 3^j = 3^j + 3^j + 3^j ≥ 1 + j + 0 = j + 1
    calc 3 * 3^j = 3^j + 3^j + 3^j := by ring
      _ ≥ 1 + j + 0 := by linarith [h2, ih]
      _ = j + 1 := by ring

/-- For n = 2·3^k, the leading digit in base 3 is 2 = 3-1.
    Mathematical insight: 2·3^k in base 3 is written as 2 followed by k zeros. -/
theorem leadingDigit_two_times_pow_three (k : ℕ) :
    leadingDigit (2 * 3^k) 3 = 2 := by
  unfold leadingDigit
  simp only [show ¬(3 ≤ 1) from by omega, ↓reduceIte]
  apply leadingDigitAux_two_pow_three
  -- Need fuel = 2 * 3^k ≥ k
  have h : 3^k ≥ k := pow_three_ge k
  have h2 : 3^k ≥ 1 := Nat.one_le_pow k 3 (by omega)
  calc 2 * 3^k ≥ 1 * 3^k := by omega
    _ = 3^k := by ring
    _ ≥ k := h

/-- From leadingDigit_two_times_pow_three and Steinerberger:
    3 divides gcd(a_{2·3^k}, L_{2·3^k}) for k ≥ 1. -/
theorem three_dvd_gcd_two_pow_three (k : ℕ) (hk : k ≥ 1) :
    (3 : ℕ) ∣ harmonicGCD (2 * 3^k) := by
  apply steinerberger_criterion _ 3 (by decide)
  · have h3k : 3^k ≥ 3^1 := Nat.pow_le_pow_right (by omega) hk
    simp at h3k
    linarith
  · exact leadingDigit_two_times_pow_three k

/-
## Part XVI: Structural Observations
-/

/-- For n ≥ 1, n divides L(n) -/
theorem n_dvd_L (n : ℕ) (hn : n ≥ 1) : n ∣ L n := dvd_L n n hn (le_refl n)

/-- The product H(n) * L(n) is always a non-negative integer.
    This follows because L(n) = lcm(1,...,n) and each term 1/k * L(n) is
    an integer (since k | L(n) for k ≤ n). -/
theorem H_mul_L_nonneg (n : ℕ) : H n * (L n : ℚ) ≥ 0 := by
  apply mul_nonneg
  · by_cases hn : n = 0
    · simp [hn, H_zero]
    · exact le_of_lt (H_pos n (by omega))
  · exact Nat.cast_nonneg (α := ℚ) (L n)

/-- H(n) * L(n) equals the sum ∑_{k=0}^{n-1} L(n)/(k+1),
    each term being an integer since (k+1) | L(n). -/
theorem H_mul_L_eq_sum (n : ℕ) :
    H n * (L n : ℚ) = ∑ k ∈ Finset.range n, (L n : ℚ) / (k + 1) := by
  simp only [H, Finset.sum_mul]
  congr 1
  ext i
  field_simp

end Erdos291
