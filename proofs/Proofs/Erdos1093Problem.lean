/-
# Erdős Problem #1093: Deficiency of Binomial Coefficients

For n ≥ 2k, the deficiency of C(n,k) counts how many of n, n-1, ..., n-k+1
are k-smooth (all prime factors ≤ k), provided C(n,k) has no prime factor ≤ k.
Are there infinitely many with deficiency 1? Only finitely many with
deficiency > 1?

## Status: OPEN

## References
- Erdős, Lacampagne, Selfridge (1988, 1993)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-
## Section I: Smooth Numbers
-/

/-- A positive integer m is k-smooth if all its prime factors are ≤ k. -/
def IsKSmooth (k m : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ m → p ≤ k

/-- IsKSmooth is decidable: for m = 0 it's false (all primes divide 0),
    for m ≥ 1 we check finitely many prime factors via Nat.primeFactors. -/
instance isKSmooth_decidable (k : ℕ) : DecidablePred (IsKSmooth k) := fun m =>
  if hm : m = 0 then
    isFalse (by
      subst hm; intro h
      obtain ⟨p, hpk, hp⟩ := Nat.exists_infinite_primes (k + 1)
      exact absurd (h p hp (dvd_zero p)) (by omega))
  else
    decidable_of_iff (∀ p ∈ m.primeFactors, p ≤ k)
      ⟨fun hf p hp hd => hf p (Nat.mem_primeFactors.mpr ⟨hp, hd, hm⟩),
       fun h p hmem => by
         obtain ⟨hp, hd, _⟩ := Nat.mem_primeFactors.mp hmem; exact h p hp hd⟩

/-
## Section II: Deficiency
-/

/-- C(n,k) has no small prime factors: every prime dividing C(n,k) exceeds k. -/
def NoSmallPrimeFactors (n k : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n.choose k → k < p

/-- The deficiency of C(n,k): the count of indices 0 ≤ i < k such that
(n - i) is k-smooth. Defined when C(n,k) has no prime factor ≤ k. -/
def deficiency (n k : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun i => IsKSmooth k (n - i)) (Finset.range k))

/-
## Section III: The Conjectures
-/

/-- **Erdős Problem #1093 Part (i)**: Are there infinitely many pairs (n, k)
with n ≥ 2k, no small prime factors in C(n,k), and deficiency exactly 1? -/
def ErdosProblem1093i : Prop :=
  Set.Infinite { p : ℕ × ℕ |
    let k := p.1; let n := p.2
    2 * k ≤ n ∧ NoSmallPrimeFactors n k ∧ deficiency n k = 1 }

/-- **Erdős Problem #1093 Part (ii)**: Are there only finitely many pairs (n, k)
with n ≥ 2k, no small prime factors in C(n,k), and deficiency > 1? -/
def ErdosProblem1093ii : Prop :=
  Set.Finite { p : ℕ × ℕ |
    let k := p.1; let n := p.2
    2 * k ≤ n ∧ NoSmallPrimeFactors n k ∧ deficiency n k > 1 }

/-- The combined problem. -/
def ErdosProblem1093 : Prop :=
  ErdosProblem1093i ∧ ErdosProblem1093ii

/-
## Section IV: Known Examples
-/

/-- C(7,3) = 35 has deficiency 1: among {7, 6, 5}, only 6 is 3-smooth. -/
theorem deficiency_7_3 : deficiency 7 3 = 1 := by native_decide

/-- C(13,4) = 715 has deficiency 1. -/
theorem deficiency_13_4 : deficiency 13 4 = 1 := by native_decide

/-- C(284,28) has the highest known deficiency: 9. -/
theorem deficiency_284_28 : deficiency 284 28 = 9 := by native_decide

/-
## Section V: Upper Bound
-/

/-- Erdős-Lacampagne-Selfridge (1993): if deficiency ≥ 1 then n ≪ 2^k · √k. -/
axiom els_upper_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ n k : ℕ, 2 * k ≤ n →
    NoSmallPrimeFactors n k → deficiency n k ≥ 1 →
    (n : ℝ) ≤ C * 2 ^ k * Real.sqrt k

/-- Additional verified deficiency-1 examples spanning k = 4..19.
    These replace the former axiom claiming ≥ 58 such examples for n ≤ 10⁵.
    Each is individually verified by native_decide. -/
theorem deficiency_14_4 : deficiency 14 4 = 1 := by native_decide
theorem deficiency_23_5 : deficiency 23 5 = 1 := by native_decide
theorem deficiency_62_6 : deficiency 62 6 = 1 := by native_decide
theorem deficiency_143_7 : deficiency 143 7 = 1 := by native_decide
theorem deficiency_89_8 : deficiency 89 8 = 1 := by native_decide
theorem deficiency_319_9 : deficiency 319 9 = 1 := by native_decide
theorem deficiency_94_10 : deficiency 94 10 = 1 := by native_decide
theorem deficiency_1391_11 : deficiency 1391 11 = 1 := by native_decide
theorem deficiency_188_12 : deficiency 188 12 = 1 := by native_decide
theorem deficiency_719_14 : deficiency 719 14 = 1 := by native_decide
theorem deficiency_719_15 : deficiency 719 15 = 1 := by native_decide
theorem deficiency_566_16 : deficiency 566 16 = 1 := by native_decide
theorem deficiency_2099_19 : deficiency 2099 19 = 1 := by native_decide

/-
## Section VI: Verified Deficiency > 1 Examples

These are the known examples from ELS (1988) and computational searches.
The conjecture asks whether there are only finitely many with deficiency > 1.
-/

/-- C(44,8): deficiency 2. -/
theorem deficiency_44_8 : deficiency 44 8 = 2 := by native_decide
/-- C(74,10): deficiency 2. -/
theorem deficiency_74_10 : deficiency 74 10 = 2 := by native_decide
/-- C(174,12): deficiency 2. -/
theorem deficiency_174_12 : deficiency 174 12 = 2 := by native_decide
/-- C(239,14): deficiency 2. -/
theorem deficiency_239_14 : deficiency 239 14 = 2 := by native_decide
/-- C(46,10): deficiency 3. -/
theorem deficiency_46_10 : deficiency 46 10 = 3 := by native_decide
/-- C(47,10): deficiency 3. -/
theorem deficiency_47_10 : deficiency 47 10 = 3 := by native_decide
/-- C(241,16): deficiency 3. -/
theorem deficiency_241_16 : deficiency 241 16 = 3 := by native_decide
/-- C(1119,27): deficiency 3. -/
theorem deficiency_1119_27 : deficiency 1119 27 = 3 := by native_decide
/-- C(2105,25): deficiency 3. -/
theorem deficiency_2105_25 : deficiency 2105 25 = 3 := by native_decide
/-- C(6459,33): deficiency 3. -/
theorem deficiency_6459_33 : deficiency 6459 33 = 3 := by native_decide
/-- C(47,11): deficiency 4 — highest known deficiency for small parameters. -/
theorem deficiency_47_11 : deficiency 47 11 = 4 := by native_decide

/-
## Section VII: Structural Properties
-/

/-- If n - i has a prime factor > k, it is not k-smooth,
so it does not contribute to the deficiency. -/
theorem large_factor_no_contribution (n k i : ℕ) (hi : i < k)
    (p : ℕ) (hp : p.Prime) (hpk : p > k) (hd : p ∣ n - i) :
    ¬IsKSmooth k (n - i) := by
  intro h
  have := h p hp hd
  omega

/-- Trivial upper bound: the deficiency is at most k. -/
theorem deficiency_le (n k : ℕ) : deficiency n k ≤ k := by
  unfold deficiency
  calc Finset.card (Finset.filter (fun i => IsKSmooth k (n - i)) (Finset.range k))
      ≤ Finset.card (Finset.range k) := Finset.card_filter_le _ _
    _ = k := Finset.card_range k

/-- 1 is k-smooth for any k (vacuously: 1 has no prime factors). -/
theorem isKSmooth_one (k : ℕ) : IsKSmooth k 1 := by
  intro p hp hd
  have h2 := hp.two_le
  have h1 := Nat.le_of_dvd one_pos hd
  omega

/-- 0 is not k-smooth for any k (every prime divides 0). -/
theorem not_isKSmooth_zero (k : ℕ) : ¬IsKSmooth k 0 := by
  intro h
  obtain ⟨p, hpk, hp⟩ := Nat.exists_infinite_primes (k + 1)
  exact absurd (h p hp (dvd_zero p)) (by omega)

/-- IsKSmooth is monotone in k: a k-smooth number is also j-smooth for j ≥ k. -/
theorem isKSmooth_mono {k j : ℕ} (hkj : k ≤ j) {m : ℕ} (hm : IsKSmooth k m) :
    IsKSmooth j m :=
  fun p hp hd => (hm p hp hd).trans hkj

/-- A prime p is k-smooth if and only if p ≤ k. -/
theorem isKSmooth_prime_iff {k p : ℕ} (hp : p.Prime) : IsKSmooth k p ↔ p ≤ k := by
  constructor
  · intro h; exact h p hp dvd_rfl
  · intro hpk q hq hqp
    rcases hp.eq_one_or_self_of_dvd q hqp with h1 | h2
    · exact absurd h1 hq.one_lt.ne'
    · rw [h2]; exact hpk

/-- A product of k-smooth numbers is k-smooth. -/
theorem isKSmooth_mul {k a b : ℕ} (ha : IsKSmooth k a) (hb : IsKSmooth k b) :
    IsKSmooth k (a * b) :=
  fun p hp hd => (hp.dvd_mul.mp hd).elim (ha p hp) (hb p hp)

/-- A power of a k-smooth number is k-smooth. -/
theorem isKSmooth_pow {k a : ℕ} (ha : IsKSmooth k a) (n : ℕ) : IsKSmooth k (a ^ n) :=
  fun p hp hd => ha p hp (hp.dvd_of_dvd_pow hd)

/-- A divisor of a k-smooth number is k-smooth. -/
theorem isKSmooth_of_dvd {k a b : ℕ} (hab : a ∣ b) (hb : IsKSmooth k b) : IsKSmooth k a :=
  fun p hp hd => hb p hp (hd.trans hab)

/-- k-smoothness is characterized by the prime factorization (for positive m). -/
theorem isKSmooth_iff_primeFactors {k m : ℕ} (hm : m ≠ 0) :
    IsKSmooth k m ↔ ∀ p ∈ m.primeFactors, p ≤ k := by
  constructor
  · intro h p hmem
    obtain ⟨hp, hd, _⟩ := Nat.mem_primeFactors.mp hmem
    exact h p hp hd
  · intro h p hp hd
    exact h p (Nat.mem_primeFactors.mpr ⟨hp, hd, hm⟩)

/-- If n - i is k-smooth for some i < k, then the deficiency is positive. -/
theorem deficiency_pos_of_smooth {n k : ℕ} {i : ℕ} (hi : i < k)
    (hsmooth : IsKSmooth k (n - i)) : 0 < deficiency n k := by
  unfold deficiency
  apply Finset.card_pos.mpr
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hsmooth⟩⟩
