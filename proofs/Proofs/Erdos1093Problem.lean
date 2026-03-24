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

/-- At least 58 examples with deficiency 1 are known for n ≤ 10⁵. -/
axiom many_deficiency_one_examples :
  58 ≤ Finset.card (Finset.filter
    (fun p : ℕ × ℕ => 2 * p.1 ≤ p.2 ∧ deficiency p.2 p.1 = 1)
    (Finset.range 100 ×ˢ Finset.range 100001))

/-
## Section VI: Structural Properties
-/

/-- If n - i has a prime factor > k, it is not k-smooth,
so it does not contribute to the deficiency. -/
theorem large_factor_no_contribution (n k i : ℕ) (hi : i < k)
    (p : ℕ) (hp : p.Prime) (hpk : p > k) (hd : p ∣ n - i) :
    ¬IsKSmooth k (n - i) := by
  intro h
  have := h p hp hd
  omega
