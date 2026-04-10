/-
Erdős Problem #1141: Coprime-Square Subtraction Primes

Are there infinitely many n such that n - k² is prime for all k
with gcd(n, k) = 1 and k² < n?

Known results:
- The known values satisfying this are: 3, 4, 6, 8, 12, 14, 18, 20,
  24, 30, 32, 38, 42, 48, 54, 60, 62, 68, 72, 80, 84, 90, 98, 108,
  110, 132, 138, 140, 150, 180, 182, 198, 252, 318, 360, 398, 468,
  570, 572, 930, 1722 (OEIS A214583)
- No further terms exist below 10^10
- ChatGPT-Tang proved the count in [1,N] is O(N^{1/2+o(1)})

Status: SOLVED (Alexeev-Putterman-Sawhney-Sellke-Valiant 2026,
arXiv:2604.06609). Answer: NO, only finitely many such n exist.
More generally, for each fixed a ≥ 1, only finitely many n have
n - ak² prime for all coprime k with ak² < n. Proof deduces this
from Pollack's theorem (2017) on small prime quadratic residues.
The result is ineffective (Siegel's theorem); computationally,
1722 appears to be the largest good value for a=1.

Reference: https://erdosproblems.com/1141
-/

import Mathlib

-- ## Core Definition

/-- n satisfies the Erdős-1141 property if for every k with k² < n and
    gcd(n,k) = 1, the value n - k² is prime.
    We bound the quantifier by Finset.range n to ensure decidability. -/
def IsErdos1141Good (n : ℕ) : Prop :=
  ∀ k ∈ Finset.range n, k ^ 2 < n → Nat.Coprime n k → (n - k ^ 2).Prime

instance (n : ℕ) : Decidable (IsErdos1141Good n) := by
  unfold IsErdos1141Good; infer_instance

/-- Equivalent unbounded formulation (for mathematical statements). -/
theorem isErdos1141Good_iff_unbounded (n : ℕ) :
    IsErdos1141Good n ↔
    (∀ k : ℕ, k ^ 2 < n → Nat.Coprime n k → (n - k ^ 2).Prime) := by
  unfold IsErdos1141Good
  constructor
  · intro h k hk hcop
    exact h k (Finset.mem_range.mpr (by nlinarith [sq_nonneg k])) hk hcop
  · intro h k _ hk hcop
    exact h k hk hcop

-- ## Computational Verification of Small Examples

/-- n = 3 satisfies the property: only k=1 qualifies, and 3 - 1 = 2 is prime. -/
theorem good_3 : IsErdos1141Good 3 := by native_decide

/-- n = 4 satisfies the property. -/
theorem good_4 : IsErdos1141Good 4 := by native_decide

/-- n = 6 satisfies the property. -/
theorem good_6 : IsErdos1141Good 6 := by native_decide

/-- n = 8 satisfies the property. -/
theorem good_8 : IsErdos1141Good 8 := by native_decide

/-- n = 12 satisfies the property. -/
theorem good_12 : IsErdos1141Good 12 := by native_decide

/-- n = 14 satisfies the property. -/
theorem good_14 : IsErdos1141Good 14 := by native_decide

/-- n = 18 satisfies the property. -/
theorem good_18 : IsErdos1141Good 18 := by native_decide

/-- n = 20 satisfies the property. -/
theorem good_20 : IsErdos1141Good 20 := by native_decide

-- ## Counterexamples: values that do NOT satisfy the property

/-- n = 5 does not satisfy the property: k=2, gcd(5,2)=1, 5-4=1 not prime. -/
theorem not_good_5 : ¬ IsErdos1141Good 5 := by native_decide

/-- n = 7 does not satisfy the property. -/
theorem not_good_7 : ¬ IsErdos1141Good 7 := by native_decide

/-- n = 9 does not satisfy the property. -/
theorem not_good_9 : ¬ IsErdos1141Good 9 := by native_decide

/-- n = 10 does not satisfy the property. -/
theorem not_good_10 : ¬ IsErdos1141Good 10 := by native_decide

/-- n = 16 does not satisfy the property: 16-1=15 not prime. -/
theorem not_good_16 : ¬ IsErdos1141Good 16 := by native_decide

-- ## Structural Properties

/-- n = 0 trivially satisfies the property (vacuously true). -/
theorem good_0 : IsErdos1141Good 0 := by
  intro k hk; simp at hk

/-- n = 1 does not satisfy the property: k=0, 0²=0 < 1, gcd(1,0)=1,
    but 1-0=1 is not prime. -/
theorem not_good_1 : ¬ IsErdos1141Good 1 := by native_decide

/-- n = 2 does not satisfy the property: k=1, gcd(2,1)=1, 2-1=1 not prime. -/
theorem not_good_2 : ¬ IsErdos1141Good 2 := by native_decide

/-- If n ≥ 2 is good, then n - 1 is prime (taking k = 1, gcd(n,1) = 1). -/
theorem good_implies_pred_prime (n : ℕ) (hn : 2 ≤ n) (hg : IsErdos1141Good n) :
    (n - 1).Prime := by
  rw [isErdos1141Good_iff_unbounded] at hg
  have := hg 1 (by omega) (Nat.Coprime.symm (Nat.coprime_one_left n))
  simpa using this

/-- All good values n ≥ 4 are even. Proof: n-1 must be prime, and if n is odd
    then n-1 is even and ≥ 3, hence composite (only even prime is 2). -/
theorem good_ge4_even (n : ℕ) (hn : 4 ≤ n) (hg : IsErdos1141Good n) : 2 ∣ n := by
  by_contra hodd
  have hpred := good_implies_pred_prime n (by omega) hg
  have heven : 2 ∣ (n - 1) := by omega
  rcases hpred.eq_one_or_self_of_dvd 2 heven with h | h <;> omega

-- ## The Open Conjecture

/-- Erdős Problem #1141: SOLVED — only finitely many n satisfy the property.
    Alexeev-Putterman-Sawhney-Sellke-Valiant (2026, arXiv:2604.06609) proved
    this via Pollack's theorem on small prime quadratic residues.
    The result is ineffective due to Siegel's theorem. -/
axiom erdos_1141_finitely_many :
  ∃ N : ℕ, ∀ n : ℕ, n ≥ N → ¬ IsErdos1141Good n

-- ## Known Finite Results

/-- The OEIS sequence A214583: known good values up to 1722. -/
def knownGoodValues : List ℕ :=
  [3, 4, 6, 8, 12, 14, 18, 20, 24, 30, 32, 38, 42, 48, 54, 60,
   62, 68, 72, 80, 84, 90, 98, 108, 110, 132, 138, 140, 150, 180,
   182, 198, 252, 318, 360, 398, 468, 570, 572, 930, 1722]

/-- There are exactly 41 known good values. -/
theorem knownGoodValues_length : knownGoodValues.length = 41 := by native_decide

-- ## Larger verified examples (using native_decide for speed)

/-- n = 24 satisfies the property. -/
theorem good_24 : IsErdos1141Good 24 := by native_decide

/-- n = 30 satisfies the property. -/
theorem good_30 : IsErdos1141Good 30 := by native_decide

/-- n = 60 satisfies the property. -/
theorem good_60 : IsErdos1141Good 60 := by native_decide

/-- n = 90 satisfies the property. -/
theorem good_90 : IsErdos1141Good 90 := by native_decide

/-- n = 110 satisfies the property. -/
theorem good_110 : IsErdos1141Good 110 := by native_decide

/-- n = 198 satisfies the property. -/
theorem good_198 : IsErdos1141Good 198 := by native_decide

/-- n = 252 satisfies the property. -/
theorem good_252 : IsErdos1141Good 252 := by native_decide

/-- n = 570 satisfies the property. -/
theorem good_570 : IsErdos1141Good 570 := by native_decide

/-- The value n = 1722 (largest known) satisfies the property. -/
theorem good_1722 : IsErdos1141Good 1722 := by native_decide

-- ## Unified Verification

/-- All 41 known OEIS A214583 values satisfy the Erdős-1141 property. -/
theorem all_known_good : ∀ n ∈ knownGoodValues, IsErdos1141Good n := by native_decide

-- ## Complete Classification to n = 100

/-- The exhaustive list of good values in {0, …, 100}. -/
def goodValuesUpTo100 : List ℕ :=
  [0, 3, 4, 6, 8, 12, 14, 18, 20, 24, 30, 32, 38, 42, 48, 54, 60, 62, 68, 72, 80, 84, 90, 98]

/-- Complete classification: the good values in {0, …, 100} are exactly `goodValuesUpTo100`. -/
theorem classification_100 :
    (Finset.range 101).filter IsErdos1141Good = goodValuesUpTo100.toFinset := by native_decide

/-- There are exactly 24 good values in {0, …, 100}. -/
theorem good_count_100 :
    ((Finset.range 101).filter IsErdos1141Good).card = 24 := by native_decide

-- ## Structural Corollaries

/-- No prime ≥ 5 satisfies the Erdős-1141 property.
    Proof: primes ≥ 5 are odd, but good values ≥ 4 must be even. -/
theorem good_not_prime_ge5 (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ¬ IsErdos1141Good p := by
  intro hg
  have heven := good_ge4_even p (by omega) hg
  rcases hp.eq_one_or_self_of_dvd 2 heven with h | h <;> omega

/-- 3 is the only odd good value ≥ 3. -/
theorem good_odd_eq_three (n : ℕ) (hn : 3 ≤ n) (hg : IsErdos1141Good n)
    (hodd : ¬ 2 ∣ n) : n = 3 := by
  by_contra h
  exact hodd (good_ge4_even n (by omega) hg)

/-- If n ≥ 10 is good and coprime to 3, then n − 9 is also prime. -/
theorem good_coprime3_sub9_prime (n : ℕ) (hn : 10 ≤ n)
    (hg : IsErdos1141Good n) (hcop : Nat.Coprime n 3) :
    (n - 9).Prime := by
  rw [isErdos1141Good_iff_unbounded] at hg
  exact hg 3 (by omega) hcop
