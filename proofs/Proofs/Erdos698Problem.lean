/-
Erdős Problem #698: GCDs of Binomial Coefficients

Source: https://erdosproblems.com/698
Status: SOLVED (Bergman 2011)

Statement:
Is there some h(n) → ∞ such that for all 2 ≤ i < j ≤ n/2,
gcd(C(n,i), C(n,j)) ≥ h(n)?

Background:
- Erdős and Szekeres (1978) posed this problem
- They observed: gcd(C(n,i), C(n,j)) ≥ C(n,i)/C(j,i) ≥ 2^i
- In particular, the GCD is always > 1
- This bound is sharp for i=1, j=p, n=2p

Answer: YES (Bergman 2011)

Key Result:
Bergman proved: gcd(C(n,i), C(n,j)) ≫ n^{1/2} · 2^i / i^{3/2}
where the implied constant is absolute.

References:
- Erdős, Szekeres (1978): Original problem
- Bergman (2011): "On common divisors of multinomial coefficients"
  Bull. Aust. Math. Soc. (2011), 138-157.
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Nat

namespace Erdos698

/-
## Part I: Basic Definitions
-/

/--
**Binomial Coefficient C(n,k):**
The number of ways to choose k elements from n elements.
In Mathlib this is `Nat.choose n k`.
-/
def binom (n k : ℕ) : ℕ := Nat.choose n k

/--
**GCD of Binomial Coefficients:**
The greatest common divisor of two binomial coefficients.
-/
def binomGcd (n i j : ℕ) : ℕ := Nat.gcd (binom n i) (binom n j)

/-
## Part II: The Erdős-Szekeres Observation
-/

/--
**Valid Index Pair:**
A pair (i, j) is valid for n if 2 ≤ i < j ≤ n/2.
-/
def isValidPair (n i j : ℕ) : Prop :=
  2 ≤ i ∧ i < j ∧ j ≤ n / 2

/--
**Erdős-Szekeres Lower Bound (1978):**
For valid pairs (i,j), gcd(C(n,i), C(n,j)) ≥ C(n,i)/C(j,i) ≥ 2^i.

This shows the GCD is always at least 2 when i ≥ 1.
-/
/--
**Exponential Lower Bound:**
The Erdős-Szekeres bound implies gcd ≥ 2^i.
-/
axiom erdos_szekeres_exponential (n i j : ℕ) (h : isValidPair n i j) :
  binomGcd n i j ≥ 2^i

/--
**GCD is Always > 1:**
As a corollary, the GCD of two distinct binomial coefficients
(with indices in the valid range) is always greater than 1.
-/
theorem gcd_always_gt_one (n i j : ℕ) (h : isValidPair n i j) :
    binomGcd n i j > 1 := by
  have hi : 2 ≤ i := h.1
  have hexp := erdos_szekeres_exponential n i j h
  calc binomGcd n i j ≥ 2^i := hexp
    _ ≥ 2^2 := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hi
    _ = 4 := by norm_num
    _ > 1 := by norm_num

/-
## Part III: Sharpness of the Erdős-Szekeres Bound
-/

/--
**Sharpness Example:**
The Erdős-Szekeres bound is sharp for i=1, j=p, n=2p
where p is prime.

In this case, gcd(C(2p,1), C(2p,p)) = 2p/C(p,1) = 2p/p = 2 = 2^1.
-/
/-
## Part IV: The Main Question
-/

/--
**Unbounded Growth Function:**
A function h : ℕ → ℕ tends to infinity.
-/
def tendsToInfinity (h : ℕ → ℕ) : Prop :=
  ∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N, h n > M

/--
**The Erdős-Szekeres Question (1978):**
Is there some h(n) → ∞ such that for all valid pairs (i,j),
gcd(C(n,i), C(n,j)) ≥ h(n)?

In other words: does the minimum GCD over all valid pairs grow unboundedly?
-/
def erdos698Question : Prop :=
  ∃ h : ℕ → ℕ, tendsToInfinity h ∧
    ∀ n i j : ℕ, isValidPair n i j → binomGcd n i j ≥ h n

/-
## Part V: Bergman's Theorem (2011)
-/

/--
**Bergman's Bound:**
For any valid pair (i,j), the GCD satisfies:
gcd(C(n,i), C(n,j)) ≥ c · n^{1/2} · 2^i / i^{3/2}
for some absolute constant c > 0.
-/
/--
**Bergman's Theorem (Main Result):**
For any valid pair, gcd ≫ n^{1/2} · 2^i / i^{3/2}.
Taking i = 2 (the minimum), this gives gcd ≥ c · n^{1/2} · 4 / 2^{3/2} ≈ c · n^{1/2}.
-/
/--
**Minimum GCD Growth:**
The minimum GCD over all valid pairs grows like Ω(√n).
-/
axiom min_gcd_growth :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 4 →
    ∀ i j : ℕ, isValidPair n i j → (binomGcd n i j : ℝ) ≥ c * Real.sqrt n

/-
## Part VI: Resolution of the Problem
-/

/--
**The Growth Function:**
We can take h(n) = ⌊c · √n⌋ for appropriate c.
-/
noncomputable def bergmanH (c : ℝ) (n : ℕ) : ℕ :=
  ⌊c * Real.sqrt n⌋₊

/--
**h(n) → ∞:**
The function h(n) = ⌊c · √n⌋ tends to infinity.
-/
theorem bergmanH_unbounded (c : ℝ) (hc : c > 0) : tendsToInfinity (bergmanH c) := by
  intro M
  -- Take N large enough that c · √N > M + 1
  refine ⟨⌈((↑(M + 1) : ℝ) / c) ^ 2⌉₊, fun n hn => ?_⟩
  show M < ⌊c * Real.sqrt ↑n⌋₊
  -- It suffices to show ↑(M + 1) ≤ c * √n
  suffices h : (↑(M + 1) : ℝ) ≤ c * Real.sqrt ↑n by
    have := (Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ c * Real.sqrt ↑n)).mpr h
    omega
  -- Show c * √n ≥ M + 1 via (M+1)/c ≤ √n
  have hdc_nn : (0 : ℝ) ≤ (↑(M + 1) : ℝ) / c := by positivity
  calc (↑(M + 1) : ℝ)
      = c * ((↑(M + 1) : ℝ) / c) := by field_simp
    _ ≤ c * Real.sqrt ↑n := by
        apply mul_le_mul_of_nonneg_left _ hc.le
        rw [← Real.sqrt_sq hdc_nn]
        exact Real.sqrt_le_sqrt (le_trans (Nat.le_ceil _) (by exact_mod_cast hn))

/--
**Affirmative Answer:**
Bergman's theorem implies the answer to Erdős Problem #698 is YES.
-/
theorem erdos698_answer : erdos698Question := by
  obtain ⟨c, hc, hbound⟩ := min_gcd_growth
  use bergmanH c
  constructor
  · exact bergmanH_unbounded c hc
  · intro n i j hvalid
    -- From isValidPair: 2 ≤ i < j ≤ n/2, so n ≥ 6 ≥ 4
    have hn4 : n ≥ 4 := by
      have := hvalid.1; have := hvalid.2.1; have := hvalid.2.2; omega
    -- Bergman gives (binomGcd n i j : ℝ) ≥ c * √n
    have hreal := hbound n hn4 i j hvalid
    -- ⌊c * √n⌋₊ ≤ c * √n ≤ binomGcd n i j
    show bergmanH c n ≤ binomGcd n i j
    show ⌊c * Real.sqrt ↑n⌋₊ ≤ binomGcd n i j
    exact_mod_cast (Nat.floor_le (by positivity : (0 : ℝ) ≤ c * Real.sqrt ↑n)).trans hreal

/-
## Part VII: Implications and Generalizations
-/

/-
**Divisibility Observation:**
The fact that gcd(C(n,i), C(n,j)) > 1 for all valid pairs
shows that the middle binomial coefficients share common factors.
This is related to the arithmetic structure of Pascal's triangle.
-/

/-
**Pascal's Triangle Primes:**
The only primes in Pascal's triangle (besides the edges) are
the entries C(p, k) where p is prime and 0 < k < p.
These are all equal to p · (p-1)! / (k! (p-k)!) which is divisible by p.
-/

/-
**Multinomial Generalization:**
Bergman actually proved a more general result about
common divisors of multinomial coefficients.
-/

/-
**Connection to Number Theory:**
The GCD of binomial coefficients relates to:
1. p-adic valuations of factorials (Kummer's theorem)
2. Lucas' theorem on binomial coefficients mod p
3. Distribution of prime factors in products
-/

/-
## Part VIII: Kummer's Theorem Connection
-/

/--
**Kummer's Theorem:**
The largest power of prime p dividing C(m+n, m) equals
the number of carries in adding m and n in base p.
-/
/- kummer_theorem: the largest power of prime p dividing C(m+n, m)
  equals the number of carries in adding m and n in base p. -/

/- **Lucas' Theorem:** C(m, n) mod p can be computed from the
  base-p digits of m and n (modular reduction of binomial coefficients). -/

/-
## Part IX: Summary
-/

/--
**Summary of Known Results:**
-/
theorem erdos_698_summary :
    -- Erdős-Szekeres bound: gcd ≥ 2^i
    (∀ n i j : ℕ, isValidPair n i j → binomGcd n i j ≥ 2^i) ∧
    -- GCD is always > 1
    (∀ n i j : ℕ, isValidPair n i j → binomGcd n i j > 1) ∧
    -- Answer is YES
    erdos698Question := by
  constructor
  · exact erdos_szekeres_exponential
  constructor
  · exact gcd_always_gt_one
  · exact erdos698_answer

/--
**Erdős Problem #698: SOLVED**

Is there h(n) → ∞ such that gcd(C(n,i), C(n,j)) ≥ h(n)
for all valid pairs 2 ≤ i < j ≤ n/2?

Answer: YES (Bergman 2011)

The minimum GCD grows like Ω(√n), specifically:
gcd(C(n,i), C(n,j)) ≫ n^{1/2} · 2^i / i^{3/2}
-/
theorem erdos_698 : erdos698Question := erdos698_answer

end Erdos698
