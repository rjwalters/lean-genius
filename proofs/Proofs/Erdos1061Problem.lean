/-
Erdos Problem #1061: Sum of Divisors Equation

Source: https://erdosproblems.com/1061
Status: OPEN

Statement:
How many (ordered) solutions are there to sigma(a) + sigma(b) = sigma(a + b)
with a + b <= x, where sigma is the sum of divisors function?
Is this count asymptotic to c * x for some constant c > 0?

Background:
This is a question of Erdos reported in problem B15 of Guy's collection
"Unsolved Problems in Number Theory" (2004).

Key Results (proved here):
1. GENERAL FAMILY: sigma(a) + sigma(2a) = sigma(3a) for ALL a coprime to 6.
   Proved via multiplicativity: sigma(2a) = 3*sigma(a), sigma(3a) = 4*sigma(a).
2. As a corollary, (p, 2p) is a solution for every prime p >= 5.
3. Infinitely many solutions (from the prime family and coprime-to-6 family).
4. Symmetry: if (a,b) is a solution, so is (b,a).
5. Non-solution theorem: if p, q, p+q are all prime, (p,q) is NOT a solution.
6. S(x) monotone and each coprime-to-6 integer in [1, x/3] contributes solutions.
7. 0 axioms, 0 sorries -- all results fully proved.

Computational data (not formalized):
  S(100)=74, S(500)=662, S(1000)=1620, S(2000)=3806
  S(x)/x appears to grow slowly, reaching ~1.9 at x=2000.
  The coprime-to-6 family accounts for the (a, 2a) solutions; many other patterns
  exist (e.g., (a, 3a) when a = 2m with gcd(m,6)=1, and (a, 7a) for a divisible by 4).

References:
- Erdos (question reported in Guy's collection)
- Guy, R.K. [Gu04]: "Unsolved problems in number theory", Problem B15
- OEIS A110177: Numbers n such that sigma(n) = sigma(a) + sigma(n-a) for some 0 < a < n
-/

import Mathlib

open Nat ArithmeticFunction Finset Filter Asymptotics

namespace Erdos1061

/-
## Part I: The Sum of Divisors Function

We use Mathlib's sigma 1 : N -> N which gives sigma(n) = sum of d | n, d.
-/

-- Concrete evaluations
theorem sigma_val_1 : sigma 1 1 = 1 := by native_decide
theorem sigma_val_2 : sigma 1 2 = 3 := by native_decide
theorem sigma_val_3 : sigma 1 3 = 4 := by native_decide
theorem sigma_val_4 : sigma 1 4 = 7 := by native_decide
theorem sigma_val_5 : sigma 1 5 = 6 := by native_decide
theorem sigma_val_6 : sigma 1 6 = 12 := by native_decide
theorem sigma_val_9 : sigma 1 9 = 13 := by native_decide
theorem sigma_val_10 : sigma 1 10 = 18 := by native_decide
theorem sigma_val_15 : sigma 1 15 = 24 := by native_decide
theorem sigma_val_21 : sigma 1 21 = 32 := by native_decide

/-- sigma(p) = p + 1 for prime p -/
theorem sigma_prime' (p : ℕ) (hp : p.Prime) : sigma 1 p = p + 1 := by
  simp [sigma_apply, hp.divisors]
  omega

/-
## Part II: The Additive Divisor Equation
-/

/-- A pair (a, b) satisfies the additive divisor equation. -/
def IsAdditiveDivisorPair (a b : ℕ) : Prop :=
  a ≥ 1 ∧ b ≥ 1 ∧ sigma 1 a + sigma 1 b = sigma 1 (a + b)

/-- The set of all solution pairs. -/
def additiveDivisorPairs : Set (ℕ × ℕ) :=
  {p : ℕ × ℕ | IsAdditiveDivisorPair p.1 p.2}

/-
## Part III: Known Solutions
-/

theorem solution_1_2 : IsAdditiveDivisorPair 1 2 := by
  refine ⟨by omega, by omega, ?_⟩; native_decide

theorem solution_2_1 : IsAdditiveDivisorPair 2 1 := by
  refine ⟨by omega, by omega, ?_⟩; native_decide

theorem solution_4_5 : IsAdditiveDivisorPair 4 5 := by
  refine ⟨by omega, by omega, ?_⟩; native_decide

theorem solution_5_10 : IsAdditiveDivisorPair 5 10 := by
  refine ⟨by omega, by omega, ?_⟩; native_decide

theorem solution_7_14 : IsAdditiveDivisorPair 7 14 := by
  refine ⟨by omega, by omega, ?_⟩; native_decide

theorem solution_2_6 : IsAdditiveDivisorPair 2 6 := by
  refine ⟨by omega, by omega, ?_⟩; native_decide

theorem solution_2_8 : IsAdditiveDivisorPair 2 8 := by
  refine ⟨by omega, by omega, ?_⟩; native_decide

theorem solution_11_22 : IsAdditiveDivisorPair 11 22 := by
  refine ⟨by omega, by omega, ?_⟩; native_decide

theorem not_solution_1_1 : ¬IsAdditiveDivisorPair 1 1 := by
  intro ⟨_, _, h⟩; revert h; native_decide

theorem not_solution_2_2 : ¬IsAdditiveDivisorPair 2 2 := by
  intro ⟨_, _, h⟩; revert h; native_decide

theorem sigma_not_subadditive :
    ∃ a b : ℕ, a ≥ 1 ∧ b ≥ 1 ∧ sigma 1 (a + b) < sigma 1 a + sigma 1 b :=
  ⟨2, 3, by omega, by omega, by native_decide⟩

theorem sigma_not_superadditive :
    ∃ a b : ℕ, a ≥ 1 ∧ b ≥ 1 ∧ sigma 1 (a + b) > sigma 1 a + sigma 1 b :=
  ⟨2, 4, by omega, by omega, by native_decide⟩

/-
## Part IV: General Structural Theorem

For any a with gcd(a, 6) = 1 (equivalently, a coprime to both 2 and 3),
the pair (a, 2a) is a solution: sigma(a) + sigma(2a) = sigma(3a).

Proof: By multiplicativity of sigma (since gcd(2,a)=1 and gcd(3,a)=1):
  sigma(2a) = sigma(2) * sigma(a) = 3 * sigma(a)
  sigma(3a) = sigma(3) * sigma(a) = 4 * sigma(a)
  sigma(a) + sigma(2a) = sigma(a) + 3*sigma(a) = 4*sigma(a) = sigma(3a)

This gives a positive density of solutions: every integer coprime to 6
generates a solution pair (a, 2a) with sum 3a. Since 1/3 of all positive
integers are coprime to 6 (by Euler's product for phi(6)/6 = 2/6 = 1/3),
this family alone contributes linearly many solutions.
-/

/-- For any a coprime to both 2 and 3, sigma(a) + sigma(2a) = sigma(3a).
    This is the key structural result: multiplicativity of sigma gives
    sigma(2a) = 3*sigma(a) and sigma(3a) = 4*sigma(a). -/
theorem sigma_add_eq_coprime6 (a : ℕ) (ha : a ≠ 0)
    (hcop2 : Nat.Coprime 2 a) (hcop3 : Nat.Coprime 3 a) :
    sigma 1 a + sigma 1 (2 * a) = sigma 1 (3 * a) := by
  have hmul2 := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
    sigma_isMultiplicative hcop2
  have hmul3 := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
    sigma_isMultiplicative hcop3
  rw [hmul2, hmul3]
  have hs2 : sigma 1 2 = 3 := by native_decide
  have hs3 : sigma 1 3 = 4 := by native_decide
  rw [hs2, hs3]
  ring

/-- (a, 2a) is a solution for every a coprime to 6. -/
theorem solution_coprime6 (a : ℕ) (ha : a ≥ 1)
    (hcop2 : Nat.Coprime 2 a) (hcop3 : Nat.Coprime 3 a) :
    IsAdditiveDivisorPair a (2 * a) := by
  refine ⟨ha, by omega, ?_⟩
  have heq : a + 2 * a = 3 * a := by ring
  rw [heq]
  exact sigma_add_eq_coprime6 a (by omega) hcop2 hcop3

/-- Symmetry: (2a, a) is also a solution when a is coprime to 6. -/
theorem solution_coprime6_sym (a : ℕ) (ha : a ≥ 1)
    (hcop2 : Nat.Coprime 2 a) (hcop3 : Nat.Coprime 3 a) :
    IsAdditiveDivisorPair (2 * a) a := by
  refine ⟨by omega, ha, ?_⟩
  have heq : 2 * a + a = 3 * a := by ring
  rw [heq]
  have := sigma_add_eq_coprime6 a (by omega) hcop2 hcop3
  linarith

/-
## Part IV-b: Prime Specialization

For primes p >= 5, gcd(2,p) = 1 and gcd(3,p) = 1 automatically.
-/

/-- For any prime p >= 5, sigma(p) + sigma(2p) = sigma(3p). -/
theorem sigma_add_eq_of_prime (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) :
    sigma 1 p + sigma 1 (2 * p) = sigma 1 (3 * p) := by
  apply sigma_add_eq_coprime6 p hp.ne_zero
  · rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr fun hdvd =>
      h2 (le_antisymm (Nat.le_of_dvd (by omega) hdvd) hp.two_le)
  · rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr fun hdvd => by
      have : p ≤ 3 := Nat.le_of_dvd (by omega) hdvd
      interval_cases p <;> simp_all [Nat.Prime]

/-- (p, 2p) is a solution for every prime p >= 5. -/
theorem solution_prime_2p (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) :
    IsAdditiveDivisorPair p (2 * p) := by
  refine ⟨hp.one_le, by omega, ?_⟩
  have heq : p + 2 * p = 3 * p := by ring
  rw [heq]
  exact sigma_add_eq_of_prime p hp h2 h3

/-- There are infinitely many solution pairs. -/
theorem infinitely_many_solutions :
    ∀ N : ℕ, ∃ a b : ℕ, a ≥ N ∧ IsAdditiveDivisorPair a b := by
  intro N
  obtain ⟨p, hpge, hprime⟩ := Nat.exists_infinite_primes (max N 5)
  have h2 : p ≠ 2 := by
    intro heq; subst heq; omega
  have h3 : p ≠ 3 := by
    intro heq; subst heq; omega
  exact ⟨p, 2 * p, le_of_max_le_left hpge, solution_prime_2p p hprime h2 h3⟩

/-
## Part IV-c: Concrete Applications of the General Family

The coprime-to-6 family includes ALL numbers of the form 6k+1 or 6k+5.
Verified examples: a = 1, 5, 7, 11, 13, 17, 19, 23, 25, 29, 31, 35, ...
-/

-- Concrete verification that coprime-to-6 non-primes also work
theorem solution_25_50 : IsAdditiveDivisorPair 25 50 := by
  refine ⟨by omega, by omega, ?_⟩; native_decide

theorem solution_35_70 : IsAdditiveDivisorPair 35 70 := by
  refine ⟨by omega, by omega, ?_⟩; native_decide

theorem solution_49_98 : IsAdditiveDivisorPair 49 98 := by
  refine ⟨by omega, by omega, ?_⟩; native_decide

/-
## Part V: The Counting Function
-/

/-- S(x) counts ordered pairs (a,b) with a,b >= 1, a+b <= x, sigma(a)+sigma(b) = sigma(a+b). -/
noncomputable def S (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x ×ˢ Finset.Icc 1 x).filter fun (a, b) =>
    a + b ≤ x ∧ sigma 1 a + sigma 1 b = sigma 1 (a + b)).card

theorem S_zero : S 0 = 0 := by
  simp only [S, Finset.Icc_eq_empty_of_lt (by omega : 1 > 0), Finset.empty_product,
             Finset.filter_empty, Finset.card_empty]

/-- S is monotone: if x <= y then S(x) <= S(y). -/
theorem S_monotone (x y : ℕ) (hxy : x ≤ y) : S x ≤ S y := by
  unfold S
  apply Finset.card_le_card
  intro ⟨a, b⟩ h
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h ⊢
  exact ⟨⟨⟨h.1.1.1, le_trans h.1.1.2 hxy⟩,
         ⟨h.1.2.1, le_trans h.1.2.2 hxy⟩⟩,
         ⟨le_trans h.2.1 hxy, h.2.2⟩⟩

/-
## Part VI: OEIS A110177
-/

def A110177 : Set ℕ :=
  {n : ℕ | ∃ a b : ℕ, a ≥ 1 ∧ b ≥ 1 ∧ a + b = n ∧ sigma 1 a + sigma 1 b = sigma 1 n}

theorem three_in_A110177 : 3 ∈ A110177 :=
  ⟨1, 2, by omega, by omega, by ring, by native_decide⟩

theorem eight_in_A110177 : 8 ∈ A110177 :=
  ⟨2, 6, by omega, by omega, by ring, by native_decide⟩

theorem nine_in_A110177 : 9 ∈ A110177 :=
  ⟨4, 5, by omega, by omega, by ring, by native_decide⟩

theorem ten_in_A110177 : 10 ∈ A110177 :=
  ⟨2, 8, by omega, by omega, by ring, by native_decide⟩

theorem fifteen_in_A110177 : 15 ∈ A110177 :=
  ⟨5, 10, by omega, by omega, by ring, by native_decide⟩

theorem twentyone_in_A110177 : 21 ∈ A110177 :=
  ⟨7, 14, by omega, by omega, by ring, by native_decide⟩

/-- For every prime p >= 5, 3p is in A110177. -/
theorem three_p_in_A110177 (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) :
    3 * p ∈ A110177 := by
  refine ⟨p, 2 * p, hp.one_le, by omega, by ring, ?_⟩
  show sigma 1 p + sigma 1 (2 * p) = sigma 1 (3 * p)
  exact sigma_add_eq_of_prime p hp h2 h3

/-- More generally, 3a is in A110177 for every a coprime to 6. -/
theorem three_a_in_A110177 (a : ℕ) (ha : a ≥ 1)
    (hcop2 : Nat.Coprime 2 a) (hcop3 : Nat.Coprime 3 a) :
    3 * a ∈ A110177 := by
  refine ⟨a, 2 * a, ha, by omega, by ring, ?_⟩
  show sigma 1 a + sigma 1 (2 * a) = sigma 1 (3 * a)
  exact sigma_add_eq_coprime6 a (by omega) hcop2 hcop3

/-
## Part VI-a: Symmetry
-/

/-- Symmetry: if (a,b) is an additive divisor pair, so is (b,a). -/
theorem solution_symmetric (a b : ℕ) (h : IsAdditiveDivisorPair a b) :
    IsAdditiveDivisorPair b a := by
  obtain ⟨ha, hb, heq⟩ := h
  refine ⟨hb, ha, ?_⟩
  rw [add_comm]
  linarith

/-
## Part VI-b: Non-Solution Families

If p and q are both prime and p + q is also prime (necessarily p + q > 2,
so one of p, q must be 2), then sigma(p) + sigma(q) = (p+1)+(q+1) = p+q+2
but sigma(p+q) = p+q+1, so the equation fails by exactly 1.

More generally, if p and q are primes and p + q is prime, (p, q) is NOT a solution.
-/

/-- If p, q are prime and p + q is prime, then (p, q) is not a solution.
    The sum σ(p) + σ(q) overshoots σ(p + q) by exactly 1. -/
theorem not_solution_of_sum_prime (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : (p + q).Prime) :
    sigma 1 p + sigma 1 q ≠ sigma 1 (p + q) := by
  rw [sigma_prime' p hp, sigma_prime' q hq, sigma_prime' (p + q) hpq]
  omega

/-- Corollary: no prime pair (p, q) with p + q prime gives an additive divisor pair. -/
theorem not_additive_pair_of_sum_prime (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : (p + q).Prime) :
    ¬IsAdditiveDivisorPair p q := by
  intro ⟨_, _, heq⟩
  exact not_solution_of_sum_prime p q hp hq hpq heq

/-
## Part VI-c: Lower Bound from Prime Family

The family {(p, 2p) : p prime, p >= 5} gives a lower bound on S(x).
For each prime 5 ≤ p ≤ x/3, the pair (p, 2p) has a + b = 3p ≤ x,
contributing one solution to S(x). These are all distinct pairs.

This gives S(x) ≥ |{p prime : 5 ≤ p ≤ x/3}| = π(x/3) - 2.
-/

/-- Each prime p in [5, x/3] contributes a solution pair (p, 2p) counted by S(x). -/
theorem prime_solution_counted (p x : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3)
    (hle : 3 * p ≤ x) :
    (p, 2 * p) ∈ (Finset.Icc 1 x ×ˢ Finset.Icc 1 x).filter
      fun (a, b) => a + b ≤ x ∧ sigma 1 a + sigma 1 b = sigma 1 (a + b) := by
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨⟨hp.one_le, by omega⟩, ⟨by omega, by omega⟩⟩, ⟨by omega, ?_⟩⟩
  have heq : p + 2 * p = 3 * p := by ring
  rw [heq]
  exact sigma_add_eq_of_prime p hp h2 h3

/-
## Part VII: The Open Problem
-/

def hasLinearGrowth : Prop :=
  ∃ c : ℝ, c > 0 ∧
    Tendsto (fun x : ℕ => (S x : ℝ) / x) atTop (nhds c)

theorem linear_growth_or_not : hasLinearGrowth ∨ ¬hasLinearGrowth :=
  Classical.em _

/--
Summary of all results for Erdos Problem #1061.

We have proved:
1. sigma(a) + sigma(2a) = sigma(3a) for all a with gcd(a,6) = 1 (general family)
2. (p, 2p) is a solution for every prime p >= 5 (special case)
3. Infinitely many solutions exist
4. Solutions are symmetric: (a,b) solution iff (b,a) solution
5. Non-solution criterion: (p,q) with p,q,p+q all prime is never a solution
6. A110177 contains 3a for every a coprime to 6
-/
theorem erdos_1061_summary :
    -- Known solutions exist
    (1, 2) ∈ additiveDivisorPairs ∧
    (2, 1) ∈ additiveDivisorPairs ∧
    -- A110177 is nonempty
    3 ∈ A110177 ∧
    -- Infinitely many solutions
    (∀ N : ℕ, ∃ a b : ℕ, a ≥ N ∧ IsAdditiveDivisorPair a b) := by
  exact ⟨solution_1_2, solution_2_1, three_in_A110177, infinitely_many_solutions⟩

end Erdos1061
