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
1. The pair (p, 2p) is a solution for every prime p >= 5,
   giving infinitely many solutions via multiplicativity of sigma.
2. All axioms from the stub eliminated (5 axioms -> 0 axioms).
3. S(x) monotone (proved).
4. 8 solution pairs and 6 A110177 members verified.

References:
- Erdos (question reported in Guy's collection)
- Guy, R.K. [Gu04]: "Unsolved problems in number theory", Problem B15
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
## Part IV: Structural Theorem - Infinitely Many Solutions

For any prime p >= 5, the pair (p, 2p) is a solution.
Proof:
  sigma(p) = p + 1                              (p is prime)
  sigma(2p) = sigma(2) * sigma(p) = 3(p+1)      (multiplicativity, gcd(2,p)=1)
  sigma(3p) = sigma(3) * sigma(p) = 4(p+1)      (multiplicativity, gcd(3,p)=1)
  sigma(p) + sigma(2p) = (p+1) + 3(p+1) = 4(p+1) = sigma(3p) = sigma(p + 2p)
-/

/-- For any prime p >= 5, sigma(p) + sigma(2p) = sigma(3p). -/
theorem sigma_add_eq_of_prime (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) :
    sigma 1 p + sigma 1 (2 * p) = sigma 1 (3 * p) := by
  have hcop2 : Nat.Coprime 2 p := by
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr fun hdvd =>
      h2 (le_antisymm (Nat.le_of_dvd (by omega) hdvd) hp.two_le)
  have hcop3 : Nat.Coprime 3 p := by
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr fun hdvd => by
      have : p ≤ 3 := Nat.le_of_dvd (by omega) hdvd
      interval_cases p <;> simp_all [Nat.Prime]
  have hmul2 := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
    sigma_isMultiplicative hcop2
  have hmul3 := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
    sigma_isMultiplicative hcop3
  -- hmul2 : (sigma 1) (2 * p) = (sigma 1) 2 * (sigma 1) p
  -- hmul3 : (sigma 1) (3 * p) = (sigma 1) 3 * (sigma 1) p
  rw [hmul2, hmul3]
  have hs2 : sigma 1 2 = 3 := by native_decide
  have hs3 : sigma 1 3 = 4 := by native_decide
  rw [sigma_prime' p hp, hs2, hs3]
  ring

/-- (p, 2p) is a solution for every prime p >= 5. -/
theorem solution_prime_2p (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) :
    IsAdditiveDivisorPair p (2 * p) := by
  have hp1 : p ≥ 1 := hp.one_le
  have h2p1 : 2 * p ≥ 1 := by omega
  refine ⟨hp1, h2p1, ?_⟩
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

/-
## Part VII: The Open Problem
-/

def hasLinearGrowth : Prop :=
  ∃ c : ℝ, c > 0 ∧
    Tendsto (fun x : ℕ => (S x : ℝ) / x) atTop (nhds c)

theorem linear_growth_or_not : hasLinearGrowth ∨ ¬hasLinearGrowth :=
  Classical.em _

theorem erdos_1061_summary :
    (1, 2) ∈ additiveDivisorPairs ∧
    (2, 1) ∈ additiveDivisorPairs ∧
    3 ∈ A110177 := by
  exact ⟨solution_1_2, solution_2_1, three_in_A110177⟩

end Erdos1061
