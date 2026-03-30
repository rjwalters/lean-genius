/-
  Erdős Problem #1160: Group Counting Function Maximized at Powers of 2

  Source: https://erdosproblems.com/1160
  Status: OPEN

  Statement:
  Let g(n) denote the number of non-isomorphic groups of order n.
  Conjecture: If n ≤ 2^m then g(n) ≤ g(2^m).
  In other words, powers of 2 maximize the group-counting function.

  Background:
  - g(n) is sequence A000001 in the OEIS
  - Known values: g(1)=1, g(2)=1, g(4)=2, g(8)=5, g(16)=14, g(32)=51,
    g(64)=267, g(128)=2328, g(256)=56092
  - g(2^m) grows super-exponentially: g(2^m) ~ 2^{(2/27)m³}
  - Pantelidakis (2003) proved the conjecture for odd n when m ≥ 3619

  References:
  - [BNV07] Blackburn, Neumann, Venkataraman, "Enumeration of finite groups" (2007)
  - [Pa03] Pantelidakis, DPhil Thesis, Oxford (2003)
  - [Va99, 5.71]

  Tags: group-theory, enumeration, open-problem, erdos-problem
-/

import Mathlib.Data.Nat.Basic
import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

namespace Erdos1160

/-
## Section I: The Group Counting Function
-/

/-- The number of non-isomorphic groups of order n.
    This is OEIS A000001. We axiomatize it since Lean/Mathlib does not
    have a computable group enumeration function. -/
axiom numGroups : ℕ → ℕ

/-- There is exactly one group of order 0 (the trivial group, by convention)
    and one group of order 1. -/
axiom numGroups_zero : numGroups 0 = 0

axiom numGroups_one : numGroups 1 = 1

/-- For any prime p, there is exactly one group of order p (the cyclic group). -/
axiom numGroups_prime (p : ℕ) (hp : Nat.Prime p) : numGroups p = 1

/-- numGroups 2 = 1: derived from numGroups_prime since 2 is prime. -/
theorem numGroups_two : numGroups 2 = 1 :=
  numGroups_prime 2 (by norm_num)

/-- For any prime p, there are exactly 2 groups of order p²:
    the cyclic group ℤ/p²ℤ and the direct product ℤ/pℤ × ℤ/pℤ. -/
axiom numGroups_prime_sq (p : ℕ) (hp : Nat.Prime p) : numGroups (p ^ 2) = 2

/-- numGroups 4 = 2: derived from numGroups_prime_sq since 4 = 2². -/
theorem numGroups_four : numGroups 4 = 2 := by
  have : (2 : ℕ) ^ 2 = 4 := by norm_num
  rw [← this]; exact numGroups_prime_sq 2 (by norm_num)

/-- For distinct primes p > q, the number of groups of order pq is:
    - 2 if q ∣ (p - 1): ℤ/pqℤ and a semidirect product ℤ/pℤ ⋊ ℤ/qℤ
    - 1 if q ∤ (p - 1): only ℤ/pqℤ (by Sylow theory) -/
axiom numGroups_pq (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hlt : q < p) :
    numGroups (p * q) = if q ∣ (p - 1) then 2 else 1

/-- Derived: g(pq) = 2 when q ∣ (p - 1). -/
theorem numGroups_pq_dvd (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hlt : q < p)
    (hdvd : q ∣ (p - 1)) : numGroups (p * q) = 2 := by
  rw [numGroups_pq p q hp hq hlt, if_pos hdvd]

/-- Derived: g(pq) = 1 when q ∤ (p - 1). -/
theorem numGroups_pq_ndvd (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hlt : q < p)
    (hndvd : ¬(q ∣ (p - 1))) : numGroups (p * q) = 1 := by
  rw [numGroups_pq p q hp hq hlt, if_neg hndvd]

/-- numGroups 6 = 2: derived from numGroups_pq_dvd since 6 = 3 × 2 and 2 ∣ (3-1). -/
theorem numGroups_six : numGroups 6 = 2 := by
  have : 6 = 3 * 2 := by norm_num
  rw [this]; exact numGroups_pq_dvd 3 2 (by norm_num) (by norm_num) (by omega) ⟨1, by omega⟩

/-- For any prime p, there are exactly 5 groups of order p³:
    ℤ/p³ℤ, ℤ/p²ℤ×ℤ/pℤ, (ℤ/pℤ)³, and two non-abelian groups
    (e.g. for p=2: D₄ and Q₈; for odd p: Heisenberg group and ℤ/p²ℤ⋊ℤ/pℤ). -/
axiom numGroups_prime_cube (p : ℕ) (hp : Nat.Prime p) : numGroups (p ^ 3) = 5

/-- g(8) = 5: derived from numGroups_prime_cube since 8 = 2³. -/
theorem numGroups_eight : numGroups 8 = 5 := by
  have : (2 : ℕ) ^ 3 = 8 := by norm_num
  rw [← this]; exact numGroups_prime_cube 2 (by norm_num)

/-- Known value: g(12) = 5. The 5 groups are: ℤ/12ℤ, ℤ/2ℤ×ℤ/6ℤ, D₆, A₄, Dic₃. -/
axiom numGroups_twelve : numGroups 12 = 5

/-- Known value: g(16) = 14. There are 14 non-isomorphic groups of order 2⁴. -/
axiom numGroups_sixteen : numGroups 16 = 14

/-
## Section II: Basic Properties
-/

/-- For prime powers p^k, the number of groups grows with k.
    This captures the fact that higher prime powers have richer group structure. -/
axiom numGroups_prime_power_mono (p : ℕ) (hp : Nat.Prime p) (k₁ k₂ : ℕ)
    (hk : k₁ ≤ k₂) (hk₁ : 0 < k₁) : numGroups (p ^ k₁) ≤ numGroups (p ^ k₂)

/-- For prime powers p^k with k ≥ 1, the group counting function is positive.
    Derived from numGroups_prime (g(p)=1) and prime power monotonicity. -/
theorem numGroups_prime_power_pos (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 0 < k) :
    0 < numGroups (p ^ k) := by
  calc 0 < 1 := by omega
    _ = numGroups (p ^ 1) := by rw [pow_one, numGroups_prime p hp]
    _ ≤ numGroups (p ^ k) := numGroups_prime_power_mono p hp 1 k hk (by omega)

/-- g(2^m) ≥ 1 for all m ≥ 0. Proved without any axiom about general positivity:
    derived from numGroups_one (m=0) and numGroups_prime_power_pos (m≥1). -/
theorem numGroups_two_power_pos (m : ℕ) : 0 < numGroups (2 ^ m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [pow_zero, numGroups_one]
  · exact numGroups_prime_power_pos 2 (by norm_num) m hm

/-
## Section III: The Conjecture
-/

/-- **Erdős Problem #1160** (Main Conjecture):
    For all n ≤ 2^m, the number of groups of order n is at most
    the number of groups of order 2^m.

    Equivalently: powers of 2 maximize the group counting function. -/
def erdos_1160 : Prop :=
  ∀ (m n : ℕ), n ≤ 2 ^ m → numGroups n ≤ numGroups (2 ^ m)

/-- Equivalent formulation: 2^m is a global maximum of numGroups on [1, 2^m]. -/
def erdos_1160_alt : Prop :=
  ∀ (m : ℕ), ∀ n ∈ Finset.range (2 ^ m + 1), numGroups n ≤ numGroups (2 ^ m)

/-- The two formulations are equivalent. -/
theorem erdos_1160_equiv : erdos_1160 ↔ erdos_1160_alt := by
  unfold erdos_1160 erdos_1160_alt
  constructor
  · intro h m n hn
    have := Finset.mem_range.mp hn
    exact h m n (by omega)
  · intro h m n hn
    exact h m n (Finset.mem_range.mpr (by omega))

/-
## Section IV: Stronger Conjecture (BNV07, Question 22.18)
-/

/-- **Stronger Conjecture** (Blackburn-Neumann-Venkataraman):
    The sum of g(n) over all n < 2^m is at most g(2^m),
    for all sufficiently large m (perhaps m ≥ 7). -/
def erdos_1160_strong : Prop :=
  ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
    (∑ n ∈ Finset.range (2 ^ m), numGroups n) ≤ numGroups (2 ^ m)

/-- The stronger conjecture implies the original. -/
theorem strong_implies_original (h : erdos_1160_strong) (h0 : ∀ n, 0 ≤ numGroups n) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ∀ n, n < 2 ^ m → numGroups n ≤ numGroups (2 ^ m) := by
  obtain ⟨M, hM⟩ := h
  exact ⟨M, fun m hm n hn => le_trans
    (Finset.single_le_sum (fun i _ => h0 i) (Finset.mem_range.mpr hn))
    (hM m hm)⟩

/-
## Section V: Known Partial Results
-/

/-- Pantelidakis (2003): The conjecture holds for odd n when m ≥ 3619.
    Stated as a Prop (not axiom) since it is a published result not used
    by any theorem in this file. -/
def pantelidakis_odd_theorem : Prop :=
  ∀ (m n : ℕ), 3619 ≤ m → n ≤ 2 ^ m → Odd n →
    numGroups n ≤ numGroups (2 ^ m)

/-- The conjecture trivially holds for n = 1. -/
theorem erdos_1160_n_eq_one (m : ℕ) :
    numGroups 1 ≤ numGroups (2 ^ m) := by
  rw [numGroups_one]
  exact numGroups_two_power_pos m

/-- The conjecture holds for prime n (since g(p) = 1 ≤ g(2^m)). -/
theorem erdos_1160_prime (m : ℕ) (p : ℕ) (hp : Nat.Prime p) :
    numGroups p ≤ numGroups (2 ^ m) := by
  rw [numGroups_prime p hp]
  exact numGroups_two_power_pos m

/-
## Section VI: Asymptotic Growth
-/

/-- The asymptotic formula for g(2^m):
    log₂(g(2^m)) ~ (2/27) · m³ as m → ∞.
    This shows the super-exponential growth of the group counting function
    at powers of 2, which is why they dominate all other orders.
    Stated as a Prop (not axiom) since it is a known result not used
    by any theorem in this file. -/
def numGroups_two_power_growth_theorem : Prop :=
    ∀ ε > 0, ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      (2 : ℝ) / 27 - ε < (Real.log (numGroups (2 ^ m) : ℝ)) / ((m : ℝ) ^ 3 * Real.log 2) ∧
      (Real.log (numGroups (2 ^ m) : ℝ)) / ((m : ℝ) ^ 3 * Real.log 2) < 2 / 27 + ε

/-
## Section VII: Structural Results
-/

/-- The conjecture holds for n = 0 (trivially, since g(0) = 0). -/
theorem erdos_1160_n_eq_zero (m : ℕ) :
    numGroups 0 ≤ numGroups (2 ^ m) := by
  rw [numGroups_zero]
  exact Nat.zero_le _

/-- The conjecture holds when n is a power of 2 with exponent ≤ m.
    This follows directly from the monotonicity of g at prime powers. -/
theorem erdos_1160_power_of_two (k m : ℕ) (hk : k ≤ m) :
    numGroups (2 ^ k) ≤ numGroups (2 ^ m) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · -- k = 0: numGroups(1) = 1 ≤ numGroups(2^m)
    simp only [pow_zero]
    exact erdos_1160_n_eq_one m
  · -- k > 0: apply prime power monotonicity
    exact numGroups_prime_power_mono 2 (by norm_num) k m hk hk_pos

/-- The conjecture holds for n = 2^m itself (reflexivity). -/
theorem erdos_1160_self (m : ℕ) :
    numGroups (2 ^ m) ≤ numGroups (2 ^ m) :=
  le_refl _

/-- The conjecture for all n ≤ 2 follows from g(0)=0, g(1)=1, g(2)=1. -/
theorem erdos_1160_m_eq_one (n : ℕ) (hn : n ≤ 2) :
    numGroups n ≤ numGroups (2 ^ 1) := by
  simp only [pow_one]
  interval_cases n
  · rw [numGroups_zero, numGroups_two]; omega
  · rw [numGroups_one, numGroups_two]
  · exact le_refl _

/-- The conjecture for all n ≤ 4 (m = 2). Uses g(3) = 1 from numGroups_prime. -/
theorem erdos_1160_m_eq_two (n : ℕ) (hn : n ≤ 4) :
    numGroups n ≤ numGroups (2 ^ 2) := by
  have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
  rw [h4]
  interval_cases n
  · rw [numGroups_zero]; exact Nat.zero_le _
  · rw [numGroups_one, numGroups_four]; omega
  · rw [numGroups_two, numGroups_four]; omega
  · rw [numGroups_prime 3 (by norm_num), numGroups_four]; omega
  · exact le_refl _

/-- The conjecture for all n ≤ 8 (m = 3).
    Uses g(p) = 1 for primes p ∈ {3,5,7}, g(4) = 2, g(6) = 2, g(8) = 5. -/
theorem erdos_1160_m_eq_three (n : ℕ) (hn : n ≤ 8) :
    numGroups n ≤ numGroups (2 ^ 3) := by
  have h8 : (2 : ℕ) ^ 3 = 8 := by norm_num
  rw [h8]
  interval_cases n
  · rw [numGroups_zero]; exact Nat.zero_le _
  · rw [numGroups_one, numGroups_eight]; omega
  · rw [numGroups_two, numGroups_eight]; omega
  · rw [numGroups_prime 3 (by norm_num), numGroups_eight]; omega
  · rw [numGroups_four, numGroups_eight]; omega
  · rw [numGroups_prime 5 (by norm_num), numGroups_eight]; omega
  · rw [numGroups_six, numGroups_eight]; omega
  · rw [numGroups_prime 7 (by norm_num), numGroups_eight]; omega
  · exact le_refl _

/-- Helper: g(9) = 2, since 9 = 3² and g(p²) = 2 for all primes. -/
theorem numGroups_nine : numGroups 9 = 2 := by
  have : (3 : ℕ) ^ 2 = 9 := by norm_num
  rw [← this]; exact numGroups_prime_sq 3 (by norm_num)

/-- Helper: g(10) = 2, since 10 = 5 × 2 and 2 ∣ (5 - 1). -/
theorem numGroups_ten : numGroups 10 = 2 := by
  have : 10 = 5 * 2 := by norm_num
  rw [this]; exact numGroups_pq_dvd 5 2 (by norm_num) (by norm_num) (by omega) ⟨2, by omega⟩

/-- Helper: g(14) = 2, since 14 = 7 × 2 and 2 ∣ (7 - 1). -/
theorem numGroups_fourteen : numGroups 14 = 2 := by
  have : 14 = 7 * 2 := by norm_num
  rw [this]; exact numGroups_pq_dvd 7 2 (by norm_num) (by norm_num) (by omega) ⟨3, by omega⟩

/-- Helper: g(15) = 1, since 15 = 5 × 3 and 3 ∤ (5 - 1) = 4. -/
theorem numGroups_fifteen : numGroups 15 = 1 := by
  have : 15 = 5 * 3 := by norm_num
  rw [this]; exact numGroups_pq_ndvd 5 3 (by norm_num) (by norm_num) (by omega)
    (by omega)

/-- The conjecture for all n ≤ 16 (m = 4).
    Uses structural axioms: g(p²) = 2, g(pq) formulas, plus g(8) = 5, g(12) = 5, g(16) = 14. -/
theorem erdos_1160_m_eq_four (n : ℕ) (hn : n ≤ 16) :
    numGroups n ≤ numGroups (2 ^ 4) := by
  have h16 : (2 : ℕ) ^ 4 = 16 := by norm_num
  rw [h16]
  interval_cases n
  · rw [numGroups_zero]; exact Nat.zero_le _
  · rw [numGroups_one, numGroups_sixteen]; omega
  · rw [numGroups_two, numGroups_sixteen]; omega
  · rw [numGroups_prime 3 (by norm_num), numGroups_sixteen]; omega
  · rw [numGroups_four, numGroups_sixteen]; omega
  · rw [numGroups_prime 5 (by norm_num), numGroups_sixteen]; omega
  · rw [numGroups_six, numGroups_sixteen]; omega
  · rw [numGroups_prime 7 (by norm_num), numGroups_sixteen]; omega
  · rw [numGroups_eight, numGroups_sixteen]; omega
  · rw [numGroups_nine, numGroups_sixteen]; omega
  · rw [numGroups_ten, numGroups_sixteen]; omega
  · rw [numGroups_prime 11 (by norm_num), numGroups_sixteen]; omega
  · rw [numGroups_twelve, numGroups_sixteen]; omega
  · rw [numGroups_prime 13 (by norm_num), numGroups_sixteen]; omega
  · rw [numGroups_fourteen, numGroups_sixteen]; omega
  · rw [numGroups_fifteen, numGroups_sixteen]; omega
  · exact le_refl _

/-- If the conjecture holds for m, and g(2^m) ≤ g(2^(m+1)),
    then the conjecture holds for m+1 on the range [0, 2^m].
    (The new range (2^m, 2^(m+1)] still needs verification.) -/
theorem erdos_1160_lift (m : ℕ) (h : erdos_1160)  :
    ∀ n, n ≤ 2 ^ m → numGroups n ≤ numGroups (2 ^ (m + 1)) := by
  intro n hn
  calc numGroups n
      ≤ numGroups (2 ^ m) := h m n hn
    _ ≤ numGroups (2 ^ (m + 1)) :=
        erdos_1160_power_of_two m (m + 1) (Nat.le_succ m)

end Erdos1160
