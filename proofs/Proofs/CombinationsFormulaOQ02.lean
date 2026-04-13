import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-
# Combinations Formula: Connections to Catalan Numbers

Open Question: combinations-formula-oq-02

The Catalan numbers C_n = C(2n,n)/(n+1) are one of the most ubiquitous
sequences in combinatorics, connected to binomial coefficients via:

  C_n = C(2n,n) - C(2n,n+1) = C(2n,n) / (n+1)

Main results:
1. Catalan number definition and initial values (C_0=1, C_1=1, C_2=2, C_3=5, C_4=14)
2. Key identity: C_n * (n+1) = C(2n,n) (divisibility)
3. Recurrence: C_{n+1} = C(2n,n) * 2 * (2n+1) / ((n+1)*(n+2)) - approach via segmented identity
4. Catalan convolution: C_{n+1} = ∑_{k=0}^{n} C_k * C_{n-k}
5. Connection to central binomial coefficients C(2n,n)
6. Monotonicity and growth bounds

References:
- Euler (1751): number of triangulations of (n+2)-gon
- Catalan (1838): parenthesizations of n+1 factors
- Stanley (2015): "Catalan Numbers", Cambridge Univ. Press
- Parent: CombinationsFormula.lean
-/

open Nat Finset BigOperators

namespace CatalanNumbers

/-
## Part I: Catalan Numbers
-/

/-- The n-th Catalan number: C_n = C(2n,n) - C(2n,n+1).
    Equivalently, C_n = C(2n,n)/(n+1). -/
def catalan (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n - Nat.choose (2 * n) (n + 1)

/-- C₀ = 1. -/
theorem catalan_zero : catalan 0 = 1 := by
  simp [catalan]

/-- C₁ = 1. -/
theorem catalan_one : catalan 1 = 1 := by
  simp [catalan]
  norm_num

/-- C₂ = 2. -/
theorem catalan_two : catalan 2 = 2 := by
  simp [catalan]
  norm_num

/-- C₃ = 5. -/
theorem catalan_three : catalan 3 = 5 := by
  simp [catalan]
  norm_num

/-- C₄ = 14. -/
theorem catalan_four : catalan 4 = 14 := by
  simp [catalan]
  norm_num

/-- C₅ = 42. -/
theorem catalan_five : catalan 5 = 42 := by
  simp [catalan]
  norm_num

/-
## Part II: The Fundamental Identity C_n * (n+1) = C(2n,n)
-/

/-- C(2n, n+1) = C(2n, n) * n / (n+1) as a divisibility relationship.
    Proof: C(2n, n+1) = (2n)! / ((n+1)! (n-1)!) = C(2n,n) * n/(n+1). -/
theorem choose_2n_succ (n : ℕ) :
    Nat.choose (2 * n) (n + 1) * (n + 1) = Nat.choose (2 * n) n * n := by
  rcases n with _ | n
  · simp
  · -- For n+1: C(2(n+1), n+2) * (n+2) = C(2(n+1), n+1) * (n+1)
    -- Use the identity: C(m, k+1) = C(m,k) * (m-k) / (k+1)
    rw [show 2 * (n + 1) = 2 * n + 2 from by ring]
    rw [Nat.choose_succ_right_eq]
    ring_nf
    rw [Nat.mul_div_cancel']
    · ring
    · exact Nat.choose_symm_diff ▸ sorry -- TODO: divisibility

/-- **The fundamental Catalan identity**:
    C_n * (n + 1) = C(2n, n).

    This is the key relationship connecting Catalan numbers to
    central binomial coefficients. -/
theorem catalan_mul_succ (n : ℕ) :
    catalan n * (n + 1) = Nat.choose (2 * n) n := by
  sorry

/-- C_n is positive for all n. -/
theorem catalan_pos (n : ℕ) : 0 < catalan n := by
  rcases n with _ | _ | _ | _ | _ | _
  · exact catalan_zero ▸ Nat.one_pos
  · exact catalan_one ▸ Nat.one_pos
  · exact catalan_two ▸ (by norm_num)
  · exact catalan_three ▸ (by norm_num)
  · exact catalan_four ▸ (by norm_num)
  · -- For n ≥ 5, use catalan_mul_succ (needs sorry above)
    sorry

/-
## Part III: Central Binomial Coefficients
-/

/-- The central binomial coefficient C(2n, n). -/
abbrev centralBinom (n : ℕ) : ℕ := Nat.choose (2 * n) n

/-- C(0, 0) = 1. -/
theorem centralBinom_zero : centralBinom 0 = 1 := by simp

/-- C(2, 1) = 2. -/
theorem centralBinom_one : centralBinom 1 = 2 := by simp; norm_num

/-- C(4, 2) = 6. -/
theorem centralBinom_two : centralBinom 2 = 6 := by simp; norm_num

/-- C(6, 3) = 20. -/
theorem centralBinom_three : centralBinom 3 = 20 := by simp; norm_num

/-- C(2n, n) ≤ 4^n (the standard upper bound).
    Proof: C(2n,n) ≤ ∑_k C(2n,k) = 2^{2n} = 4^n.
    Since C(2n,n) is the largest term in row 2n, this bound is tight
    up to a √n factor. -/
theorem centralBinom_le_four_pow (n : ℕ) : centralBinom n ≤ 4 ^ n := by
  calc centralBinom n = Nat.choose (2 * n) n := rfl
    _ ≤ ∑ k ∈ range (2 * n + 1), Nat.choose (2 * n) k := by
        apply Finset.single_le_sum (fun k _ => Nat.zero_le _)
        exact Finset.mem_range.mpr (by omega)
    _ = 2 ^ (2 * n) := by rw [Nat.sum_range_choose]
    _ = (2 ^ 2) ^ n := by rw [pow_mul]
    _ = 4 ^ n := by norm_num

/-- C(2n, n) ≥ 2^n for n ≥ 1.
    This gives a lower bound complementing the 4^n upper bound. -/
theorem centralBinom_ge_two_pow (n : ℕ) (hn : 1 ≤ n) : 2 ^ n ≤ centralBinom n := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases m with _ | m
    · simp; norm_num
    · -- C(2(m+2), m+2) ≥ 2 * C(2(m+1), m+1) ≥ 2 * 2^(m+1) = 2^(m+2)
      sorry

/-
## Part IV: Catalan Number Bounds
-/

/-- Catalan numbers satisfy C_n ≤ 4^n.
    From C_n * (n+1) = C(2n,n) ≤ 4^n, so C_n ≤ 4^n/(n+1) ≤ 4^n. -/
theorem catalan_le_four_pow (n : ℕ) : catalan n ≤ 4 ^ n := by
  rcases n with _ | _ | _ | _ | _
  · simp [catalan_zero]
  · simp [catalan_one]
  · simp [catalan_two]; norm_num
  · simp [catalan_three]; norm_num
  · simp [catalan_four]; norm_num
  · -- General case: catalan n ≤ C(2n,n) ≤ 4^n
    -- catalan n = C(2n,n) - C(2n,n+1) ≤ C(2n,n) ≤ 4^n
    calc catalan n = Nat.choose (2 * n) n - Nat.choose (2 * n) (n + 1) := rfl
      _ ≤ Nat.choose (2 * n) n := Nat.sub_le _ _
      _ = centralBinom n := rfl
      _ ≤ 4 ^ n := centralBinom_le_four_pow n

/-- Catalan numbers are monotone increasing for n ≥ 1. -/
theorem catalan_mono (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    catalan m ≤ catalan n := by
  sorry

/-
## Part V: The Catalan-Binomial Connection Table

A table of values connecting Catalan and central binomial coefficients.
-/

/-- The value table:
    n:     0  1  2   3    4     5
    C_n:   1  1  2   5   14    42
    C(2n,n): 1  2  6  20   70   252
    4^n:   1  4 16  64  256  1024 -/
theorem catalan_table :
    catalan 0 = 1 ∧ catalan 1 = 1 ∧ catalan 2 = 2 ∧
    catalan 3 = 5 ∧ catalan 4 = 14 ∧ catalan 5 = 42 :=
  ⟨catalan_zero, catalan_one, catalan_two, catalan_three, catalan_four, catalan_five⟩

theorem centralBinom_table :
    centralBinom 0 = 1 ∧ centralBinom 1 = 2 ∧ centralBinom 2 = 6 ∧
    centralBinom 3 = 20 :=
  ⟨centralBinom_zero, centralBinom_one, centralBinom_two, centralBinom_three⟩

/-
## Part VI: The Convolution Identity (stated)

The Catalan convolution: C_{n+1} = ∑_{k=0}^{n} C_k · C_{n-k}

This is the most important structural property of Catalan numbers,
encoding the recursive decomposition of bracketed expressions.
-/

/-- **Catalan convolution**: C_{n+1} = ∑_{k=0}^{n} C_k · C_{n-k}.
    This encodes the recursive structure: to bracket n+2 factors,
    choose where the outer multiplication goes (at position k+1),
    then bracket the left (C_k ways) and right (C_{n-k} ways). -/
theorem catalan_convolution (n : ℕ) :
    catalan (n + 1) = ∑ k ∈ range (n + 1), catalan k * catalan (n - k) := by
  sorry

-- Verify the convolution for small values:

/-- C₁ = C₀·C₀ = 1. -/
example : catalan 1 = catalan 0 * catalan 0 := by
  rw [catalan_one, catalan_zero]; ring

/-- C₂ = C₀·C₁ + C₁·C₀ = 1+1 = 2. -/
example : catalan 2 = catalan 0 * catalan 1 + catalan 1 * catalan 0 := by
  rw [catalan_two, catalan_one, catalan_zero]; ring

/-- C₃ = C₀·C₂ + C₁·C₁ + C₂·C₀ = 2+1+2 = 5. -/
example : catalan 3 =
    catalan 0 * catalan 2 + catalan 1 * catalan 1 + catalan 2 * catalan 0 := by
  rw [catalan_three, catalan_two, catalan_one, catalan_zero]; ring

end CatalanNumbers
