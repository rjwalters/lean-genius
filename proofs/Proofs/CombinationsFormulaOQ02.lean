import Mathlib.Combinatorics.Enumerative.Catalan
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

/-- C(2n, n+1) * (n+1) = C(2n, n) * n.
    Uses the absorption identity twice and symmetry of C(2n-1, n) = C(2n-1, n-1). -/
theorem choose_2n_succ (n : ℕ) :
    Nat.choose (2 * n) (n + 1) * (n + 1) = Nat.choose (2 * n) n * n := by
  rcases n with _ | n
  · simp
  · -- Apply absorption identity: (m+1) * C(m,k) = C(m+1,k+1) * (k+1)
    -- With m = 2n+1, k = n+1: (2n+2) * C(2n+1, n+1) = C(2n+2, n+2) * (n+2)
    have h1 := Nat.succ_mul_choose_eq (2 * n + 1) (n + 1)
    simp only [Nat.succ_eq_add_one] at h1
    -- h1: (2*n+2) * C(2*n+1, n+1) = C(2*n+2, n+2) * (n+2)
    -- With m = 2n+1, k = n: (2n+2) * C(2n+1, n) = C(2n+2, n+1) * (n+1)
    have h2 := Nat.succ_mul_choose_eq (2 * n + 1) n
    simp only [Nat.succ_eq_add_one] at h2
    -- h2: (2*n+2) * C(2*n+1, n) = C(2*n+2, n+1) * (n+1)
    -- Symmetry: C(2n+1, n+1) = C(2n+1, n)
    have hsym : Nat.choose (2 * n + 1) (n + 1) = Nat.choose (2 * n + 1) n := by
      rw [Nat.choose_symm (show n + 1 ≤ 2 * n + 1 by omega)]
      congr 1; omega
    -- From h1+hsym and h2: C(2n+2, n+2)*(n+2) = C(2n+2, n+1)*(n+1)
    rw [hsym] at h1
    -- h1: (2n+2) * C(2n+1, n) = C(2n+2, n+2) * (n+2)
    -- h2: (2n+2) * C(2n+1, n) = C(2n+2, n+1) * (n+1)
    -- Goal: C(2*(n+1), (n+1)+1) * ((n+1)+1) = C(2*(n+1), n+1) * (n+1)
    show Nat.choose (2 * (n + 1)) ((n + 1) + 1) * ((n + 1) + 1) =
         Nat.choose (2 * (n + 1)) (n + 1) * (n + 1)
    linarith

/-- **The fundamental Catalan identity**:
    C_n * (n + 1) = C(2n, n).

    Proof: catalan n = C(2n,n) - C(2n,n+1), so catalan n * (n+1) =
    C(2n,n)*(n+1) - C(2n,n+1)*(n+1) = C(2n,n)*(n+1) - C(2n,n)*n = C(2n,n). -/
theorem catalan_mul_succ (n : ℕ) :
    catalan n * (n + 1) = Nat.choose (2 * n) n := by
  simp only [catalan]
  rw [Nat.sub_mul]
  rw [choose_2n_succ]
  -- goal: C(2n,n) * (n+1) - C(2n,n) * n = C(2n,n)
  have h : Nat.choose (2 * n) n * n ≤ Nat.choose (2 * n) n * (n + 1) :=
    Nat.mul_le_mul_left _ (Nat.le_succ n)
  omega

/-- C_n is positive for all n. -/
theorem catalan_pos (n : ℕ) : 0 < catalan n := by
  -- catalan n * (n+1) = C(2n, n) > 0, and n+1 > 0, so catalan n > 0
  rcases Nat.eq_zero_or_pos (catalan n) with h | h
  · exfalso
    have h1 := catalan_mul_succ n
    rw [h, zero_mul] at h1
    exact absurd h1.symm (Nat.pos_iff_ne_zero.mp (Nat.choose_pos (by omega : n ≤ 2 * n)))
  · exact h

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
    · -- C(2(m+2), m+2) = 2 * C(2m+3, m+1) ≥ 2 * C(2m+2, m+1) ≥ 2 * 2^(m+1) = 2^(m+2)
      have ih' : 2 ^ (m + 1) ≤ centralBinom (m + 1) := ih (by omega)
      -- Pascal + symmetry: C(2m+4, m+2) = 2 * C(2m+3, m+1)
      have pascal : Nat.choose (2 * m + 4) (m + 2) =
          Nat.choose (2 * m + 3) (m + 1) + Nat.choose (2 * m + 3) (m + 2) := by
        rw [show 2 * m + 4 = (2 * m + 3) + 1 from by omega,
            show m + 2 = (m + 1) + 1 from by omega]
        exact Nat.choose_succ_succ (2 * m + 3) (m + 1)
      have hsym : Nat.choose (2 * m + 3) (m + 2) = Nat.choose (2 * m + 3) (m + 1) := by
        rw [Nat.choose_symm (show m + 2 ≤ 2 * m + 3 by omega)]
        congr 1; omega
      have hdouble : Nat.choose (2 * m + 4) (m + 2) = 2 * Nat.choose (2 * m + 3) (m + 1) := by
        rw [pascal, hsym]; ring
      -- Monotonicity: C(2m+3, m+1) ≥ C(2m+2, m+1)
      have hmono : Nat.choose (2 * m + 2) (m + 1) ≤ Nat.choose (2 * m + 3) (m + 1) :=
        Nat.choose_le_choose (m + 1) (by omega)
      -- Combine
      show 2 ^ (m + 2) ≤ centralBinom (m + 2)
      simp only [centralBinom]
      calc 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by ring
        _ ≤ 2 * Nat.choose (2 * (m + 1)) (m + 1) := by linarith [ih']
        _ ≤ 2 * Nat.choose (2 * m + 3) (m + 1) := by linarith [hmono]
        _ = Nat.choose (2 * m + 4) (m + 2) := hdouble.symm
        _ = Nat.choose (2 * (m + 2)) (m + 2) := by ring_nf

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

/-- Helper: C(2(n+1), n+1) = 2 * C(2n+1, n). -/
private lemma centralBinom_succ_eq (n : ℕ) :
    Nat.choose (2 * (n + 1)) (n + 1) = 2 * Nat.choose (2 * n + 1) n := by
  have pascal : Nat.choose (2 * n + 2) (n + 1) =
      Nat.choose (2 * n + 1) n + Nat.choose (2 * n + 1) (n + 1) := by
    rw [show 2 * n + 2 = (2 * n + 1) + 1 from by omega]
    exact Nat.choose_succ_succ (2 * n + 1) n
  have hsym : Nat.choose (2 * n + 1) (n + 1) = Nat.choose (2 * n + 1) n := by
    rw [Nat.choose_symm (show n + 1 ≤ 2 * n + 1 by omega)]
    congr 1; omega
  linarith

/-- Helper: catalan n ≤ catalan (n + 1) for all n. -/
private lemma catalan_step (n : ℕ) : catalan n ≤ catalan (n + 1) := by
  -- Show catalan n * (n+2) ≤ catalan (n+1) * (n+2), then cancel (n+2)
  suffices h : catalan n * (n + 2) ≤ catalan (n + 1) * (n + 2) from
    Nat.le_of_mul_le_mul_right h (by omega)
  have eq_n := catalan_mul_succ n        -- catalan n * (n+1) = C(2n, n)
  have eq_n1 := catalan_mul_succ (n + 1) -- catalan (n+1) * ((n+1)+1) = C(2(n+1), n+1)
  have hdbl := centralBinom_succ_eq n    -- C(2(n+1), n+1) = 2 * C(2n+1, n)
  have hmono : Nat.choose (2 * n) n ≤ Nat.choose (2 * n + 1) n :=
    Nat.choose_le_choose n (by omega)
  -- catalan (n+1) * (n+2) = C(2(n+1), n+1) = 2 * C(2n+1, n) ≥ 2 * C(2n,n)
  --   = 2 * catalan n * (n+1) ≥ catalan n * (n+2)  [since 2*(n+1) ≥ n+2]
  nlinarith

/-- Catalan numbers are monotone increasing for n ≥ 1. -/
theorem catalan_mono (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    catalan m ≤ catalan n := by
  induction hmn with
  | refl => le_refl _
  | step _ ih => exact le_trans ih (catalan_step _)

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
  -- Bridge: our catalan equals Mathlib's _root_.catalan
  have heq : ∀ m : ℕ, catalan m = _root_.catalan m := fun m => by
    have hmul : catalan m * (m + 1) = Nat.centralBinom m := catalan_mul_succ m
    rw [_root_.catalan_eq_centralBinom_div, ← hmul, Nat.mul_div_cancel _ (Nat.succ_pos m)]
  -- Use Mathlib's catalan_succ' (convolution over antidiagonal)
  rw [heq (n + 1), _root_.catalan_succ',
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ]
  apply Finset.sum_congr rfl
  intro k _
  rw [← heq k, ← heq (n - k)]

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
