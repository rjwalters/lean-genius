/-
Erdos Problem #686: Ratios of Products of Consecutive Integers

Source: https://erdosproblems.com/686
Status: OPEN

Statement:
Can every integer N >= 2 be written as
  N = prod_{1 <= i <= k}(m+i) / prod_{1 <= i <= k}(n+i)
for some k >= 2 and m >= n + k?

Background:
- Products of k consecutive integers equal k! * C(n+k, k)
- k >= 2 excludes the trivial single-factor case
- m >= n + k ensures the ranges don't overlap

Reference: [Er79d]

Axiom elimination (researcher-3):
  representable_set_infinite was axiomatized. Now proved via:
  For fixed n, k, choosing m = n + t*P(n,k) ensures (n+i) | (m+i) for each factor,
  so the product ratio is an integer. Strict monotonicity of consecutiveProduct
  gives infinitely many distinct values.
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

open Finset BigOperators Nat

namespace Erdos686

-- ## Part I: Consecutive Products

/-- Product of k consecutive integers starting at n+1: P(n,k) = (n+1)(n+2)...(n+k). -/
def consecutiveProduct (n k : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 k, (n + i)

/-- Recursion: P(n, k+1) = P(n, k) * (n + k + 1). -/
theorem consecutiveProduct_succ (n k : ℕ) :
    consecutiveProduct n (k + 1) = consecutiveProduct n k * (n + k + 1) := by
  unfold consecutiveProduct
  rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1)]
  ring

/-- P(n,k) = (n+k)! / n!. This is a standard identity proved by induction on k. -/
theorem consecutiveProduct_eq_factorial (n k : ℕ) :
    consecutiveProduct n k * n ! = (n + k) ! := by
  induction k with
  | zero =>
    simp [consecutiveProduct]
  | succ k ih =>
    rw [consecutiveProduct_succ]
    rw [show consecutiveProduct n k * (n + k + 1) * n ! =
        (consecutiveProduct n k * n !) * (n + k + 1) from by ring]
    rw [ih]
    rw [show n + (k + 1) = (n + k) + 1 from by omega]
    rw [Nat.factorial_succ]
    ring

/-- P(n,k) = k! * C(n+k, k). Follows from the factorial identity and
    the definition of binomial coefficients. -/
theorem product_binomial_relation (n k : ℕ) :
    consecutiveProduct n k = k ! * (n + k).choose k := by
  have h := consecutiveProduct_eq_factorial n k
  have hchoose := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left k n)
  rw [show n + k - k = n from by omega] at hchoose
  have : consecutiveProduct n k * n ! = k ! * (n + k).choose k * n ! := by
    rw [h, ← hchoose]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos n) this

-- ## Part II: The Ratio Expression

/-- The ratio P(m,k)/P(n,k) as a rational number. -/
noncomputable def ratioExpression (n m k : ℕ) : ℚ :=
  (consecutiveProduct m k : ℚ) / (consecutiveProduct n k : ℚ)

/-- The ratio equals C(m+k,k) / C(n+k,k) when expressed via binomials. -/
theorem ratio_as_binomials (n m k : ℕ) (_hk : k ≥ 1) :
    ratioExpression n m k = ((m + k).choose k : ℚ) / ((n + k).choose k : ℚ) := by
  unfold ratioExpression
  rw [product_binomial_relation n k, product_binomial_relation m k]
  push_cast
  have hfact : (k ! : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  field_simp

/-- The ratio is an integer when the denominator divides the numerator. -/
def IsIntegerRatio (n m k : ℕ) : Prop :=
  (consecutiveProduct n k) ∣ (consecutiveProduct m k)

-- ## Part III: The Representation Property

/-- N is representable with parameters (n, m, k). -/
def IsRepresentable (N : ℕ) (n m k : ℕ) : Prop :=
  k ≥ 2 ∧ m ≥ n + k ∧ ratioExpression n m k = N

/-- N is representable (existentially). -/
def Representable (N : ℕ) : Prop :=
  ∃ n m k, IsRepresentable N n m k

/-- Erdos Problem #686 (OPEN):
    Every integer N >= 2 can be expressed as a ratio of two products
    of k consecutive integers with non-overlapping ranges.
    Stated as a definition since this is an open conjecture. -/
def Erdos686Conjecture : Prop := ∀ N ≥ 2, Representable N

-- ## Part IV: Structural Properties

/-- When m > n, each factor (m+i) > (n+i), so the product is strictly larger. -/
theorem numerator_gt_denominator (n m k : ℕ) (hk : k ≥ 1) (hm : m > n) :
    consecutiveProduct m k > consecutiveProduct n k := by
  induction k with
  | zero => omega
  | succ k' ih =>
    rw [consecutiveProduct_succ, consecutiveProduct_succ]
    cases k' with
    | zero =>
      simp [consecutiveProduct]; omega
    | succ k'' =>
      have h_prod := ih (by omega : k'' + 1 ≥ 1)
      calc consecutiveProduct m (k'' + 1) * (m + (k'' + 1) + 1)
          > consecutiveProduct n (k'' + 1) * (m + (k'' + 1) + 1) := by
            exact Nat.mul_lt_mul_of_pos_right h_prod (by omega)
        _ ≥ consecutiveProduct n (k'' + 1) * (n + (k'' + 1) + 1) := by
            exact Nat.mul_le_mul_left _ (by omega)

/-- Each factor is positive, so the product is positive. -/
theorem consecutiveProduct_pos (n k : ℕ) :
    consecutiveProduct n k > 0 := by
  unfold consecutiveProduct
  apply Finset.prod_pos
  intro i hi
  simp [Finset.mem_Icc] at hi
  omega

/-- The product is monotone in the first argument. -/
theorem consecutiveProduct_mono {n₁ n₂ : ℕ} (k : ℕ) (h : n₁ ≤ n₂) :
    consecutiveProduct n₁ k ≤ consecutiveProduct n₂ k := by
  unfold consecutiveProduct
  apply Finset.prod_le_prod
  · intro i _; omega
  · intro i _; omega

-- ## Part IV-B: Divisibility Infrastructure

/-- Each factor (n+i) divides the consecutive product P(n,k). -/
theorem factor_dvd_consecutiveProduct (n k : ℕ) {i : ℕ} (hi : i ∈ Finset.Icc 1 k) :
    (n + i) ∣ consecutiveProduct n k := by
  unfold consecutiveProduct
  exact Finset.dvd_prod_of_mem _ hi

/-- Pointwise divisibility of factors implies product divisibility. -/
theorem consecutiveProduct_dvd_of_pointwise {n m k : ℕ}
    (h : ∀ i ∈ Finset.Icc 1 k, (n + i) ∣ (m + i)) :
    consecutiveProduct n k ∣ consecutiveProduct m k := by
  unfold consecutiveProduct
  exact Finset.prod_dvd_prod_of_dvd _ (fun i => m + i) h

/-- For m = n + t*P(n,k), each factor (n+i) divides (m+i) since (n+i) | P(n,k). -/
theorem shifted_factor_dvd (n k t : ℕ) {i : ℕ} (hi : i ∈ Finset.Icc 1 k) :
    (n + i) ∣ (n + (t + 1) * consecutiveProduct n k + i) := by
  have hdvd : (n + i) ∣ consecutiveProduct n k := factor_dvd_consecutiveProduct n k hi
  have : n + (t + 1) * consecutiveProduct n k + i =
      (n + i) + (t + 1) * consecutiveProduct n k := by ring
  rw [this]
  exact dvd_add (dvd_refl _) (dvd_mul_of_dvd_right hdvd _)

/-- For m = n + t*P(n,k), the product ratio is always an integer. -/
theorem integer_ratio_at_multiples (n k t : ℕ) :
    IsIntegerRatio n (n + (t + 1) * consecutiveProduct n k) k :=
  consecutiveProduct_dvd_of_pointwise (fun i hi => shifted_factor_dvd n k t hi)

/-- P(n,k) >= k! since P(n,k) = k! * C(n+k,k) and C(n+k,k) >= 1. -/
theorem consecutiveProduct_ge_factorial (n k : ℕ) :
    consecutiveProduct n k ≥ k ! := by
  rw [product_binomial_relation]
  exact Nat.le_mul_of_pos_right _ (Nat.choose_pos (Nat.le_add_left k n))

/-- k! >= k for k >= 1. -/
theorem factorial_ge_self (k : ℕ) (hk : k ≥ 1) : k ! ≥ k := by
  induction k with
  | zero => omega
  | succ m ih =>
    rw [Nat.factorial_succ]
    by_cases hm : m = 0
    · subst hm; simp
    · calc (m + 1) * m ! ≥ (m + 1) * m := Nat.mul_le_mul_left _ (ih (by omega))
        _ ≥ m + 1 := le_mul_of_one_le_right (by omega) (by omega)

/-- The shifted index m = n + (t+1)*P(n,k) satisfies m >= n + k when k >= 2. -/
theorem shift_ge_gap (n k t : ℕ) (hk : k ≥ 2) :
    n + (t + 1) * consecutiveProduct n k ≥ n + k := by
  have h1 : consecutiveProduct n k ≥ k := by
    calc consecutiveProduct n k ≥ k ! := consecutiveProduct_ge_factorial n k
      _ ≥ k := factorial_ge_self k (by omega)
  nlinarith

/-- When P(n,k) | P(m,k), the rational ratio equals the natural quotient. -/
theorem ratioExpression_eq_nat_div {n m k : ℕ} (h : IsIntegerRatio n m k) :
    ratioExpression n m k = ((consecutiveProduct m k / consecutiveProduct n k : ℕ) : ℚ) := by
  unfold ratioExpression
  have hne : (consecutiveProduct n k : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (consecutiveProduct_pos n k).ne'
  exact (Nat.cast_div h hne).symm

/-- consecutiveProduct is injective in its first argument when k >= 1,
    since it is strictly monotone. -/
theorem consecutiveProduct_inj {k : ℕ} (hk : k ≥ 1) {n₁ n₂ : ℕ}
    (heq : consecutiveProduct n₁ k = consecutiveProduct n₂ k) : n₁ = n₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact absurd heq.symm (Nat.ne_of_gt (numerator_gt_denominator n₁ n₂ k hk h))
  · exact absurd heq (Nat.ne_of_gt (numerator_gt_denominator n₂ n₁ k hk h))

-- ## Part V: Verified Examples

/-- N = 2: P(2,2)/P(1,2) = (3*4)/(2*3) = 12/6 = 2. -/
theorem example_N2 : IsIntegerRatio 1 2 2 := by
  unfold IsIntegerRatio consecutiveProduct
  decide

/-- N = 6: P(2,2)/P(0,2) = (3*4)/(1*2) = 12/2 = 6. -/
theorem example_N6 : IsIntegerRatio 0 2 2 ∧ consecutiveProduct 2 2 / consecutiveProduct 0 2 = 6 := by
  constructor
  · unfold IsIntegerRatio consecutiveProduct; decide
  · native_decide

/-- N = 3: P(3,2)/P(1,2) = (4*5)/(2*3) = 20/6. Not integer! Try k=3:
    P(3,3)/P(0,3) = (4*5*6)/(1*2*3) = 120/6 = 20. So 3 needs different params.
    P(1,2)/P(0,2) = (2*3)/(1*2) = 6/2 = 3. -/
theorem example_N3 : IsIntegerRatio 0 1 2 ∧ consecutiveProduct 1 2 / consecutiveProduct 0 2 = 3 := by
  constructor
  · unfold IsIntegerRatio consecutiveProduct; decide
  · native_decide

/-- N = 10: P(3,2)/P(0,2) = (4*5)/(1*2) = 20/2 = 10. -/
theorem example_N10 : IsIntegerRatio 0 3 2 ∧ consecutiveProduct 3 2 / consecutiveProduct 0 2 = 10 := by
  constructor
  · unfold IsIntegerRatio consecutiveProduct; decide
  · native_decide

-- ## Part VI: Follow-Up Question — PROVED (was axiom)

/-- The set of integers representable with fixed n, k. -/
def RepresentableSet (n k : ℕ) : Set ℕ :=
  {N | ∃ m ≥ n + k, ratioExpression n m k = N}

/-- Helper: the natural-number quotient for the t-th shifted index. -/
private def repValue (n k t : ℕ) : ℕ :=
  consecutiveProduct (n + (t + 1) * consecutiveProduct n k) k / consecutiveProduct n k

/-- Each repValue is a member of RepresentableSet. -/
private theorem repValue_mem (n k : ℕ) (hk : k ≥ 2) (t : ℕ) :
    repValue n k t ∈ RepresentableSet n k := by
  refine ⟨n + (t + 1) * consecutiveProduct n k, shift_ge_gap n k t hk, ?_⟩
  exact ratioExpression_eq_nat_div (integer_ratio_at_multiples n k t)

/-- repValue is injective: distinct t give distinct quotients. -/
private theorem repValue_injective (n k : ℕ) (hk : k ≥ 2) :
    Function.Injective (repValue n k) := by
  intro t₁ t₂ heq
  simp only [repValue] at heq
  have h₁ := integer_ratio_at_multiples n k t₁
  have h₂ := integer_ratio_at_multiples n k t₂
  have hprod_eq : consecutiveProduct (n + (t₁ + 1) * consecutiveProduct n k) k =
                  consecutiveProduct (n + (t₂ + 1) * consecutiveProduct n k) k := by
    rw [← Nat.div_mul_cancel h₁, ← Nat.div_mul_cancel h₂, heq]
  have hm_eq := consecutiveProduct_inj (by omega : k ≥ 1) hprod_eq
  have h_cancel := Nat.add_left_cancel hm_eq
  have h_succ := Nat.eq_of_mul_eq_mul_right (consecutiveProduct_pos n k) h_cancel
  omega

/-- For fixed n, k >= 2, the representable set is infinite.
    Proof: m_t = n + (t+1)*P(n,k) gives integer ratios for all t,
    and strict monotonicity ensures they are all distinct. -/
theorem representable_set_infinite (n k : ℕ) (hk : k ≥ 2) :
    Set.Infinite (RepresentableSet n k) :=
  Set.Infinite.mono
    (Set.range_subset_iff.mpr (repValue_mem n k hk))
    (Set.infinite_range_of_injective (repValue_injective n k hk))

-- ## Part VII: Connections

/-- Connection to Problem #677: integers as products of consecutive integers.
    This is the special case where the denominator product is 1. -/
def problem_677_special_case (N : ℕ) : Prop :=
  ∃ n k : ℕ, k ≥ 2 ∧ consecutiveProduct n k = N

end Erdos686
