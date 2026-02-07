/- Erdős Problem #390: Factorial Factorization with Large Factors

Let f(n) be the minimal m such that n! = a₁ · a₂ · ⋯ · aₖ with
n < a₁ < a₂ < ⋯ < aₖ = m. Is there a constant c such that
f(n) - 2n ~ c · n / log n?

Status: OPEN

References:
- Erdős–Graham (1980), Old and New Problems and Results in Combinatorial Number Theory
- Erdős–Guy–Selfridge (1982), "Another property of 239 and some related questions"
- OEIS A193429
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/- ## Section I: Formal Definition -/

/-- A valid factorization of n! into strictly increasing factors > n.
The list `factors` must be strictly increasing, all elements > n,
and their product equals n!. -/
structure ValidFactorization (n : ℕ) where
  factors : List ℕ
  sorted : factors.Sorted (· < ·)
  all_gt : ∀ a ∈ factors, a > n
  nonempty : factors ≠ []
  prod_eq : factors.prod = n.factorial

/-- The maximum element of a valid factorization (the last element
of the sorted list). -/
def ValidFactorization.maxFactor {n : ℕ} (vf : ValidFactorization n) : ℕ :=
  vf.factors.getLast (by exact vf.nonempty)

/-- f(n) is the minimal maximum factor over all valid factorizations. -/
noncomputable def factorizationMax (n : ℕ) : ℕ :=
  if h : ∃ vf : ValidFactorization n, True
  then sInf { vf.maxFactor | vf : ValidFactorization n }
  else 0

/- ## Section II: Concrete Values via Explicit Witnesses -/

-- For n=3: 3! = 6. Only factorization with factors > 3: [6].
-- So f(3) = 6.

/-- Witness: 3! = 6, factored as [6]. -/
def vf3 : ValidFactorization 3 where
  factors := [6]
  sorted := by simp [List.Sorted]
  all_gt := by simp
  nonempty := by simp
  prod_eq := by native_decide

/-- f(3) has a factorization achieving maximum 6. -/
theorem factorizationMax_3_le : ∃ vf : ValidFactorization 3, vf.maxFactor = 6 :=
  ⟨vf3, by native_decide⟩

/-- No factorization of 3! = 6 with factors > 3 has maximum < 6.
The only divisor of 6 that is > 3 is 6 itself. -/
theorem factorizationMax_3_ge : ∀ vf : ValidFactorization 3, vf.maxFactor ≥ 6 := by
  intro vf
  unfold ValidFactorization.maxFactor
  have hprod := vf.prod_eq
  have hgt := vf.all_gt
  have hne := vf.nonempty
  have hall4 : ∀ a ∈ vf.factors, a ≥ 4 := fun a ha => hgt a ha
  cases hf : vf.factors with
  | nil => exact absurd hf hne
  | cons x xs =>
    cases xs with
    | nil =>
      simp [List.prod] at hprod
      simp [List.getLast] at *
      omega
    | cons y ys =>
      exfalso
      have hx : x ≥ 4 := hall4 x (by simp [hf])
      have hy : y > x := by
        have hsorted := vf.sorted
        rw [hf] at hsorted
        simp [List.Sorted, List.Pairwise] at hsorted
        exact hsorted.1.1
      have hy5 : y ≥ 5 := by omega
      have hys_pos : ys.prod ≥ 1 :=
        (List.prod_pos (fun a ha => by
          have := hall4 a (by rw [hf]; simp [ha]); omega)).le
      have hprod_ge : vf.factors.prod ≥ 4 * 5 := by
        rw [hf]; simp [List.prod]
        calc x * (y * ys.prod) ≥ x * y := by
              apply Nat.mul_le_mul_left
              exact Nat.le_mul_of_pos_right y (by omega)
             _ ≥ 4 * 5 := Nat.mul_le_mul hx hy5
      rw [hprod] at hprod_ge
      norm_num at hprod_ge

-- For n=5: 5! = 120 = 10 · 12
def vf5 : ValidFactorization 5 where
  factors := [10, 12]
  sorted := by simp [List.Sorted, List.Pairwise]
  all_gt := by simp; omega
  nonempty := by simp
  prod_eq := by native_decide

theorem factorizationMax_5_le : ∃ vf : ValidFactorization 5, vf.maxFactor = 12 :=
  ⟨vf5, by native_decide⟩

-- For n=6: 6! = 720 = 8 · 9 · 10
def vf6 : ValidFactorization 6 where
  factors := [8, 9, 10]
  sorted := by simp [List.Sorted, List.Pairwise]; omega
  all_gt := by simp; omega
  nonempty := by simp
  prod_eq := by native_decide

theorem factorizationMax_6_le : ∃ vf : ValidFactorization 6, vf.maxFactor = 10 :=
  ⟨vf6, by native_decide⟩

-- For n=7: 7! = 5040 = 14 · 18 · 20
def vf7 : ValidFactorization 7 where
  factors := [14, 18, 20]
  sorted := by simp [List.Sorted, List.Pairwise]; omega
  all_gt := by simp; omega
  nonempty := by simp
  prod_eq := by native_decide

theorem factorizationMax_7_le : ∃ vf : ValidFactorization 7, vf.maxFactor = 20 :=
  ⟨vf7, by native_decide⟩

/- ## Section III: Basic Structural Properties -/

/-- For any valid factorization of n!, the maximum factor is > n. -/
theorem maxFactor_gt (n : ℕ) (vf : ValidFactorization n) : vf.maxFactor > n := by
  unfold ValidFactorization.maxFactor
  exact vf.all_gt _ (List.getLast_mem vf.nonempty)

/-- A single-factor factorization [n!] is always valid for n ≥ 3,
giving an upper bound f(n) ≤ n!. -/
theorem factorizationMax_le_factorial (n : ℕ) (hn : n ≥ 3) :
    ∃ vf : ValidFactorization n, vf.maxFactor = n.factorial := by
  refine ⟨⟨[n.factorial], ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [List.Sorted]
  · simp; omega
  · simp
  · simp
  · simp [ValidFactorization.maxFactor]

/- ## Section IV: The Erdős–Guy–Selfridge Asymptotic Result

The 1982 paper showed f(n) - 2n ≍ n/log n, meaning there exist constants
c, C > 0 such that c·n/log n ≤ f(n) - 2n ≤ C·n/log n for large n.
This is a deep combinatorial result that we axiomatize. -/

axiom factorizationMax_asymptotic :
  ∃ C c : ℝ, C > 0 ∧ c > 0 ∧
    ∀ n : ℕ, n ≥ 10 →
      c * n / Real.log n ≤ (factorizationMax n : ℝ) - 2 * n ∧
      (factorizationMax n : ℝ) - 2 * n ≤ C * n / Real.log n

/- ## Section V: The Open Conjecture

Erdős Problem #390 asks whether the limit of (f(n) - 2n) · log(n) / n
exists as n → ∞. The Erdős–Guy–Selfridge bounds show this ratio is bounded
between positive constants, but existence of the limit is unknown. -/

def ErdosProblem390 : Prop :=
  ∃ c : ℝ, c > 0 ∧
    Filter.Tendsto
      (fun n : ℕ => ((factorizationMax n : ℝ) - 2 * n) * Real.log n / n)
      Filter.atTop (nhds c)
