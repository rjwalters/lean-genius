import Mathlib

/-
# De Moivre OQ-02: Chebyshev Polynomial Properties via De Moivre

## Research Question

Prove deeper Chebyshev polynomial properties using De Moivre's theorem as the
primary tool, going beyond the basic T_n(cos θ) = cos(nθ) identity.

## Answer: YES

We prove composition T_m ∘ T_n = T_{mn}, product-to-sum, parity, and
special values — all from De Moivre / cos identities.
-/

open Polynomial Polynomial.Chebyshev Real

namespace DeMoivreOQ02

-- T_real_cos θ n : (T ℝ n).eval (cos θ) = cos (↑n * θ)

/- ## Part I: Composition Identity -/

/-- T_m(T_n(cos θ)) = T_{mn}(cos θ): Chebyshev composition. -/
theorem chebyshev_composition (m n : ℤ) (θ : ℝ) :
    (T ℝ m).eval ((T ℝ n).eval (Real.cos θ)) = (T ℝ (m * n)).eval (Real.cos θ) := by
  rw [T_real_cos θ n, T_real_cos (↑n * θ) m, T_real_cos θ (m * n)]
  congr 1; push_cast; ring

/-- Composition is commutative on cos values. -/
theorem chebyshev_composition_comm (m n : ℤ) (θ : ℝ) :
    (T ℝ m).eval ((T ℝ n).eval (Real.cos θ)) =
    (T ℝ n).eval ((T ℝ m).eval (Real.cos θ)) := by
  rw [chebyshev_composition, chebyshev_composition]
  congr 1; ring_nf

/-- T_1 is the identity for composition. -/
theorem chebyshev_comp_one (n : ℤ) (θ : ℝ) :
    (T ℝ 1).eval ((T ℝ n).eval (Real.cos θ)) = (T ℝ n).eval (Real.cos θ) := by
  rw [chebyshev_composition]; simp

/-- Composition associativity: T_l(T_m(T_n(x))) = T_{lmn}(x). -/
theorem chebyshev_comp_assoc (l m n : ℤ) (θ : ℝ) :
    (T ℝ l).eval ((T ℝ m).eval ((T ℝ n).eval (Real.cos θ))) =
    (T ℝ (l * m * n)).eval (Real.cos θ) := by
  rw [chebyshev_composition m n θ, chebyshev_composition l (m * n) θ]
  congr 1; ring_nf

/-- T_2(T_n(cos θ)) = T_{2n}(cos θ). -/
theorem T_two_comp (n : ℤ) (θ : ℝ) :
    (T ℝ 2).eval ((T ℝ n).eval (Real.cos θ)) = (T ℝ (2 * n)).eval (Real.cos θ) :=
  chebyshev_composition 2 n θ

/-- T_n(T_n(cos θ)) = T_{n²}(cos θ). -/
theorem T_self_comp (n : ℤ) (θ : ℝ) :
    (T ℝ n).eval ((T ℝ n).eval (Real.cos θ)) = (T ℝ (n * n)).eval (Real.cos θ) :=
  chebyshev_composition n n θ

/- ## Part II: Product-to-Sum -/

/-- 2·T_m(cos θ)·T_n(cos θ) = T_{m+n}(cos θ) + T_{m-n}(cos θ). -/
theorem chebyshev_product_to_sum (m n : ℤ) (θ : ℝ) :
    2 * ((T ℝ m).eval (Real.cos θ)) * ((T ℝ n).eval (Real.cos θ)) =
    (T ℝ (m + n)).eval (Real.cos θ) + (T ℝ (m - n)).eval (Real.cos θ) := by
  rw [T_real_cos θ m, T_real_cos θ n, T_real_cos θ (m + n), T_real_cos θ (m - n)]
  have hsum := Real.cos_add ((↑m : ℝ) * θ) ((↑n : ℝ) * θ)
  have hdiff := Real.cos_sub ((↑m : ℝ) * θ) ((↑n : ℝ) * θ)
  have h1 : (↑(m + n) : ℝ) * θ = ↑m * θ + ↑n * θ := by push_cast; ring
  have h2 : (↑(m - n) : ℝ) * θ = ↑m * θ - ↑n * θ := by push_cast; ring
  rw [h1, h2]; linarith

/-- 2·T_n(cos θ)² = T_{2n}(cos θ) + 1. -/
theorem chebyshev_square (n : ℤ) (θ : ℝ) :
    2 * ((T ℝ n).eval (Real.cos θ)) * ((T ℝ n).eval (Real.cos θ)) =
    (T ℝ (2 * n)).eval (Real.cos θ) + 1 := by
  have h := chebyshev_product_to_sum n n θ
  simp only [show n + n = 2 * n from by ring, show n - n = 0 from by ring] at h
  rwa [T_real_cos θ 0, show (↑(0 : ℤ) : ℝ) * θ = 0 from by simp, Real.cos_zero] at h

/- ## Part III: Parity -/

/-- T_n(-cos θ) = (-1)^n · T_n(cos θ). -/
theorem chebyshev_parity (n : ℤ) (θ : ℝ) :
    (T ℝ n).eval (-Real.cos θ) = (-1)^n * (T ℝ n).eval (Real.cos θ) := by
  have hcos : -Real.cos θ = Real.cos (π - θ) := by
    rw [Real.cos_pi_sub]
  rw [hcos, T_real_cos (π - θ) n, T_real_cos θ n]
  rw [show (↑n : ℝ) * (π - θ) = ↑n * π - ↑n * θ from by ring, Real.cos_int_mul_pi_sub]

/-- Even Chebyshev: T_{2n}(-x) = T_{2n}(x). -/
theorem chebyshev_even_parity (n : ℤ) (θ : ℝ) :
    (T ℝ (2 * n)).eval (-Real.cos θ) = (T ℝ (2 * n)).eval (Real.cos θ) := by
  rw [chebyshev_parity]
  have heven : Even (2 * n) := ⟨n, by ring⟩
  rw [Even.neg_one_zpow heven, one_mul]

/-- Odd Chebyshev: T_{2n+1}(-x) = -T_{2n+1}(x). -/
theorem chebyshev_odd_parity (n : ℤ) (θ : ℝ) :
    (T ℝ (2 * n + 1)).eval (-Real.cos θ) = -(T ℝ (2 * n + 1)).eval (Real.cos θ) := by
  rw [chebyshev_parity]
  have : (-1 : ℝ) ^ (2 * n + 1) = -1 := by
    have heven : Even (2 * n) := ⟨n, by ring⟩
    rw [zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0), Even.neg_one_zpow heven, zpow_one, one_mul]
  rw [this]; ring

/- ## Part IV: Special Values -/

/-- T_n(1) = 1 (from cos(0) = 1 and cos(n·0) = 1). -/
theorem chebyshev_at_one (n : ℤ) : (T ℝ n).eval 1 = 1 := by
  have h := T_real_cos 0 n
  simp only [mul_zero, Real.cos_zero] at h
  exact h

/-- T_n(-1) = (-1)^n (from cos(π) = -1 and cos(nπ) = (-1)^n). -/
theorem chebyshev_at_neg_one (n : ℤ) : (T ℝ n).eval (-1) = (-1)^n := by
  have hcos : (-1 : ℝ) = Real.cos π := by rw [Real.cos_pi]
  conv_lhs => rw [hcos]
  rw [T_real_cos π n]
  exact Real.cos_int_mul_pi n

/-- T_n(0) = cos(nπ/2). -/
theorem chebyshev_at_zero (n : ℤ) :
    (T ℝ n).eval 0 = Real.cos (↑n * π / 2) := by
  have h : (0 : ℝ) = Real.cos (π / 2) := by simp [Real.cos_pi_div_two]
  rw [h, T_real_cos (π / 2) n]; congr 1; ring

/- ## Part V: Roots of Chebyshev Polynomials -/

/-- T_n vanishes at cos((2k+1)π/(2n)). -/
theorem chebyshev_root (n : ℕ) (hn : 0 < n) (k : ℤ) :
    (T ℝ (↑n)).eval (Real.cos ((2 * ↑k + 1) * π / (2 * ↑n))) = 0 := by
  rw [T_real_cos]
  have hn_ne : (↑n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  have hcast : (↑(↑n : ℤ) : ℝ) = (↑n : ℝ) := by push_cast; ring
  rw [hcast]
  rw [show (↑n : ℝ) * ((2 * ↑k + 1) * π / (2 * ↑n)) = (2 * ↑k + 1) * π / 2 from by
    field_simp]
  rw [show (2 * (↑k : ℝ) + 1) * π / 2 = ↑k * π + π / 2 from by ring]
  rw [Real.cos_add (↑k * π) (π / 2)]
  simp [Real.cos_pi_div_two, Real.sin_pi_div_two]

/- ## Part VI: Summary -/

/-- De Moivre OQ-02: Chebyshev composition, product-to-sum, parity, special values. -/
theorem demoivre_oq02_summary (m n : ℤ) (θ : ℝ) :
    ((T ℝ m).eval ((T ℝ n).eval (Real.cos θ)) = (T ℝ (m * n)).eval (Real.cos θ)) ∧
    (2 * ((T ℝ m).eval (Real.cos θ)) * ((T ℝ n).eval (Real.cos θ)) =
     (T ℝ (m + n)).eval (Real.cos θ) + (T ℝ (m - n)).eval (Real.cos θ)) ∧
    ((T ℝ n).eval (-Real.cos θ) = (-1)^n * (T ℝ n).eval (Real.cos θ)) ∧
    ((T ℝ n).eval 1 = 1) :=
  ⟨chebyshev_composition m n θ,
   chebyshev_product_to_sum m n θ,
   chebyshev_parity n θ,
   chebyshev_at_one n⟩

end DeMoivreOQ02
