import Mathlib

set_option linter.unusedVariables false

namespace ChineseRemainderNonCoprimeOQ02

open Polynomial

section EuclideanDomainCRT

variable {R : Type*} [EuclideanDomain R] [DecidableEq R]

theorem ed_crt_necessary {m n a b : R}
    (h : ∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b)) :
    EuclideanDomain.gcd m n ∣ (a - b) := by
  obtain ⟨x, hm, hn⟩ := h
  have h1 := dvd_trans (EuclideanDomain.gcd_dvd_left m n) hm
  have h2 := dvd_trans (EuclideanDomain.gcd_dvd_right m n) hn
  have : EuclideanDomain.gcd m n ∣ ((x - b) - (x - a)) := dvd_sub h2 h1
  rwa [show (x - b) - (x - a) = a - b from by ring] at this

theorem ed_crt_sufficient {m n a b : R}
    (h : EuclideanDomain.gcd m n ∣ (a - b)) :
    ∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b) := by
  obtain ⟨q, hq⟩ := h
  refine ⟨a - m * (EuclideanDomain.gcdA m n * q), ?_, ?_⟩
  · exact ⟨-(EuclideanDomain.gcdA m n * q), by ring⟩
  · refine ⟨EuclideanDomain.gcdB m n * q, ?_⟩
    have hbez := EuclideanDomain.gcd_eq_gcd_ab m n
    have hkey : EuclideanDomain.gcd m n - m * EuclideanDomain.gcdA m n =
        n * EuclideanDomain.gcdB m n := by rw [hbez]; ring
    calc a - m * (EuclideanDomain.gcdA m n * q) - b
        = (a - b) - m * EuclideanDomain.gcdA m n * q := by ring
      _ = EuclideanDomain.gcd m n * q - m * EuclideanDomain.gcdA m n * q := by rw [hq]
      _ = (EuclideanDomain.gcd m n - m * EuclideanDomain.gcdA m n) * q := by ring
      _ = n * EuclideanDomain.gcdB m n * q := by rw [hkey]
      _ = n * (EuclideanDomain.gcdB m n * q) := by ring

theorem ed_crt_iff {m n a b : R} :
    (∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b)) ↔ EuclideanDomain.gcd m n ∣ (a - b) :=
  ⟨ed_crt_necessary, ed_crt_sufficient⟩

theorem ed_crt_unique {m n a b x y : R}
    (hx : m ∣ (x - a) ∧ n ∣ (x - b))
    (hy : m ∣ (y - a) ∧ n ∣ (y - b)) :
    EuclideanDomain.lcm m n ∣ (x - y) := by
  have hm : m ∣ (x - y) := by
    have := dvd_sub hx.1 hy.1
    rwa [show (x - a) - (y - a) = x - y from by ring] at this
  have hn : n ∣ (x - y) := by
    have := dvd_sub hx.2 hy.2
    rwa [show (x - b) - (y - b) = x - y from by ring] at this
  exact EuclideanDomain.lcm_dvd hm hn

theorem ed_crt_coprime {m n a b : R}
    (hcop : IsUnit (EuclideanDomain.gcd m n)) :
    ∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b) :=
  ed_crt_sufficient (hcop.dvd)

theorem ed_crt_three_necessary {m n p a b c : R}
    (h : ∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b) ∧ p ∣ (x - c)) :
    EuclideanDomain.gcd m n ∣ (a - b) ∧
    EuclideanDomain.gcd m p ∣ (a - c) ∧
    EuclideanDomain.gcd n p ∣ (b - c) := by
  obtain ⟨x, hm, hn, hp⟩ := h
  exact ⟨ed_crt_necessary ⟨x, hm, hn⟩, ed_crt_necessary ⟨x, hm, hp⟩,
         ed_crt_necessary ⟨x, hn, hp⟩⟩

theorem ed_crt_weaken (m m' a x : R)
    (hdvd : m' ∣ m) (h : m ∣ (x - a)) : m' ∣ (x - a) := dvd_trans hdvd h

theorem ed_crt_combine_same {m n a x : R}
    (hm : m ∣ (x - a)) (hn : n ∣ (x - a)) :
    EuclideanDomain.lcm m n ∣ (x - a) := EuclideanDomain.lcm_dvd hm hn

theorem int_crt_from_ed (m n a b : ℤ) :
    (∃ x : ℤ, m ∣ (x - a) ∧ n ∣ (x - b)) ↔ EuclideanDomain.gcd m n ∣ (a - b) := ed_crt_iff

theorem int_crt_unique_from_ed (m n a b x y : ℤ)
    (hx : m ∣ (x - a) ∧ n ∣ (x - b))
    (hy : m ∣ (y - a) ∧ n ∣ (y - b)) :
    EuclideanDomain.lcm m n ∣ (x - y) := ed_crt_unique hx hy

end EuclideanDomainCRT

section PolynomialCRT

variable {k : Type*} [Field k]

theorem linear_factors_coprime {a b : k} (hab : a ≠ b) :
    IsCoprime (X - C a : k[X]) (X - C b) := by
  refine ⟨C (b - a)⁻¹, -(C (b - a)⁻¹), ?_⟩
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  simp only [neg_mul, ← sub_eq_add_neg, ← mul_sub]
  rw [show (X - C a : k[X]) - (X - C b) = C b - C a from by ring,
      ← map_sub, ← map_mul, inv_mul_cancel₀ hba, map_one]

theorem polynomial_crt_two_points {a b c d : k} (hab : a ≠ b) :
    ∃ p : k[X], p.eval a = c ∧ p.eval b = d := by
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hba' : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  refine ⟨C c * (C (a - b)⁻¹ * (X - C b)) + C d * (C (b - a)⁻¹ * (X - C a)), ?_, ?_⟩
  · simp [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero,
          add_zero, inv_mul_cancel₀ hab', mul_one]
  · simp [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero,
          inv_mul_cancel₀ hba', mul_one]

theorem polynomial_crt_same_point {a c d : k} :
    (∃ p : k[X], p.eval a = c ∧ p.eval a = d) ↔ c = d := by
  constructor
  · rintro ⟨p, hc, hd⟩; exact hc.symm.trans hd
  · rintro rfl; exact ⟨C c, by simp, by simp⟩

theorem dvd_sub_C_eval (p : k[X]) (a : k) :
    (X - C a) ∣ (p - C (p.eval a)) := by
  rw [Polynomial.dvd_iff_isRoot]; simp [Polynomial.IsRoot, eval_sub, eval_C]

theorem polynomial_crt_uniqueness_mod {a₁ a₂ : k} (hab : a₁ ≠ a₂)
    {p q : k[X]} (hp₁ : p.eval a₁ = q.eval a₁) (hp₂ : p.eval a₂ = q.eval a₂) :
    (X - C a₁) * (X - C a₂) ∣ (p - q) := by
  have h₁ : (X - C a₁) ∣ (p - q) := by
    rw [Polynomial.dvd_iff_isRoot]; simp [Polynomial.IsRoot, eval_sub, hp₁]
  have h₂ : (X - C a₂) ∣ (p - q) := by
    rw [Polynomial.dvd_iff_isRoot]; simp [Polynomial.IsRoot, eval_sub, hp₂]
  exact (linear_factors_coprime hab).mul_dvd h₁ h₂

end PolynomialCRT

section PolynomialInduction

variable {k : Type*} [Field k]

theorem poly_crt_one_point (a b : k) : ∃ p : k[X], p.eval a = b :=
  ⟨C b, by simp⟩

theorem eval_ne_zero_of_coprime {m : k[X]} {a : k}
    (hcop : IsCoprime m (X - C a)) : m.eval a ≠ 0 := by
  intro heq
  have hdvd : (X - C a) ∣ m := Polynomial.dvd_iff_isRoot.mpr heq
  have hunit : IsUnit (X - C a : k[X]) := hcop.isUnit_of_dvd' hdvd (dvd_refl _)
  have h0 := Polynomial.natDegree_eq_zero_of_isUnit hunit
  rw [Polynomial.natDegree_X_sub_C] at h0
  exact absurd h0 one_ne_zero

theorem poly_crt_extend {a b : k} {m : k[X]}
    (hcop : IsCoprime m (X - C a)) (p₀ : k[X]) :
    ∃ q : k[X], m ∣ (q - p₀) ∧ q.eval a = b := by
  have hma : m.eval a ≠ 0 := eval_ne_zero_of_coprime hcop
  refine ⟨p₀ + m * C ((b - p₀.eval a) * (m.eval a)⁻¹), ?_, ?_⟩
  · exact ⟨C ((b - p₀.eval a) * (m.eval a)⁻¹), by ring⟩
  · simp only [eval_add, eval_mul, eval_C]
    rw [mul_comm (m.eval a), mul_assoc, inv_mul_cancel₀ hma, mul_one]
    ring

end PolynomialInduction

theorem crt_extension_summary : True := trivial

end ChineseRemainderNonCoprimeOQ02
