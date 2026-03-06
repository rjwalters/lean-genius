/-
# CRT Non-Coprime OQ-02: Extension to Polynomial Rings and PIDs

Extend the non-coprime Chinese Remainder Theorem from ℤ to:
1. **EuclideanDomains** — necessity, sufficiency, uniqueness via extended GCD
2. **Polynomial rings** — Lagrange interpolation as CRT specialization
3. **Ideal bridge** — element-level coprimality ↔ ideal-level coprimality

The CRT generalizes cleanly from ℤ to any EuclideanDomain:
  Given m, n in a EuclideanDomain R, and a, b in R:
  - Necessity: ∃ x, m ∣ (x - a) ∧ n ∣ (x - b) → gcd(m,n) ∣ (a - b)
  - Sufficiency: gcd(m,n) ∣ (a - b) → ∃ x solving both congruences
  - Uniqueness: Solutions are unique modulo lcm(m, n)

For polynomial rings over fields:
  (X - a) and (X - b) are coprime when a ≠ b, yielding Lagrange interpolation.

The ideal bridge shows:
  IsCoprime a b ↔ Ideal.span {a} ⊔ Ideal.span {b} = ⊤

References:
- Hungerford (1974): "Algebra", Chapter III
- Lang (2002): "Algebra", Chapter II
- Mathlib: RingTheory.Coprime.Basic, RingTheory.EuclideanDomain
-/
import Mathlib

set_option linter.unusedSectionVars false

namespace ChineseRemainderNonCoprimeOQ02

open Polynomial

/-
## Part I: CRT for EuclideanDomains
-/

section EuclideanDomainCRT

variable {R : Type*} [EuclideanDomain R] [DecidableEq R]

/-- Necessity: if x solves both congruences, then gcd(m,n) ∣ (a - b). -/
theorem ed_crt_necessary {m n a b : R}
    (h : ∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b)) :
    EuclideanDomain.gcd m n ∣ (a - b) := by
  obtain ⟨x, hm, hn⟩ := h
  have h1 := dvd_trans (EuclideanDomain.gcd_dvd_left m n) hm
  have h2 := dvd_trans (EuclideanDomain.gcd_dvd_right m n) hn
  have : EuclideanDomain.gcd m n ∣ ((x - b) - (x - a)) := dvd_sub h2 h1
  rwa [show (x - b) - (x - a) = a - b from by ring] at this

/-- Sufficiency: if gcd(m,n) ∣ (a - b), construct a solution via Bézout. -/
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

/-- The full iff: system solvable ↔ gcd divides difference. -/
theorem ed_crt_iff {m n a b : R} :
    (∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b)) ↔ EuclideanDomain.gcd m n ∣ (a - b) :=
  ⟨ed_crt_necessary, ed_crt_sufficient⟩

/-- Uniqueness: solutions agree modulo lcm(m, n). -/
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

/-- Coprime case: when gcd is a unit, system is always solvable. -/
theorem ed_crt_coprime {m n a b : R}
    (hcop : IsUnit (EuclideanDomain.gcd m n)) :
    ∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b) :=
  ed_crt_sufficient (hcop.dvd)

/-- Three moduli: pairwise gcd conditions are necessary. -/
theorem ed_crt_three_necessary {m n p a b c : R}
    (h : ∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b) ∧ p ∣ (x - c)) :
    EuclideanDomain.gcd m n ∣ (a - b) ∧
    EuclideanDomain.gcd m p ∣ (a - c) ∧
    EuclideanDomain.gcd n p ∣ (b - c) := by
  obtain ⟨x, hm, hn, hp⟩ := h
  exact ⟨ed_crt_necessary ⟨x, hm, hn⟩, ed_crt_necessary ⟨x, hm, hp⟩,
         ed_crt_necessary ⟨x, hn, hp⟩⟩

/-- Weakening: congruence mod m implies congruence mod any divisor of m. -/
theorem ed_crt_weaken (m m' a x : R)
    (hdvd : m' ∣ m) (h : m ∣ (x - a)) : m' ∣ (x - a) := dvd_trans hdvd h

/-- Combining: if x ≡ a mod m and x ≡ a mod n, then x ≡ a mod lcm(m,n). -/
theorem ed_crt_combine_same {m n a x : R}
    (hm : m ∣ (x - a)) (hn : n ∣ (x - a)) :
    EuclideanDomain.lcm m n ∣ (x - a) := EuclideanDomain.lcm_dvd hm hn

/-- Specialization to ℤ: the CRT iff for integers. -/
theorem int_crt_from_ed (m n a b : ℤ) :
    (∃ x : ℤ, m ∣ (x - a) ∧ n ∣ (x - b)) ↔ EuclideanDomain.gcd m n ∣ (a - b) := ed_crt_iff

/-- Specialization to ℤ: uniqueness for integers. -/
theorem int_crt_unique_from_ed (m n a b x y : ℤ)
    (hx : m ∣ (x - a) ∧ n ∣ (x - b))
    (hy : m ∣ (y - a) ∧ n ∣ (y - b)) :
    EuclideanDomain.lcm m n ∣ (x - y) := ed_crt_unique hx hy

end EuclideanDomainCRT

/-
## Part II: Polynomial Ring — Linear Factor Coprimality
-/

section PolynomialCRT

variable {k : Type*} [Field k]

/-- Over a field, (X - a) and (X - b) are coprime when a ≠ b.
    Proof via explicit Bézout coefficients. -/
theorem linear_factors_coprime {a b : k} (hab : a ≠ b) :
    IsCoprime (X - C a : k[X]) (X - C b) := by
  refine ⟨C (b - a)⁻¹, -(C (b - a)⁻¹), ?_⟩
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  simp only [neg_mul, ← sub_eq_add_neg, ← mul_sub]
  rw [show (X - C a : k[X]) - (X - C b) = C b - C a from by ring,
      ← map_sub, ← map_mul, inv_mul_cancel₀ hba, map_one]

/-- 2-point polynomial CRT (Lagrange interpolation): given distinct points,
    there exists an interpolating polynomial. -/
theorem polynomial_crt_two_points {a b c d : k} (hab : a ≠ b) :
    ∃ p : k[X], p.eval a = c ∧ p.eval b = d := by
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hba' : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  refine ⟨C c * (C (a - b)⁻¹ * (X - C b)) + C d * (C (b - a)⁻¹ * (X - C a)), ?_, ?_⟩
  · simp [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero,
          add_zero, inv_mul_cancel₀ hab', mul_one]
  · simp [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero,
          inv_mul_cancel₀ hba', mul_one]

/-- Same-point CRT: solvable iff targets agree. -/
theorem polynomial_crt_same_point {a c d : k} :
    (∃ p : k[X], p.eval a = c ∧ p.eval a = d) ↔ c = d := by
  constructor
  · rintro ⟨p, hc, hd⟩; exact hc.symm.trans hd
  · rintro rfl; exact ⟨C c, by simp, by simp⟩

/-- Factor theorem: (X - a) divides (p - C(p(a))). -/
theorem dvd_sub_C_eval (p : k[X]) (a : k) :
    (X - C a) ∣ (p - C (p.eval a)) := by
  rw [Polynomial.dvd_iff_isRoot]; simp [Polynomial.IsRoot, eval_sub, eval_C]

/-- Polynomial CRT uniqueness: if p and q agree at two distinct points,
    then (X - a₁)(X - a₂) divides (p - q). -/
theorem polynomial_crt_uniqueness_mod {a₁ a₂ : k} (hab : a₁ ≠ a₂)
    {p q : k[X]} (hp₁ : p.eval a₁ = q.eval a₁) (hp₂ : p.eval a₂ = q.eval a₂) :
    (X - C a₁) * (X - C a₂) ∣ (p - q) := by
  have h₁ : (X - C a₁) ∣ (p - q) := by
    rw [Polynomial.dvd_iff_isRoot]; simp [Polynomial.IsRoot, eval_sub, hp₁]
  have h₂ : (X - C a₂) ∣ (p - q) := by
    rw [Polynomial.dvd_iff_isRoot]; simp [Polynomial.IsRoot, eval_sub, hp₂]
  exact (linear_factors_coprime hab).mul_dvd h₁ h₂

end PolynomialCRT

/-
## Part III: Polynomial CRT Induction
-/

section PolynomialInduction

variable {k : Type*} [Field k]

/-- Base case: for any single point, the constant polynomial interpolates. -/
theorem poly_crt_one_point (a b : k) : ∃ p : k[X], p.eval a = b :=
  ⟨C b, by simp⟩

/-- If m and (X - a) are coprime, then m(a) ≠ 0. -/
theorem eval_ne_zero_of_coprime {m : k[X]} {a : k}
    (hcop : IsCoprime m (X - C a)) : m.eval a ≠ 0 := by
  intro heq
  have hdvd : (X - C a) ∣ m := Polynomial.dvd_iff_isRoot.mpr heq
  have hunit : IsUnit (X - C a : k[X]) := hcop.isUnit_of_dvd' hdvd (dvd_refl _)
  have h0 := Polynomial.natDegree_eq_zero_of_isUnit hunit
  rw [Polynomial.natDegree_X_sub_C] at h0
  exact absurd h0 one_ne_zero

/-- Inductive CRT step: extend a solution to one more linear factor.
    Given p₀ satisfying congruences mod m, adjust to also hit value b at a. -/
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

/-
## Part IV: Ideal Bridge — Element vs Ideal Coprimality

The fundamental bridge between element-level and ideal-level coprimality:
  IsCoprime a b ↔ Ideal.span {a} ⊔ Ideal.span {b} = ⊤

This connects the CRT to the ideal-theoretic perspective used in
algebraic number theory and commutative algebra.
-/

section IdealBridge

variable {R : Type*} [CommRing R]

/-- Element coprimality is equivalent to ideal coprimality:
    IsCoprime a b ↔ Ideal.span {a} ⊔ Ideal.span {b} = ⊤ -/
theorem isCoprime_iff_span_sup_eq_top (a b : R) :
    IsCoprime a b ↔ Ideal.span {a} ⊔ Ideal.span {b} = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  constructor
  · intro ⟨s, t, hst⟩
    rw [Submodule.mem_sup]
    refine ⟨a * s, Ideal.mem_span_singleton.mpr ⟨s, rfl⟩,
            b * t, Ideal.mem_span_singleton.mpr ⟨t, rfl⟩, ?_⟩
    linear_combination hst
  · intro h
    rw [Submodule.mem_sup] at h
    obtain ⟨u, hu, v, hv, huv⟩ := h
    rw [Ideal.mem_span_singleton] at hu hv
    obtain ⟨s, rfl⟩ := hu
    obtain ⟨t, rfl⟩ := hv
    exact ⟨s, t, by linear_combination huv⟩

/-- Euclid's lemma from coprimality: if a ∣ b*c and gcd(a,b) = 1, then a ∣ c. -/
theorem euclid_lemma_from_coprimality {a b c : R}
    (hcop : IsCoprime a b) (hdvd : a ∣ b * c) : a ∣ c :=
  IsCoprime.dvd_of_dvd_mul_left hcop hdvd

/-- If coprime, the product divides iff both factors divide (key for uniqueness). -/
theorem coprime_mul_dvd_iff {a b c : R} (hcop : IsCoprime a b) :
    a * b ∣ c ↔ a ∣ c ∧ b ∣ c :=
  ⟨fun h => ⟨dvd_trans (dvd_mul_right a b) h, dvd_trans (dvd_mul_left b a) h⟩,
   fun ⟨ha, hb⟩ => hcop.mul_dvd ha hb⟩

/-- Coprime CRT uniqueness via ideals: solutions agree mod a*b. -/
theorem coprime_crt_unique_ideal {a b r s x₁ x₂ : R}
    (hcop : IsCoprime a b)
    (h1a : a ∣ (x₁ - r)) (h1b : b ∣ (x₁ - s))
    (h2a : a ∣ (x₂ - r)) (h2b : b ∣ (x₂ - s)) :
    a * b ∣ (x₁ - x₂) := by
  have ha : a ∣ (x₁ - x₂) := by
    have := dvd_sub h1a h2a
    rwa [show (x₁ - r) - (x₂ - r) = x₁ - x₂ from by ring] at this
  have hb : b ∣ (x₁ - x₂) := by
    have := dvd_sub h1b h2b
    rwa [show (x₁ - s) - (x₂ - s) = x₁ - x₂ from by ring] at this
  exact hcop.mul_dvd ha hb

end IdealBridge

/-
## Part V: Summary Theorems
-/

/-- Summary: the full CRT for EuclideanDomains combines existence, uniqueness,
    and the ideal characterization. -/
theorem crt_oq02_summary {R : Type*} [CommRing R] [IsDomain R]
    {m n a b : R} (hcop : IsCoprime m n) :
    (∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b)) ∧
    (∀ x₁ x₂, m ∣ (x₁ - a) → n ∣ (x₁ - b) →
                m ∣ (x₂ - a) → n ∣ (x₂ - b) →
                m * n ∣ (x₁ - x₂)) ∧
    (Ideal.span {m} ⊔ Ideal.span {n} = ⊤) := by
  refine ⟨?_, ?_, (isCoprime_iff_span_sup_eq_top m n).mp hcop⟩
  · obtain ⟨s, t, hst⟩ := hcop
    refine ⟨a * (t * n) + b * (s * m), ?_, ?_⟩
    · refine ⟨s * (b - a), ?_⟩
      have h1 : t * n = 1 - s * m := by linear_combination hst
      rw [h1]; ring
    · refine ⟨t * (a - b), ?_⟩
      have h1 : s * m = 1 - t * n := by linear_combination hst
      rw [h1]; ring
  · intro x₁ x₂ h1m h1n h2m h2n
    exact coprime_crt_unique_ideal hcop h1m h1n h2m h2n

end ChineseRemainderNonCoprimeOQ02
