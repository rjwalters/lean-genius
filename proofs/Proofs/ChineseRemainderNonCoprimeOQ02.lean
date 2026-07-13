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

/-
## Part VI: PID Characterization — IsPrincipalIdealRing Bridge
-/

section PIDbridge

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/-- In a PID, every ideal is principal: ∃ a, I = Ideal.span {a}.
    This is the structural property that makes CRT work in PIDs. -/
theorem pid_ideal_principal (I : Ideal R) :
    ∃ a : R, I = Ideal.span {a} :=
  ⟨Submodule.IsPrincipal.generator I,
   (Submodule.IsPrincipal.span_singleton_generator I).symm⟩

/-- Two coprime elements in a PID satisfy Bézout's identity. -/
theorem pid_bezout {a b : R} (hcop : IsCoprime a b) :
    ∃ s t : R, s * a + t * b = 1 := by
  obtain ⟨s, t, hst⟩ := hcop
  exact ⟨s, t, hst⟩

/-- CRT solvability in PIDs: coprime implies solvable (always). -/
theorem pid_crt_coprime_solvable {m n a b : R} (hcop : IsCoprime m n) :
    ∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b) := by
  obtain ⟨s, t, hst⟩ := hcop
  refine ⟨a * (t * n) + b * (s * m), ?_, ?_⟩
  · refine ⟨s * (b - a), ?_⟩
    have key : t * n = 1 - s * m := by linear_combination hst
    linear_combination a * key
  · refine ⟨t * (a - b), ?_⟩
    have key : s * m = 1 - t * n := by linear_combination hst
    linear_combination b * key

/-- CRT uniqueness in PIDs: coprime → solutions unique mod m*n. -/
theorem pid_crt_coprime_unique {m n a b x₁ x₂ : R}
    (hcop : IsCoprime m n)
    (h1 : m ∣ (x₁ - a) ∧ n ∣ (x₁ - b))
    (h2 : m ∣ (x₂ - a) ∧ n ∣ (x₂ - b)) :
    m * n ∣ (x₁ - x₂) :=
  coprime_crt_unique_ideal hcop h1.1 h1.2 h2.1 h2.2

end PIDbridge

/-
## Part VII: Polynomial Degree Bounds for CRT Interpolation
-/

section DegBounds

variable {k : Type*} [Field k]

/-- The interpolating polynomial for 2 points can be chosen with degree ≤ 1.
    This is the Lagrange interpolation bound. -/
theorem polynomial_crt_two_degree_bound {a b c d : k} (hab : a ≠ b) :
    ∃ p : k[X], p.eval a = c ∧ p.eval b = d ∧ p.natDegree ≤ 1 := by
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hba' : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  -- Construct the linear interpolating polynomial explicitly
  refine ⟨C ((c * b - d * a) * (b - a)⁻¹) + C ((d - c) * (b - a)⁻¹) * X, ?_, ?_, ?_⟩
  · simp [eval_add, eval_mul, eval_C, eval_X]
    field_simp
    ring
  · simp [eval_add, eval_mul, eval_C, eval_X]
    field_simp
    ring
  · apply le_trans (Polynomial.natDegree_add_le _ _)
    apply max_le
    · rw [Polynomial.natDegree_C]; exact Nat.zero_le _
    · exact le_trans Polynomial.natDegree_mul_le
        (by rw [Polynomial.natDegree_C, Polynomial.natDegree_X])

/-- Constant interpolation: single-point CRT yields degree 0 polynomials. -/
theorem polynomial_crt_one_degree_bound (a b : k) :
    ∃ p : k[X], p.eval a = b ∧ p.natDegree = 0 :=
  ⟨C b, by simp, Polynomial.natDegree_C b⟩

end DegBounds

/-
## Part VIII: Coprime Transitivity and Chain Properties
-/

section CoprimeChain

variable {R : Type*} [CommRing R]

/-- If a is coprime to both b and c, then a is coprime to b*c.
    This enables building coprime chains for multi-moduli CRT. -/
theorem coprime_mul_of_coprime {a b c : R}
    (hab : IsCoprime a b) (hac : IsCoprime a c) :
    IsCoprime a (b * c) := hab.mul_right hac

/-- Coprimality is symmetric. -/
theorem coprime_symm {a b : R} (h : IsCoprime a b) : IsCoprime b a :=
  h.symm

/-- Self-coprimality implies unit. -/
theorem coprime_self_iff_unit (a : R) : IsCoprime a a ↔ IsUnit a := by
  constructor
  · exact fun h => h.isUnit_of_dvd' (dvd_refl a) (dvd_refl a)
  · intro ⟨u, hu⟩
    refine ⟨↑u⁻¹, 0, ?_⟩
    rw [zero_mul, add_zero, ← hu]
    exact_mod_cast u.inv_mul

/-- Coprime and divides implies coprime to divisor. -/
theorem coprime_of_dvd_right {a b c : R}
    (h : IsCoprime a b) (hbc : c ∣ b) : IsCoprime a c := by
  obtain ⟨s, t, hst⟩ := h
  obtain ⟨q, hq⟩ := hbc
  exact ⟨s, t * q, by rw [hq] at hst; linear_combination hst⟩

end CoprimeChain

/-
## Part IX: Structural Results for Non-Coprime CRT
-/

section StructuralResults

variable {R : Type*} [EuclideanDomain R] [DecidableEq R]

/-- The non-coprime CRT subsumes the coprime CRT:
    when gcd(m,n) is a unit, the divisibility condition is trivially satisfied. -/
theorem coprime_implies_crt_solvable {m n a b : R}
    (hcop : IsUnit (EuclideanDomain.gcd m n)) :
    ∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b) :=
  ed_crt_coprime hcop

/-- Contrapositive of necessity: if gcd(m,n) ∤ (a-b), NO solution exists. -/
theorem ed_crt_impossible {m n a b : R}
    (h : ¬ EuclideanDomain.gcd m n ∣ (a - b)) :
    ¬ ∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b) :=
  fun hsol => h (ed_crt_necessary hsol)

/-- Reflexivity: x ≡ a mod m always has the trivial solution x = a. -/
theorem ed_crt_refl (m a : R) : m ∣ (a - a) := by rw [sub_self]; exact dvd_zero m

/-- Transitivity: if m | (x - a) and m | (a - b), then m | (x - b). -/
theorem ed_crt_trans {m x a b : R} (h1 : m ∣ (x - a)) (h2 : m ∣ (a - b)) :
    m ∣ (x - b) := by
  have := dvd_add h1 h2
  rwa [show (x - a) + (a - b) = x - b from by ring] at this

end StructuralResults

/-
## Part X: Coprime Multi-Moduli CRT
-/

section MultiModuliCoprime

variable {R : Type*} [CommRing R]

/-- Coprime CRT for three pairwise coprime moduli. Uses the CRT basis element
    construction: for pairwise coprime m₁, m₂, m₃:
      e₁ = t₁·(m₂·m₃), where s₁·m₁ + t₁·(m₂·m₃) = 1
    Then x = a₁·e₁ + a₂·e₂ + a₃·e₃ solves the system. -/
theorem coprime_crt_three {m₁ m₂ m₃ a₁ a₂ a₃ : R}
    (h12 : IsCoprime m₁ m₂) (h13 : IsCoprime m₁ m₃) (h23 : IsCoprime m₂ m₃) :
    ∃ x : R, m₁ ∣ (x - a₁) ∧ m₂ ∣ (x - a₂) ∧ m₃ ∣ (x - a₃) := by
  have h1_23 : IsCoprime m₁ (m₂ * m₃) := h12.mul_right h13
  have h2_13 : IsCoprime m₂ (m₁ * m₃) := h12.symm.mul_right h23
  have h3_12 : IsCoprime m₃ (m₁ * m₂) := h13.symm.mul_right h23.symm
  obtain ⟨s₁, t₁, ht₁⟩ := h1_23
  obtain ⟨s₂, t₂, ht₂⟩ := h2_13
  obtain ⟨s₃, t₃, ht₃⟩ := h3_12
  refine ⟨a₁ * (t₁ * (m₂ * m₃)) + a₂ * (t₂ * (m₁ * m₃)) + a₃ * (t₃ * (m₁ * m₂)),
    ?_, ?_, ?_⟩
  · -- m₁ | (x - a₁): t₁·m₂·m₃ ≡ 1 mod m₁, so x ≡ a₁·1 + a₂·0 + a₃·0 = a₁ mod m₁
    refine ⟨a₂ * (t₂ * m₃) + a₃ * (t₃ * m₂) - a₁ * s₁, ?_⟩
    have : t₁ * (m₂ * m₃) = 1 - s₁ * m₁ := by linear_combination ht₁
    linear_combination a₁ * this
  · -- m₂ | (x - a₂): similarly
    refine ⟨a₁ * (t₁ * m₃) + a₃ * (t₃ * m₁) - a₂ * s₂, ?_⟩
    have : t₂ * (m₁ * m₃) = 1 - s₂ * m₂ := by linear_combination ht₂
    linear_combination a₂ * this
  · -- m₃ | (x - a₃): similarly
    refine ⟨a₁ * (t₁ * m₂) + a₂ * (t₂ * m₁) - a₃ * s₃, ?_⟩
    have : t₃ * (m₁ * m₂) = 1 - s₃ * m₃ := by linear_combination ht₃
    linear_combination a₃ * this

/-- Uniqueness for three coprime moduli: solutions agree mod m₁*m₂*m₃. -/
theorem coprime_crt_three_unique {m₁ m₂ m₃ a₁ a₂ a₃ x₁ x₂ : R}
    (h12 : IsCoprime m₁ m₂) (h13 : IsCoprime m₁ m₃) (h23 : IsCoprime m₂ m₃)
    (hx₁ : m₁ ∣ (x₁ - a₁) ∧ m₂ ∣ (x₁ - a₂) ∧ m₃ ∣ (x₁ - a₃))
    (hx₂ : m₁ ∣ (x₂ - a₁) ∧ m₂ ∣ (x₂ - a₂) ∧ m₃ ∣ (x₂ - a₃)) :
    m₁ * m₂ * m₃ ∣ (x₁ - x₂) := by
  have h1 : m₁ ∣ (x₁ - x₂) := by
    have := dvd_sub hx₁.1 hx₂.1
    rwa [show (x₁ - a₁) - (x₂ - a₁) = x₁ - x₂ from by ring] at this
  have h2 : m₂ ∣ (x₁ - x₂) := by
    have := dvd_sub hx₁.2.1 hx₂.2.1
    rwa [show (x₁ - a₂) - (x₂ - a₂) = x₁ - x₂ from by ring] at this
  have h3 : m₃ ∣ (x₁ - x₂) := by
    have := dvd_sub hx₁.2.2 hx₂.2.2
    rwa [show (x₁ - a₃) - (x₂ - a₃) = x₁ - x₂ from by ring] at this
  have h12' : m₁ * m₂ ∣ (x₁ - x₂) := h12.mul_dvd h1 h2
  exact (h13.symm.mul_right h23.symm).symm.mul_dvd h12' h3

end MultiModuliCoprime

/-
## Part XI: Ideal-Theoretic CRT (General Commutative Rings)

The most general formulation of the CRT, working for arbitrary ideals
in any commutative ring R.  No coprimality, no Euclidean structure needed.

  Solvability:  ∃ x, (x - a) ∈ I ∧ (x - b) ∈ J  ↔  (a - b) ∈ I ⊔ J
  Uniqueness:   solutions agree modulo I ⊓ J

This subsumes all previous results:
- Element CRT: take I = Ideal.span {m}, J = Ideal.span {n}
- Coprime case: I ⊔ J = ⊤ makes solvability automatic
- Non-coprime case: solvability depends on whether a - b ∈ I + J
- Uniqueness: I ⊓ J generalizes lcm for principal ideals
-/

section IdealCRT

variable {R : Type*} [CommRing R]

/-- Ideal CRT necessity: if x solves both congruences, then a - b ∈ I + J.
    Proof: a - b = -(x - a) + (x - b), with the first term in I and second in J. -/
theorem ideal_crt_necessary {I J : Ideal R} {a b : R}
    (h : ∃ x : R, (x - a) ∈ I ∧ (x - b) ∈ J) :
    (a - b) ∈ I ⊔ J := by
  obtain ⟨x, hI, hJ⟩ := h
  rw [Submodule.mem_sup]
  exact ⟨-(x - a), I.neg_mem hI, x - b, hJ, by ring⟩

/-- Ideal CRT sufficiency: if a - b ∈ I + J, construct a solution.
    Write a - b = i + j, then x = a - i works. -/
theorem ideal_crt_sufficient {I J : Ideal R} {a b : R}
    (h : (a - b) ∈ I ⊔ J) :
    ∃ x : R, (x - a) ∈ I ∧ (x - b) ∈ J := by
  rw [Submodule.mem_sup] at h
  obtain ⟨i, hi, j, hj, hij⟩ := h
  refine ⟨a - i, ?_, ?_⟩
  · show -i ∈ I
    exact I.neg_mem hi
  · show a - i - b ∈ J
    have : a - i - b = j := by linarith
    rw [this]
    exact hj

/-- Ideal CRT iff: system solvable ↔ a - b ∈ I ⊔ J.
    This is the fully general non-coprime CRT for arbitrary ideals. -/
theorem ideal_crt_iff {I J : Ideal R} {a b : R} :
    (∃ x : R, (x - a) ∈ I ∧ (x - b) ∈ J) ↔ (a - b) ∈ I ⊔ J :=
  ⟨ideal_crt_necessary, ideal_crt_sufficient⟩

/-- Ideal CRT uniqueness: any two solutions agree modulo I ∩ J. -/
theorem ideal_crt_unique {I J : Ideal R} {a b x₁ x₂ : R}
    (h₁ : (x₁ - a) ∈ I ∧ (x₁ - b) ∈ J)
    (h₂ : (x₂ - a) ∈ I ∧ (x₂ - b) ∈ J) :
    (x₁ - x₂) ∈ I ⊓ J := by
  rw [Submodule.mem_inf]
  constructor
  · have := I.sub_mem h₁.1 h₂.1
    rwa [show (x₁ - a) - (x₂ - a) = x₁ - x₂ from by ring] at this
  · have := J.sub_mem h₁.2 h₂.2
    rwa [show (x₁ - b) - (x₂ - b) = x₁ - x₂ from by ring] at this

/-- Coprime ideal CRT: when I + J = R, the system is always solvable.
    This recovers the classical CRT as a special case. -/
theorem ideal_crt_coprime {I J : Ideal R} {a b : R}
    (hcop : I ⊔ J = ⊤) :
    ∃ x : R, (x - a) ∈ I ∧ (x - b) ∈ J :=
  ideal_crt_sufficient (hcop ▸ Submodule.mem_top)

/-- Ideal CRT for three ideals: necessity of pairwise conditions. -/
theorem ideal_crt_three_necessary {I J K : Ideal R} {a b c : R}
    (h : ∃ x : R, (x - a) ∈ I ∧ (x - b) ∈ J ∧ (x - c) ∈ K) :
    (a - b) ∈ I ⊔ J ∧ (a - c) ∈ I ⊔ K ∧ (b - c) ∈ J ⊔ K := by
  obtain ⟨x, hI, hJ, hK⟩ := h
  exact ⟨ideal_crt_necessary ⟨x, hI, hJ⟩,
         ideal_crt_necessary ⟨x, hI, hK⟩,
         ideal_crt_necessary ⟨x, hJ, hK⟩⟩

/-- Ideal CRT uniqueness for three ideals: solutions agree mod I ∩ J ∩ K. -/
theorem ideal_crt_three_unique {I J K : Ideal R} {a b c x₁ x₂ : R}
    (h₁ : (x₁ - a) ∈ I ∧ (x₁ - b) ∈ J ∧ (x₁ - c) ∈ K)
    (h₂ : (x₂ - a) ∈ I ∧ (x₂ - b) ∈ J ∧ (x₂ - c) ∈ K) :
    (x₁ - x₂) ∈ I ⊓ J ⊓ K := by
  rw [Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · exact (ideal_crt_unique ⟨h₁.1, h₁.2.1⟩ ⟨h₂.1, h₂.2.1⟩).1
  · have := K.sub_mem h₁.2.2 h₂.2.2
    rwa [show (x₁ - c) - (x₂ - c) = x₁ - x₂ from by ring] at this

end IdealCRT

/-
## Part XII: Connecting Ideal CRT to Element CRT

Show that the ideal-theoretic CRT applied to principal ideals
recovers the element-level CRT from Parts I and IV.
-/

section IdealElementBridge

variable {R : Type*} [CommRing R]

/-- Principal ideal membership: x ∈ Ideal.span {m} ↔ m ∣ x. -/
theorem mem_span_singleton_iff_dvd (m x : R) :
    x ∈ Ideal.span {m} ↔ m ∣ x :=
  Ideal.mem_span_singleton.trans ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩,
                                  fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

/-- Element CRT from ideal CRT: solvability via principal ideals.
    The element-level CRT (Part I for EDs) is a special case of the ideal CRT
    applied to Ideal.span {m} and Ideal.span {n}. -/
theorem element_crt_from_ideal {m n a b : R}
    (h : (a - b) ∈ Ideal.span ({m} : Set R) ⊔ Ideal.span {n}) :
    ∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b) := by
  obtain ⟨x, hI, hJ⟩ := ideal_crt_sufficient h
  exact ⟨x, (mem_span_singleton_iff_dvd m _).mp hI,
            (mem_span_singleton_iff_dvd n _).mp hJ⟩

/-- Coprime elements yield coprime principal ideals.
    This bridges IsCoprime (element) with I ⊔ J = ⊤ (ideal). -/
theorem span_sup_top_of_isCoprime {m n : R} (h : IsCoprime m n) :
    Ideal.span ({m} : Set R) ⊔ Ideal.span {n} = ⊤ :=
  (isCoprime_iff_span_sup_eq_top m n).mp h

/-- Element CRT uniqueness from ideal CRT: solutions agree mod elements
    whose span is I ∩ J.  For principal ideals, I ∩ J = Ideal.span {lcm(m,n)}
    in a GCD domain. -/
theorem element_crt_unique_from_ideal {m n a b x₁ x₂ : R}
    (h₁ : m ∣ (x₁ - a) ∧ n ∣ (x₁ - b))
    (h₂ : m ∣ (x₂ - a) ∧ n ∣ (x₂ - b)) :
    (x₁ - x₂) ∈ Ideal.span ({m} : Set R) ⊓ Ideal.span {n} := by
  apply ideal_crt_unique
  · exact ⟨(mem_span_singleton_iff_dvd m _).mpr h₁.1,
           (mem_span_singleton_iff_dvd n _).mpr h₁.2⟩
  · exact ⟨(mem_span_singleton_iff_dvd m _).mpr h₂.1,
           (mem_span_singleton_iff_dvd n _).mpr h₂.2⟩

/-- The ideal-theoretic coprime CRT instantiated for elements:
    if IsCoprime m n, the element-level system is always solvable. -/
theorem element_coprime_crt_from_ideal {m n a b : R}
    (hcop : IsCoprime m n) :
    ∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b) :=
  element_crt_from_ideal (span_sup_top_of_isCoprime hcop ▸ Submodule.mem_top)

end IdealElementBridge

/-
## Part XIII: Non-Coprime CRT for PIDs via Ideal Theory

In a PID, every ideal is principal.  The ideal CRT then gives:
- Solvability: a - b ∈ ⟨m⟩ + ⟨n⟩ = ⟨gcd(m,n)⟩ ↔ gcd(m,n) ∣ (a - b)
- Uniqueness: mod ⟨m⟩ ∩ ⟨n⟩ = ⟨lcm(m,n)⟩

This closes the gap: the PID bridge (Part VI) only handled coprime.
Now we have non-coprime CRT for PIDs too.
-/

section NonCoprimePID

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/-- In a PID, the sum of two principal ideals is principal (generated by gcd).
    This is the key structural fact enabling non-coprime CRT in PIDs. -/
theorem pid_span_sup_principal (m n : R) :
    ∃ g : R, Ideal.span ({m} : Set R) ⊔ Ideal.span {n} = Ideal.span {g} := by
  exact pid_ideal_principal _

/-- Non-coprime CRT for PIDs: solvability in terms of ideal membership.
    The system x ≡ a mod m, x ≡ b mod n is solvable iff
    a - b lies in the ideal generated by m and n (= ⟨gcd(m,n)⟩ in a PID). -/
theorem pid_noncoprime_crt_iff {m n a b : R} :
    (∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b)) ↔
    (a - b) ∈ Ideal.span ({m} : Set R) ⊔ Ideal.span {n} := by
  constructor
  · intro ⟨x, hm, hn⟩
    exact ideal_crt_necessary ⟨x,
      (mem_span_singleton_iff_dvd m _).mpr hm,
      (mem_span_singleton_iff_dvd n _).mpr hn⟩
  · exact element_crt_from_ideal

/-- Non-coprime PID CRT uniqueness: solutions agree mod I ∩ J.
    In a PID, I ∩ J = ⟨lcm(m,n)⟩ for principal ideals. -/
theorem pid_noncoprime_crt_unique {m n a b x₁ x₂ : R}
    (h₁ : m ∣ (x₁ - a) ∧ n ∣ (x₁ - b))
    (h₂ : m ∣ (x₂ - a) ∧ n ∣ (x₂ - b)) :
    (x₁ - x₂) ∈ Ideal.span ({m} : Set R) ⊓ Ideal.span {n} :=
  element_crt_unique_from_ideal h₁ h₂

/-- A PID is an integral domain where every ideal is principal — hence
    the full CRT (coprime and non-coprime) applies to all PIDs:
    ℤ, k[X], ℤ[i], etc.  This summary combines existence and uniqueness. -/
theorem pid_noncoprime_crt_full {m n a b : R}
    (h : (a - b) ∈ Ideal.span ({m} : Set R) ⊔ Ideal.span {n}) :
    (∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b)) ∧
    (∀ x₁ x₂, m ∣ (x₁ - a) → n ∣ (x₁ - b) →
                m ∣ (x₂ - a) → n ∣ (x₂ - b) →
                (x₁ - x₂) ∈ Ideal.span ({m} : Set R) ⊓ Ideal.span {n}) :=
  ⟨element_crt_from_ideal h,
   fun _ _ h1m h1n h2m h2n => element_crt_unique_from_ideal ⟨h1m, h1n⟩ ⟨h2m, h2n⟩⟩

end NonCoprimePID

end ChineseRemainderNonCoprimeOQ02
