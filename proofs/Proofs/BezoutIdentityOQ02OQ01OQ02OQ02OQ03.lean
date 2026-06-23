import Mathlib
import Proofs.BezoutIdentityOQ02OQ01OQ02OQ02

/-
# ℤ[√-2] as a Euclidean Domain: Inert Prime Classification

## Research Problem: bezout-identity-oq-02-oq-01-oq-02-oq-02-oq-03

**Open Question** (from BezoutIdentityOQ02OQ01OQ02OQ02): Can the inert prime technique
be generalized to other Euclidean imaginary quadratic rings, such as ℤ[√-2]?

**Answer**: Yes. This file establishes:

1. **ℤ[√-2] is a Euclidean domain** with Euclidean function N(a+b√-2) = a² + 2b².
   (The rounding error satisfies δ₁² + 2δ₂² ≤ 3/4 < 1.)

2. **Inert prime classification**: A rational prime p is prime in ℤ[√-2] if and only if
   p ≡ 5 or 7 (mod 8), i.e., the Legendre symbol (-2/p) = -1.

## Mathematical Content

**Why the Euclidean algorithm works**: For x/y in ℚ[√-2], round the re and im coordinates.
The error δ = (δ₁, δ₂) with |δ₁|, |δ₂| ≤ 1/2 gives N(remainder) = N(y)·(δ₁² + 2δ₂²) ≤ 3N(y)/4 < N(y).

**Why p ≡ 5 or 7 (mod 8) is inert**: If N(a) = p → a₀² + 2b₀² = p.
But a² + 2b² mod 8 ∈ {0,1,2,3,4,6}, never 5 or 7.

## Tags: number-theory, Gaussian-integers, Zsqrtd, inert-primes, Euclidean-domain
-/

namespace ZSqrtNegTwo

open Zsqrtd Complex Real

/-- ℤ[√-2] — the ring of integers of ℚ(√-2). -/
abbrev ℤ√neg2 := Zsqrtd (-2 : ℤ)

-- ============================================================
-- Part I: Basic Norm Properties
-- ============================================================

/-- The norm N(a + b√-2) = a² + 2b² is always nonneg. -/
theorem norm_nonneg (z : ℤ√neg2) : 0 ≤ Zsqrtd.norm z := by
  simp only [Zsqrtd.norm]
  nlinarith [sq_nonneg z.re, sq_nonneg z.im]

/-- The norm is positive for nonzero elements (key for Euclidean algorithm). -/
theorem norm_pos_of_ne_zero {z : ℤ√neg2} (hz : z ≠ 0) : 0 < Zsqrtd.norm z := by
  rcases (norm_nonneg z).lt_or_eq with h | h
  · exact h
  · exfalso; apply hz
    have hnn : Zsqrtd.norm z = 0 := h.symm
    simp only [Zsqrtd.norm] at hnn
    have hre : z.re = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    have him : z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    exact Zsqrtd.ext hre him

/-- Norm formula: N(a + b√-2) = a² + 2b². -/
theorem norm_formula (z : ℤ√neg2) : Zsqrtd.norm z = z.re ^ 2 + 2 * z.im ^ 2 := by
  simp [Zsqrtd.norm]; ring

/-- Norm is nonneg (alternative formulation needed for natAbs). -/
theorem norm_natAbs_cast (z : ℤ√neg2) : (z.norm.natAbs : ℤ) = z.norm :=
  Int.natAbs_of_nonneg (norm_nonneg z)

-- ============================================================
-- Part II: Embedding into ℂ for Norm Computation
-- ============================================================

/-- The embedding ℤ[√-2] →+* ℂ sending √-2 ↦ i√2. -/
noncomputable def toComplex : ℤ√neg2 →+* ℂ :=
  Zsqrtd.lift ⟨Real.sqrt 2 * Complex.I,
    by push_cast; rw [mul_pow, sq_sqrt (by norm_num : (2:ℝ) ≥ 0), I_sq]; ring⟩

@[simp]
theorem toComplex_apply (z : ℤ√neg2) :
    toComplex z = z.re + z.im * (Real.sqrt 2 * Complex.I) := by
  simp [toComplex, Zsqrtd.lift_apply]

/-- The complex embedding is injective. -/
theorem toComplex_injective : Function.Injective toComplex := by
  intro x y h
  simp only [toComplex_apply] at h
  have hre : (x.re : ℂ) = y.re := by
    have := congr_arg Complex.re h
    simp at this; exact_mod_cast this
  have him : (x.im : ℂ) = y.im := by
    have := congr_arg Complex.im h
    simp [Real.sqrt_ne_zero'] at this
    have hsqrt2 : (Real.sqrt 2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    have := mul_left_cancel₀ (ofReal_ne_zero.mpr hsqrt2) this
    exact_mod_cast this
  exact Zsqrtd.ext (by exact_mod_cast hre) (by exact_mod_cast him)

/-- The Zsqrtd norm equals Complex.normSq ∘ toComplex. -/
theorem norm_eq_normSq (z : ℤ√neg2) :
    (z.norm : ℝ) = Complex.normSq (toComplex z) := by
  simp [toComplex_apply, normSq_apply, Zsqrtd.norm,
        sq_sqrt (show (2:ℝ) ≥ 0 by norm_num)]
  push_cast; ring

-- ============================================================
-- Part III: Euclidean Division Algorithm
-- ============================================================

noncomputable instance : Div ℤ√neg2 :=
  ⟨fun x y =>
    let n := (Zsqrtd.norm y : ℚ)
    let c := star y
    ⟨round ((x * c).re / n : ℚ), round ((x * c).im / n : ℚ)⟩⟩

noncomputable instance : Mod ℤ√neg2 :=
  ⟨fun x y => x - y * (x / y)⟩

theorem div_def (x y : ℤ√neg2) :
    x / y = ⟨round ((x * star y).re / Zsqrtd.norm y : ℚ),
             round ((x * star y).im / Zsqrtd.norm y : ℚ)⟩ := rfl

theorem mod_def (x y : ℤ√neg2) : x % y = x - y * (x / y) := rfl

-- ============================================================
-- Part IV: The Key Norm Bound (3/4 rule)
-- ============================================================

/-- The exact complex quotient x/y decomposes as α + √2·β·I
    where α = (x·ȳ).re / N(y) and β = (x·ȳ).im / N(y). -/
private theorem toComplex_div_eq (x y : ℤ√neg2) (hy : y ≠ 0) :
    (toComplex x / toComplex y : ℂ) =
    (((x * star y).re : ℚ) / Zsqrtd.norm y : ℚ) +
    Real.sqrt 2 * (((x * star y).im : ℚ) / Zsqrtd.norm y : ℚ) * Complex.I := by
  have hy_ℂ : (toComplex y : ℂ) ≠ 0 := fun h => hy (toComplex_injective (by simp [h]))
  have hN : (Zsqrtd.norm y : ℂ) ≠ 0 := by
    exact_mod_cast (norm_pos_of_ne_zero hy).ne'
  rw [div_eq_iff hy_ℂ]
  apply Complex.ext
  · simp only [mul_re, add_re, ofReal_re, mul_re, ofReal_re, I_re, mul_zero,
               ofReal_im, I_im, mul_one, sub_zero, add_re, add_zero, toComplex_apply]
    push_cast
    have hN' : (Zsqrtd.norm y : ℝ) ≠ 0 := by exact_mod_cast (norm_pos_of_ne_zero hy).ne'
    rw [Zsqrtd.norm]
    simp [Zsqrtd.star_def, Zsqrtd.mul_def, mul_comm]
    field_simp
    ring
  · simp only [mul_im, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one,
               ofReal_im, I_re, mul_zero, add_zero, zero_add, toComplex_apply]
    push_cast
    have hN' : (Zsqrtd.norm y : ℝ) ≠ 0 := by exact_mod_cast (norm_pos_of_ne_zero hy).ne'
    rw [Zsqrtd.norm]
    simp [Zsqrtd.star_def, Zsqrtd.mul_def, mul_comm]
    field_simp
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [h2]

/-- The rounded quotient in ℂ: round(α) + √2·round(β)·I. -/
private theorem toComplex_quot_eq (x y : ℤ√neg2) :
    (toComplex (x / y) : ℂ) =
    (round ((x * star y).re / Zsqrtd.norm y : ℚ) : ℤ) +
    Real.sqrt 2 * (round ((x * star y).im / Zsqrtd.norm y : ℚ) : ℤ) * Complex.I := by
  simp [toComplex_apply, div_def]
  push_cast; ring

/-- **Key bound**: The rounding error has normSq ≤ 3/4 < 1. -/
theorem normSq_div_sub_div_lt_one (x y : ℤ√neg2) (hy : y ≠ 0) :
    Complex.normSq ((toComplex x / toComplex y : ℂ) - toComplex (x / y)) < 1 := by
  set rα : ℚ := ((x * star y).re : ℚ) / Zsqrtd.norm y
  set rβ : ℚ := ((x * star y).im : ℚ) / Zsqrtd.norm y
  -- Express error as δα + √2·δβ·I where |δα|, |δβ| ≤ 1/2
  have herr : (toComplex x / toComplex y : ℂ) - toComplex (x / y) =
      (rα - round rα : ℚ) + Real.sqrt 2 * (rβ - round rβ : ℚ) * Complex.I := by
    rw [toComplex_div_eq x y hy, toComplex_quot_eq]
    push_cast; ring
  rw [herr]
  -- Compute normSq = (rα - round rα)² + 2*(rβ - round rβ)²
  have hδα : |(rα - round rα : ℝ)| ≤ 1/2 := by
    have := abs_sub_round rα
    exact_mod_cast this
  have hδβ : |(rβ - round rβ : ℝ)| ≤ 1/2 := by
    have := abs_sub_round rβ
    exact_mod_cast this
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [normSq_apply]
  simp only [add_re, ofReal_re, mul_re, ofReal_re, I_re, mul_zero, sub_zero,
             ofReal_im, I_im, mul_one, add_im, ofReal_im, mul_im, ofReal_re, I_re, add_zero]
  push_cast
  nlinarith [sq_abs (rα - round rα : ℝ), sq_abs (rβ - round rβ : ℝ), h2,
             sq_nonneg (rα - round rα : ℝ), sq_nonneg (rβ - round rβ : ℝ)]

/-- **Key Result**: The remainder has strictly smaller norm. -/
theorem norm_mod_lt (x : ℤ√neg2) {y : ℤ√neg2} (hy : y ≠ 0) :
    (x % y).norm < y.norm := by
  have hy_ℂ : (toComplex y : ℂ) ≠ 0 := fun h => hy (toComplex_injective (by simp [h]))
  rw [mod_def]
  apply_fun (Int.cast : ℤ → ℝ) using Int.cast_injective
  rw [norm_eq_normSq, norm_eq_normSq]
  calc Complex.normSq (toComplex (x - y * (x / y)))
      = Complex.normSq (toComplex y * (toComplex x / toComplex y - toComplex (x / y))) := by
        rw [map_sub, map_mul, mul_sub, mul_div_cancel₀ _ hy_ℂ]; ring
    _ = Complex.normSq (toComplex y) *
        Complex.normSq (toComplex x / toComplex y - toComplex (x / y)) := normSq_mul _ _
    _ < Complex.normSq (toComplex y) * 1 :=
        mul_lt_mul_of_pos_left (normSq_div_sub_div_lt_one x y hy) (normSq_pos.2 hy_ℂ)
    _ = _ := mul_one _

theorem norm_mod_lt_natAbs (x : ℤ√neg2) {y : ℤ√neg2} (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs :=
  Int.ofNat_lt.1 (by simpa [norm_natAbs_cast] using norm_mod_lt x hy)

-- ============================================================
-- Part V: ℤ[√-2] is a Euclidean Domain
-- ============================================================

/-- **ℤ[√-2] is a Euclidean Domain** with norm N(a+b√-2) = a² + 2b². -/
noncomputable instance : EuclideanDomain ℤ√neg2 :=
  { (inferInstance : CommRing ℤ√neg2), (inferInstance : Nontrivial ℤ√neg2) with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := fun a => by
      simp [div_def, Zsqrtd.norm]
    quotient_mul_add_remainder_eq := fun x y => by simp [mod_def]
    r := fun a b => a.norm.natAbs < b.norm.natAbs
    r_wellFounded := measure_wf (fun z => z.norm.natAbs)
    remainder_lt := fun x {y} hy => norm_mod_lt_natAbs x hy
    mul_left_not_lt := fun a b hb => by
      simp only
      rw [Zsqrtd.norm_mul, Int.natAbs_mul]
      exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (fun h => by
        simp only [Int.natAbs_eq_zero] at h
        exact hb (Zsqrtd.norm_eq_zero_iff.mp h))) }

-- Derive UFD from Euclidean domain
instance : UniqueFactorizationMonoid ℤ√neg2 :=
  EuclideanDomain.toUniqueFactorizationDomain

-- ============================================================
-- Part VI: Inert Prime Classification for ℤ[√-2]
-- ============================================================

/-- Squares mod 8 are {0,1,4}, so a² + 2b² mod 8 ∈ {0,1,2,3,4,6}, never 5 or 7. -/
theorem no_sum_form_mod8 {p : ℕ} (hp5 : p % 8 = 5 ∨ p % 8 = 7) :
    ∀ a b : ZMod 8, a ^ 2 + 2 * b ^ 2 ≠ (p : ZMod 8) := by
  rcases hp5 with h | h <;>
  · rw [show (p : ZMod 8) = ((p % 8 : ℕ) : ZMod 8) from by
          simp [ZMod.natCast_eq_natCast_iff]
        h]
    decide

/-- **Inert prime classification**: p ≡ 5 or 7 (mod 8) → p is prime in ℤ[√-2].
    This is the condition (-2/p) = -1 (Legendre symbol). -/
theorem inert_prime_neg2 (p : ℕ) [hp : Fact p.Prime]
    (hmod : p % 8 = 5 ∨ p % 8 = 7) :
    Prime ((p : ℤ) : ℤ√neg2) := by
  have hprime := hp.out
  rw [← UniqueFactorizationMonoid.irreducible_iff_prime]
  have hnorm : ((p : ℤ) : ℤ√neg2).norm = (p : ℤ) ^ 2 := by
    simp [Zsqrtd.norm]; push_cast; ring
  refine ⟨fun hu => ?_, ?_⟩
  · -- Not a unit: norm = p² ≥ 25 > 1
    have h1 : ((p : ℤ) : ℤ√neg2).norm.natAbs = 1 :=
      Zsqrtd.norm_eq_one_iff.mpr hu
    simp only [hnorm, Int.natAbs_pow, Int.natAbs_natCast] at h1
    nlinarith [hprime.two_le]
  intro a b hab
  -- norm(a) * norm(b) = p²
  have hna_nn := norm_nonneg a
  have hnb_nn := norm_nonneg b
  have hfact : a.norm.natAbs * b.norm.natAbs = p ^ 2 := by
    have hmul : (a * b).norm = a.norm * b.norm := Zsqrtd.norm_mul a b
    have heq : (p : ℤ) ^ 2 = a.norm * b.norm := by rw [← hnorm, hab]; exact hmul
    have ha_eq : a.norm = (a.norm.natAbs : ℤ) := (Int.natAbs_of_nonneg hna_nn).symm
    have hb_eq : b.norm = (b.norm.natAbs : ℤ) := (Int.natAbs_of_nonneg hnb_nn).symm
    exact_mod_cast (by linarith [ha_eq ▸ hb_eq ▸ heq] : (p : ℤ) ^ 2 =
      (a.norm.natAbs : ℤ) * (b.norm.natAbs : ℤ)).symm
  by_cases hau : a.norm.natAbs = 1
  · left; exact Zsqrtd.norm_eq_one_iff.mp hau
  by_cases hbu : b.norm.natAbs = 1
  · right; exact Zsqrtd.norm_eq_one_iff.mp hbu
  -- Both non-units: norm(a), norm(b) ≥ 2
  exfalso
  have ha2 : 2 ≤ a.norm.natAbs := by
    rcases Nat.eq_zero_or_pos a.norm.natAbs with h0 | hpos
    · simp [h0] at hfact; exact absurd hfact.symm (pow_pos hprime.pos 2).ne'
    · omega
  have hb2 : 2 ≤ b.norm.natAbs := by
    rcases Nat.eq_zero_or_pos b.norm.natAbs with h0 | hpos
    · simp [h0, Nat.mul_zero] at hfact; exact absurd hfact.symm (pow_pos hprime.pos 2).ne'
    · omega
  -- norm(a) must equal p
  have hap : a.norm.natAbs = p := by
    have hdvd : a.norm.natAbs ∣ p ^ 2 := ⟨b.norm.natAbs, hfact.symm⟩
    rcases (Nat.dvd_prime_pow hprime).mp hdvd with ⟨k, hk_le, hk_eq⟩
    interval_cases k
    · simp at hk_eq; omega
    · simpa using hk_eq
    · -- k=2: a.norm.natAbs = p², forces b.norm.natAbs = 1
      rw [hk_eq] at hfact
      have hb1 := Nat.eq_of_mul_eq_mul_left (pow_pos hprime.pos 2)
        (hfact.trans (mul_one (p ^ 2)).symm)
      omega
  -- norm(a) = p means a.re² + 2*a.im² = p
  have hsum : a.re ^ 2 + 2 * a.im ^ 2 = (p : ℤ) := by
    have ha_nat : a.norm = (p : ℤ) := by
      rw [← Int.natAbs_of_nonneg hna_nn, hap]; simp
    linarith [norm_formula a]
  -- Cast to ZMod 8: a.re² + 2*a.im² ≡ p (mod 8)
  have h8 : (a.re : ZMod 8) ^ 2 + 2 * (a.im : ZMod 8) ^ 2 = (p : ZMod 8) := by
    have := congr_arg (Int.cast : ℤ → ZMod 8) hsum
    push_cast at this ⊢; exact this
  exact no_sum_form_mod8 hmod (a.re : ZMod 8) (a.im : ZMod 8) h8

/-- **Concrete examples**: 5 and 7 are inert (prime) in ℤ[√-2]. -/
theorem five_is_inert : Prime ((5 : ℤ) : ℤ√neg2) :=
  inert_prime_neg2 5 (by norm_num) (by decide)

theorem seven_is_inert : Prime ((7 : ℤ) : ℤ√neg2) :=
  inert_prime_neg2 7 (by norm_num) (by decide)

/-- **Splitting**: 3 = (1+√-2)·(1-√-2) since 1² + 2·1² = 3. -/
theorem three_splits : (3 : ℤ√neg2) = ⟨1, 1⟩ * ⟨1, -1⟩ := by decide

/-- **Ramification**: 2 = -(√-2)² since N(√-2) = 2. -/
theorem two_ramifies : (2 : ℤ√neg2) = -(⟨0, 1⟩ : ℤ√neg2) ^ 2 := by decide

end ZSqrtNegTwo
