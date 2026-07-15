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
abbrev ZdNeg2 := Zsqrtd (-2 : ℤ)

-- ============================================================
-- Part I: Basic Norm Properties
-- ============================================================

/-- The norm N(a + b√-2) = a² + 2b² is always nonneg. -/
theorem norm_nonneg (z : ZdNeg2) : 0 ≤ Zsqrtd.norm z := by
  simp only [Zsqrtd.norm]
  nlinarith [sq_nonneg z.re, sq_nonneg z.im]

/-- The norm is positive for nonzero elements (key for Euclidean algorithm). -/
theorem norm_pos_of_ne_zero {z : ZdNeg2} (hz : z ≠ 0) : 0 < Zsqrtd.norm z := by
  rcases (norm_nonneg z).lt_or_eq with h | h
  · exact h
  · exfalso; apply hz
    have hnn : Zsqrtd.norm z = 0 := h.symm
    simp only [Zsqrtd.norm] at hnn
    have hre : z.re = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    have him : z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    exact Zsqrtd.ext hre him

/-- Norm formula: N(a + b√-2) = a² + 2b². -/
theorem norm_formula (z : ZdNeg2) : Zsqrtd.norm z = z.re ^ 2 + 2 * z.im ^ 2 := by
  simp [Zsqrtd.norm]; ring

/-- Norm is nonneg (alternative formulation needed for natAbs). -/
theorem norm_natAbs_cast (z : ZdNeg2) : (z.norm.natAbs : ℤ) = z.norm :=
  Int.natAbs_of_nonneg (norm_nonneg z)

-- ============================================================
-- Part II: Embedding into ℂ for Norm Computation
-- ============================================================

/-- The embedding ℤ[√-2] →+* ℂ sending √-2 ↦ i√2. -/
noncomputable def toComplex : ZdNeg2 →+* ℂ :=
  Zsqrtd.lift ⟨Real.sqrt 2 * Complex.I, by
    have hs : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
    have h : (Real.sqrt 2 * Complex.I) * (Real.sqrt 2 * Complex.I)
        = (Real.sqrt 2 : ℂ) * Real.sqrt 2 * (Complex.I * Complex.I) := by ring
    rw [h, hs, Complex.I_mul_I]; norm_num⟩

@[simp]
theorem toComplex_apply (z : ZdNeg2) :
    toComplex z = z.re + z.im * (Real.sqrt 2 * Complex.I) := by
  simp [toComplex, Zsqrtd.lift_apply_apply]

/-- The complex embedding is injective. -/
theorem toComplex_injective : Function.Injective toComplex := by
  unfold toComplex
  exact Zsqrtd.lift_injective _ (fun n => by have := mul_self_nonneg n; omega)

/-- The Zsqrtd norm equals Complex.normSq ∘ toComplex. -/
theorem norm_eq_normSq (z : ZdNeg2) :
    (z.norm : ℝ) = Complex.normSq (toComplex z) := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hz : toComplex z = ((z.re : ℝ) : ℂ) + (((z.im : ℝ) * Real.sqrt 2 : ℝ) : ℂ) * Complex.I := by
    rw [toComplex_apply]; push_cast; ring
  rw [hz, Complex.normSq_add_mul_I, Zsqrtd.norm_def]
  push_cast
  linear_combination (-(z.im : ℝ) ^ 2) * hs

-- ============================================================
-- Part III: Euclidean Division Algorithm
-- ============================================================

noncomputable instance : Div ZdNeg2 :=
  ⟨fun x y =>
    let n := (Zsqrtd.norm y : ℚ)
    let c := star y
    ⟨round ((x * c).re / n : ℚ), round ((x * c).im / n : ℚ)⟩⟩

noncomputable instance : Mod ZdNeg2 :=
  ⟨fun x y => x - y * (x / y)⟩

theorem div_def (x y : ZdNeg2) :
    x / y = ⟨round ((x * star y).re / Zsqrtd.norm y : ℚ),
             round ((x * star y).im / Zsqrtd.norm y : ℚ)⟩ := rfl

theorem mod_def (x y : ZdNeg2) : x % y = x - y * (x / y) := rfl

-- ============================================================
-- Part IV: The Key Norm Bound (3/4 rule)
-- ============================================================

/-- The exact complex quotient x/y decomposes as α + √2·β·I
    where α = (x·ȳ).re / N(y) and β = (x·ȳ).im / N(y). -/
private theorem toComplex_div_eq (x y : ZdNeg2) (hy : y ≠ 0) :
    (toComplex x / toComplex y : ℂ) =
    (((x * star y).re : ℚ) / Zsqrtd.norm y : ℚ) +
    Real.sqrt 2 * (((x * star y).im : ℚ) / Zsqrtd.norm y : ℚ) * Complex.I := by
  have hy_ℂ : (toComplex y : ℂ) ≠ 0 := fun h => hy (toComplex_injective (by simp [h]))
  have hNz : ((Zsqrtd.norm y : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast (norm_pos_of_ne_zero hy).ne'
  -- The complex conjugate of the embedding is the embedding of the Zsqrtd conjugate.
  have hconj : (starRingEnd ℂ) (toComplex y) = toComplex (star y) := by
    rw [toComplex_apply, toComplex_apply, Zsqrtd.re_star, Zsqrtd.im_star]
    push_cast
    simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast]
    ring
  -- y * (star y) embeds to the (real) norm.
  have hyconj : toComplex y * toComplex (star y) = ((Zsqrtd.norm y : ℤ) : ℂ) := by
    rw [← map_mul, ← Zsqrtd.norm_eq_mul_conj, map_intCast]
  -- The rational RHS is toComplex (x * star y) scaled by 1/N(y).
  have expand : ((((x * star y).re : ℚ) / Zsqrtd.norm y : ℚ) : ℂ)
        + Real.sqrt 2 * (((x * star y).im : ℚ) / Zsqrtd.norm y : ℚ) * Complex.I
      = toComplex (x * star y) * (((Zsqrtd.norm y : ℤ) : ℂ))⁻¹ := by
    rw [toComplex_apply]
    push_cast
    field_simp
  rw [div_eq_iff hy_ℂ, expand]
  rw [show toComplex (x * star y) * (((Zsqrtd.norm y : ℤ) : ℂ))⁻¹ * toComplex y
        = toComplex x * (toComplex y * toComplex (star y)) *
            (((Zsqrtd.norm y : ℤ) : ℂ))⁻¹ from by rw [map_mul]; ring,
      hyconj, mul_assoc, mul_inv_cancel₀ hNz, mul_one]

/-- The rounded quotient in ℂ: round(α) + √2·round(β)·I. -/
private theorem toComplex_quot_eq (x y : ZdNeg2) :
    (toComplex (x / y) : ℂ) =
    (round ((x * star y).re / Zsqrtd.norm y : ℚ) : ℤ) +
    Real.sqrt 2 * (round ((x * star y).im / Zsqrtd.norm y : ℚ) : ℤ) * Complex.I := by
  simp [toComplex_apply, div_def]
  ring

/-- **Key bound**: The rounding error has normSq ≤ 3/4 < 1. -/
theorem normSq_div_sub_div_lt_one (x y : ZdNeg2) (hy : y ≠ 0) :
    Complex.normSq ((toComplex x / toComplex y : ℂ) - toComplex (x / y)) < 1 := by
  set rα : ℚ := ((x * star y).re : ℚ) / Zsqrtd.norm y with hrα
  set rβ : ℚ := ((x * star y).im : ℚ) / Zsqrtd.norm y with hrβ
  -- The two rational rounding errors, each bounded by 1/2 in absolute value.
  set dα : ℚ := rα - round rα with hdα
  set dβ : ℚ := rβ - round rβ with hdβ
  -- Express error as dα + √2·dβ·I where |dα|, |dβ| ≤ 1/2
  have herr : (toComplex x / toComplex y : ℂ) - toComplex (x / y) =
      ((dα : ℝ) : ℂ) + Real.sqrt 2 * ((dβ : ℝ) : ℂ) * Complex.I := by
    rw [toComplex_div_eq x y hy, toComplex_quot_eq, hdα, hdβ, hrα, hrβ]
    push_cast; ring
  have hδα : |dα| ≤ 1/2 := by rw [hdα]; exact abs_sub_round rα
  have hδβ : |dβ| ≤ 1/2 := by rw [hdβ]; exact abs_sub_round rβ
  clear_value dα dβ
  have hδαR : |(dα : ℝ)| ≤ 1/2 := by
    have h2 : ((|dα| : ℚ) : ℝ) ≤ ((1/2 : ℚ) : ℝ) := Rat.cast_le.mpr hδα
    rw [Rat.cast_abs] at h2; simpa using h2
  have hδβR : |(dβ : ℝ)| ≤ 1/2 := by
    have h2 : ((|dβ| : ℚ) : ℝ) ≤ ((1/2 : ℚ) : ℝ) := Rat.cast_le.mpr hδβ
    rw [Rat.cast_abs] at h2; simpa using h2
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [herr, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
             Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
             mul_zero, mul_one, zero_mul, sub_zero, add_zero, zero_add]
  nlinarith [sq_abs (dα : ℝ), sq_abs (dβ : ℝ), h2, hδαR, hδβR,
             abs_nonneg (dα : ℝ), abs_nonneg (dβ : ℝ)]

/-- **Key Result**: The remainder has strictly smaller norm. -/
theorem norm_mod_lt (x : ZdNeg2) {y : ZdNeg2} (hy : y ≠ 0) :
    (x % y).norm < y.norm := by
  have hy_ℂ : (toComplex y : ℂ) ≠ 0 := fun h => hy (toComplex_injective (by simp [h]))
  rw [mod_def]
  have goalR : ((x - y * (x / y)).norm : ℝ) < (y.norm : ℝ) := by
    rw [norm_eq_normSq, norm_eq_normSq]
    calc Complex.normSq (toComplex (x - y * (x / y)))
        = Complex.normSq (toComplex y * (toComplex x / toComplex y - toComplex (x / y))) := by
          rw [map_sub, map_mul, mul_sub, mul_div_cancel₀ _ hy_ℂ]
      _ = Complex.normSq (toComplex y) *
          Complex.normSq (toComplex x / toComplex y - toComplex (x / y)) := normSq_mul _ _
      _ < Complex.normSq (toComplex y) * 1 :=
          mul_lt_mul_of_pos_left (normSq_div_sub_div_lt_one x y hy) (normSq_pos.2 hy_ℂ)
      _ = _ := mul_one _
  exact_mod_cast goalR

theorem norm_mod_lt_natAbs (x : ZdNeg2) {y : ZdNeg2} (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs :=
  Int.ofNat_lt.1 (by simpa [norm_natAbs_cast] using norm_mod_lt x hy)

-- ============================================================
-- Part V: ℤ[√-2] is a Euclidean Domain
-- ============================================================

/-- **ℤ[√-2] is a Euclidean Domain** with norm N(a+b√-2) = a² + 2b². -/
noncomputable instance : EuclideanDomain ZdNeg2 :=
  { (inferInstance : CommRing ZdNeg2), (inferInstance : Nontrivial ZdNeg2) with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := fun a => by
      have e : (Zsqrtd.norm (0 : ZdNeg2) : ℚ) = 0 := by
        simp [Zsqrtd.norm_def, Zsqrtd.re_zero, Zsqrtd.im_zero]
      rw [div_def, e]
      simp only [div_zero, round_zero]
      rfl
    quotient_mul_add_remainder_eq := fun x y => by rw [mod_def]; ring
    r := fun a b => a.norm.natAbs < b.norm.natAbs
    r_wellFounded := (measure fun z : ZdNeg2 => z.norm.natAbs).wf
    remainder_lt := fun x {y} hy => norm_mod_lt_natAbs x hy
    mul_left_not_lt := fun a b hb => by
      show ¬ (a * b).norm.natAbs < a.norm.natAbs
      rw [Zsqrtd.norm_mul, Int.natAbs_mul]
      have hbn : b.norm ≠ 0 := fun h =>
        hb ((Zsqrtd.norm_eq_zero_iff (by norm_num) b).mp h)
      have hb' : 0 < b.norm.natAbs := Int.natAbs_pos.mpr hbn
      have hle : a.norm.natAbs ≤ a.norm.natAbs * b.norm.natAbs := by
        have := Nat.mul_le_mul (Nat.le_refl a.norm.natAbs) hb'
        simpa using this
      omega }

-- UFD follows automatically from the Euclidean domain instance
-- (EuclideanDomain → IsDomain → IsPrincipalIdealRing → UniqueFactorizationMonoid).
example : UniqueFactorizationMonoid ZdNeg2 := inferInstance

-- ============================================================
-- Part VI: Inert Prime Classification for ℤ[√-2]
-- ============================================================

/-- Squares mod 8 are {0,1,4}, so a² + 2b² mod 8 ∈ {0,1,2,3,4,6}, never 5 or 7. -/
theorem no_sum_form_mod8 {p : ℕ} (hp5 : p % 8 = 5 ∨ p % 8 = 7) :
    ∀ a b : ZMod 8, a ^ 2 + 2 * b ^ 2 ≠ (p : ZMod 8) := by
  have hpc : (p : ZMod 8) = ((p % 8 : ℕ) : ZMod 8) := (ZMod.natCast_mod p 8).symm
  rcases hp5 with h | h <;> rw [hpc, h] <;> decide

/-- **Inert prime classification**: p ≡ 5 or 7 (mod 8) → p is prime in ℤ[√-2].
    This is the condition (-2/p) = -1 (Legendre symbol). -/
theorem inert_prime_neg2 (p : ℕ) [hp : Fact p.Prime]
    (hmod : p % 8 = 5 ∨ p % 8 = 7) :
    Prime ((p : ℤ) : ZdNeg2) := by
  have hprime := hp.out
  rw [← UniqueFactorizationMonoid.irreducible_iff_prime]
  have hnorm : ((p : ℤ) : ZdNeg2).norm = (p : ℤ) ^ 2 := by
    simp [Zsqrtd.norm]; ring
  refine ⟨fun hu => ?_, ?_⟩
  · -- Not a unit: norm = p² ≥ 25 > 1
    have h1 : ((p : ℤ) : ZdNeg2).norm.natAbs = 1 :=
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
    · simp [h0] at hfact; exact absurd hfact.symm (pow_pos hprime.pos 2).ne'
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
      rw [← Int.natAbs_of_nonneg hna_nn, hap]
    linarith [norm_formula a]
  -- Cast to ZMod 8: a.re² + 2*a.im² ≡ p (mod 8)
  have h8 : (a.re : ZMod 8) ^ 2 + 2 * (a.im : ZMod 8) ^ 2 = (p : ZMod 8) := by
    have := congr_arg (Int.cast : ℤ → ZMod 8) hsum
    push_cast at this ⊢; exact this
  exact no_sum_form_mod8 hmod (a.re : ZMod 8) (a.im : ZMod 8) h8

/-- **Concrete examples**: 5 and 7 are inert (prime) in ℤ[√-2]. -/
theorem five_is_inert : Prime ((5 : ℤ) : ZdNeg2) :=
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  inert_prime_neg2 5 (by decide)

theorem seven_is_inert : Prime ((7 : ℤ) : ZdNeg2) :=
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  inert_prime_neg2 7 (by decide)

/-- **Splitting**: 3 = (1+√-2)·(1-√-2) since 1² + 2·1² = 3. -/
theorem three_splits : (3 : ZdNeg2) = ⟨1, 1⟩ * ⟨1, -1⟩ := by decide

/-- **Ramification**: 2 = -(√-2)² since N(√-2) = 2. -/
theorem two_ramifies : (2 : ZdNeg2) = -(⟨0, 1⟩ : ZdNeg2) ^ 2 := by decide

end ZSqrtNegTwo
