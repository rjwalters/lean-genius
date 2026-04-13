import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.Tactic

/-
# Gaussian Integers as a Euclidean Domain (bezout-identity-oq-02-oq-01-oq-02-oq-02)

## Open Question

Is there a gallery proof formalizing unique factorization in ℤ[i], including
the characterization of Gaussian primes?

## Answer: YES — via Mathlib's GaussianInt and three-way prime classification

### Main Results

1. ℤ[i] is a Euclidean domain with Euclidean function = norm(z) = z.re² + z.im²
2. ℤ[i] is a UFD via the instance chain EuclideanDomain → GCDMonoid → UFD
3. Gaussian prime classification (backward direction):
   - Norm-2 primes: norm(z) = 2 (z associates to 1+i)
   - Split primes: norm(z) = p for p ≡ 1 (mod 4) rational prime
   - Inert primes: z = ↑p for p ≡ 3 (mod 4) rational prime

## Builds On
- BezoutIdentityOQ02OQ01OQ02.lean: EuclideanDomain → UFD chain
-/

namespace GaussianIntEuclidean

open GaussianInt Zsqrtd

/-! ## Part 1: ℤ[i] as a Euclidean Domain and UFD -/

example : EuclideanDomain GaussianInt := inferInstance
example : UniqueFactorizationMonoid GaussianInt := inferInstance
example : IsPrincipalIdealRing GaussianInt := inferInstance

/-- In a UFD (like ℤ[i]), irreducible elements are exactly the prime elements. -/
example (z : GaussianInt) : Irreducible z ↔ Prime z :=
  UniqueFactorizationMonoid.irreducible_iff_prime

/-! ## Part 2: The Norm Function -/

/-- norm(a + bi) = a² + b² -/
theorem gaussian_norm_formula (z : GaussianInt) :
    z.norm = z.re * z.re + z.im * z.im := by
  unfold Zsqrtd.norm; ring

theorem norm_mul_eq (z w : GaussianInt) : (z * w).norm = z.norm * w.norm :=
  Zsqrtd.norm_mul z w

/-- z is a unit iff norm(z) = 1 -/
theorem is_unit_iff_norm_one (z : GaussianInt) : IsUnit z ↔ z.norm.natAbs = 1 :=
  Zsqrtd.norm_eq_one_iff.symm

/-- norm(star z) = norm(z) (conjugate preserves norm) -/
theorem norm_conj_eq (z : GaussianInt) : (star z).norm = z.norm := by
  simp only [Zsqrtd.norm, star, Zsqrtd.star_mk]; ring

/-! ## Part 3: Gaussian Prime Classification — Backward Direction -/

/-- An element with prime norm is prime in ℤ[i].
    Covers norm-2 primes (1+i) and split primes (2+i, 3+2i, ...). -/
theorem prime_of_prime_natAbs_norm {z : GaussianInt}
    (h : z.norm.natAbs.Prime) : Prime z := by
  rw [← UniqueFactorizationMonoid.irreducible_iff_prime]
  refine ⟨mt (Zsqrtd.norm_eq_one_iff.mpr ·) h.ne_one, ?_⟩
  intro a b hab
  have hmul : a.norm.natAbs * b.norm.natAbs = z.norm.natAbs := by
    rw [hab, Zsqrtd.norm_mul, Int.natAbs_mul]
  rcases h.eq_one_or_self_of_dvd a.norm.natAbs ⟨b.norm.natAbs, hmul.symm⟩ with ha | ha
  · left; exact Zsqrtd.norm_eq_one_iff.mp ha
  · right; apply Zsqrtd.norm_eq_one_iff.mp
    have hpos := h.pos
    -- ha : a.norm.natAbs = z.norm.natAbs, hmul : a.norm.natAbs * b.norm.natAbs = z.norm.natAbs
    -- so a.norm.natAbs * b.norm.natAbs = a.norm.natAbs * 1
    exact Nat.eq_of_mul_eq_mul_left (ha.symm ▸ hpos)
      (by rw [mul_one]; exact hmul.trans ha.symm)

/-- A rational prime p ≡ 3 (mod 4) is prime in ℤ[i] (inert prime).
    Proof: p ≡ 3 mod 4 cannot be a sum of two integer squares
    (since squares are ≡ 0 or 1 mod 4, their sum is ≡ 0, 1, or 2, never 3).
    So if ↑p = a*b, then norm(a) ≠ p, forcing norm(a) = 1 or norm(a) = p². -/
theorem inert_prime {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 3) :
    Prime ((↑p : GaussianInt)) := by
  rw [← UniqueFactorizationMonoid.irreducible_iff_prime]
  have hnorm : (↑p : GaussianInt).norm = (p : ℤ) ^ 2 := by
    simp [Zsqrtd.norm]; push_cast; ring
  refine ⟨fun hu => ?_, ?_⟩
  · -- Not a unit: norm = p² ≥ 4 > 1
    have h1 := Zsqrtd.norm_eq_one_iff.mpr hu
    simp only [hnorm, Int.natAbs_pow, Int.natAbs_natCast] at h1
    nlinarith [hp.two_le]
  intro a b hab
  -- norm(a) * norm(b) = p²
  have hna_nn := GaussianInt.norm_nonneg a
  have hnb_nn := GaussianInt.norm_nonneg b
  have hfact : a.norm.natAbs * b.norm.natAbs = p ^ 2 := by
    have hmul : (a * b).norm = a.norm * b.norm := Zsqrtd.norm_mul a b
    have heq : (p : ℤ) ^ 2 = a.norm * b.norm := by
      rw [← hnorm, hab]; exact hmul
    have ha_eq : a.norm = (a.norm.natAbs : ℤ) := (Int.natAbs_of_nonneg hna_nn).symm
    have hb_eq : b.norm = (b.norm.natAbs : ℤ) := (Int.natAbs_of_nonneg hnb_nn).symm
    have : (p : ℤ) ^ 2 = (a.norm.natAbs : ℤ) * (b.norm.natAbs : ℤ) := by
      rw [← ha_eq, ← hb_eq]; exact heq
    exact_mod_cast this.symm
  by_cases hau : a.norm.natAbs = 1
  · left; exact Zsqrtd.norm_eq_one_iff.mp hau
  by_cases hbu : b.norm.natAbs = 1
  · right; exact Zsqrtd.norm_eq_one_iff.mp hbu
  -- Both non-units: norm(a) ≥ 2, norm(b) ≥ 2, product = p²
  -- The only possibility for p prime: norm(a) = p and norm(b) = p
  exfalso
  have ha2 : 2 ≤ a.norm.natAbs := by
    rcases Nat.eq_zero_or_pos a.norm.natAbs with h0 | hpos
    · simp only [h0, zero_mul] at hfact
      exact absurd hfact.symm (pow_pos hp.pos 2).ne'
    · omega
  have hb2 : 2 ≤ b.norm.natAbs := by
    rcases Nat.eq_zero_or_pos b.norm.natAbs with h0 | hpos
    · simp only [h0, Nat.mul_zero] at hfact
      exact absurd hfact.symm (pow_pos hp.pos 2).ne'
    · omega
  have hap : a.norm.natAbs = p := by
    have hdvd : a.norm.natAbs ∣ p ^ 2 := ⟨b.norm.natAbs, hfact.symm⟩
    -- Divisors of p² are {1, p, p²}
    rcases (Nat.dvd_prime_pow hp).mp hdvd with ⟨k, hk_le, hk_eq⟩
    interval_cases k
    · simp at hk_eq; omega
    · simpa using hk_eq
    · -- k=2: a.norm.natAbs = p², forces b.norm.natAbs = 1, contradicts hb2
      have hfact' := hfact; rw [hk_eq] at hfact'
      -- hfact' : p^2 * b.norm.natAbs = p^2
      have hb1 := Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2)
        (hfact'.trans (mul_one (p ^ 2)).symm)
      omega
  -- norm(a) = p means a.re² + a.im² = p as integers
  have hsum : a.re ^ 2 + a.im ^ 2 = (p : ℤ) := by
    have ha_nat : a.norm = (p : ℤ) := by
      rw [← Int.natAbs_of_nonneg hna_nn, hap]
    have : a.re ^ 2 + a.im ^ 2 = a.norm := by
      rw [gaussian_norm_formula a]; ring
    linarith
  -- p ≡ 3 (mod 4) cannot be a sum of two squares (squares mod 4 are 0 or 1)
  have h4 : (a.re : ZMod 4) ^ 2 + (a.im : ZMod 4) ^ 2 = (p : ZMod 4) := by
    have := congr_arg (Int.cast : ℤ → ZMod 4) hsum; push_cast at this ⊢; exact this
  have hp4 : (p : ZMod 4) = 3 := by
    rw [show (3 : ZMod 4) = ((3 : ℕ) : ZMod 4) from by norm_num,
        ZMod.natCast_eq_natCast_iff]
    unfold Nat.ModEq
    omega
  rw [hp4] at h4
  exact (by decide : ∀ x y : ZMod 4, x ^ 2 + y ^ 2 ≠ 3) (a.re : ZMod 4) (a.im : ZMod 4) h4

/-! ## Part 4: Concrete Examples -/

/-- 1+i is prime in ℤ[i] (norm = 2, the ramified prime above 2). -/
theorem one_add_I_prime : Prime (⟨1, 1⟩ : GaussianInt) :=
  prime_of_prime_natAbs_norm (by native_decide)

/-- 2+i is prime in ℤ[i] (norm = 5 ≡ 1 mod 4). -/
theorem two_add_I_prime : Prime (⟨2, 1⟩ : GaussianInt) :=
  prime_of_prime_natAbs_norm (by native_decide)

/-- 2+3i is prime in ℤ[i] (norm = 13 ≡ 1 mod 4). -/
theorem two_add_3I_prime : Prime (⟨2, 3⟩ : GaussianInt) :=
  prime_of_prime_natAbs_norm (by native_decide)

/-- 3 is prime in ℤ[i] (3 ≡ 3 mod 4, inert). -/
theorem three_is_inert_prime : Prime ((3 : ℕ) : GaussianInt) :=
  inert_prime (by decide) (by decide)

/-- 7 is prime in ℤ[i] (7 ≡ 3 mod 4, inert). -/
theorem seven_is_inert_prime : Prime ((7 : ℕ) : GaussianInt) :=
  inert_prime (by decide) (by decide)

/-- 2 ramifies in ℤ[i]: 2 = -i · (1+i)² -/
theorem two_ramifies : (2 : GaussianInt) = -(⟨0, 1⟩ : GaussianInt) * ⟨1, 1⟩ ^ 2 := by
  decide

/-- 5 splits in ℤ[i]: 5 = (2+i) · (2-i) -/
theorem five_splits : (5 : GaussianInt) = ⟨2, 1⟩ * ⟨2, -1⟩ := by
  decide

/-- 13 splits in ℤ[i]: 13 = (2+3i) · (2-3i) -/
theorem thirteen_splits : (13 : GaussianInt) = ⟨2, 3⟩ * ⟨2, -3⟩ := by
  decide

#check @UniqueFactorizationMonoid.irreducible_iff_prime
#check @Zsqrtd.norm_eq_one_iff
#check @GaussianInt.norm_nonneg

end GaussianIntEuclidean
