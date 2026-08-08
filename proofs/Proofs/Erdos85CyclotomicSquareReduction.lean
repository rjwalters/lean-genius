import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.Data.ZMod.QuotientRing

/-!
# Reduction of the frequency scalar at the ramified cyclotomic prime

For a prime `p`, reduction modulo `(ζ - 1)` identifies the ring of integers
of a `p`-th cyclotomic field with `ZMod p`.  Consequently, a square
`d - 1 - ζ - ζ⁻¹` specializes to the square `d - 3` modulo `p`.
-/

namespace Erdos85

open Polynomial NumberField

noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {p d : ℕ} [hpFact : Fact p.Prime]
variable [IsCyclotomicExtension {p} ℚ K]

/-- The quotient of the cyclotomic integers by `(ζ-1)` has cardinality `p`.
This is the ramified residue field used to specialize the frequency scalar. -/
theorem card_ringOfIntegers_quotient_span_zeta_sub_one
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) :
    Nat.card (𝓞 K ⧸ Ideal.span {hζ.toInteger - 1}) = p := by
  letI : NumberField K := IsCyclotomicExtension.numberField {p} ℚ K
  rw [hζ.card_quotient_toInteger_sub_one,
    hζ.norm_toInteger_sub_one_of_prime_ne_two']
  · simp
  · exact hp2

/-- **Cyclotomic square specialization.** If the frequency scalar is a
square in a `p`-th cyclotomic field, then `d-3` is a square modulo `p`.

The square root is automatically integral because its square is integral;
it can therefore be reduced modulo `(ζ-1)`. -/
theorem isSquare_zmod_of_isSquare_cyclotomic_frequencyScalar
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) (hd : 3 ≤ d)
    (hsq : IsSquare ((d : K) - 1 - (ζ + ζ⁻¹))) :
    IsSquare ((d - 3 : ℕ) : ZMod p) := by
  rcases hsq with ⟨y, hy⟩
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hpFact.out.ne_zero
  have hζint : IsIntegral ℤ ζ := hζ.isIntegral hpFact.out.pos
  have hζinvpow : ζ ^ (p - 1) = ζ⁻¹ := by
    apply (mul_eq_one_iff_eq_inv₀ hζ0).mp
    rw [← pow_succ, Nat.sub_add_cancel hpFact.out.one_le, hζ.pow_eq_one]
  have hζinvint : IsIntegral ℤ ζ⁻¹ := by
    rw [← hζinvpow]
    exact hζint.pow _
  have hxint : IsIntegral ℤ ((d : K) - 1 - (ζ + ζ⁻¹)) := by
    exact (((isIntegral_natCast d).sub isIntegral_one).sub
      (hζint.add hζinvint))
  have hyint : IsIntegral ℤ y := by
    apply IsIntegral.of_pow (n := 2) (by omega)
    rw [show y ^ 2 = y * y by ring, ← hy]
    exact hxint
  let I : Ideal (𝓞 K) := Ideal.span {hζ.toInteger - 1}
  let R := (𝓞 K) ⧸ I
  letI : Finite R := hζ.finite_quotient_span_sub_one'
  letI : Fintype R := Fintype.ofFinite R
  have hcard : Fintype.card R = p := by
    rw [← Nat.card_eq_fintype_card]
    exact card_ringOfIntegers_quotient_span_zeta_sub_one hζ hp2
  let e : ZMod p ≃+* R :=
    ZMod.ringEquivOfPrime (R := R) hpFact.out hcard
  let q : 𝓞 K →+* R := Ideal.Quotient.mk I
  let yO : 𝓞 K := ⟨y, hyint⟩
  let ζinvO : 𝓞 K := ⟨ζ⁻¹, hζinvint⟩
  let xO : 𝓞 K := (d : 𝓞 K) - 1 - (hζ.toInteger + ζinvO)
  have hyO : xO = yO * yO := by
    apply RingOfIntegers.ext
    exact hy
  have hζone : q hζ.toInteger = 1 := by
    apply sub_eq_zero.mp
    rw [← map_one q, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton _))
  have hζinvone : q ζinvO = 1 := by
    have hprod : hζ.toInteger * ζinvO = 1 := by
      apply RingOfIntegers.ext
      exact mul_inv_cancel₀ hζ0
    have hmap := congrArg q hprod
    simp only [map_mul, map_one, hζone, one_mul] at hmap
    exact hmap
  have hyq : q yO * q yO = e ((d - 3 : ℕ) : ZMod p) := by
    rw [← map_mul, ← hyO]
    simp only [xO, map_sub, map_add, map_one, hζone,
      hζinvone]
    have hdEq : d = (d - 3) + 3 := by omega
    calc
      (d : R) - 1 - (1 + 1) = ((d - 3 : ℕ) : R) := by
        rw [hdEq]
        push_cast
        ring
      _ = e ((d - 3 : ℕ) : ZMod p) := (map_natCast e _).symm
  refine ⟨e.symm (q yO), ?_⟩
  apply e.injective
  simp [hyq]

/-- A quadratic nonresidue `d-3` modulo `p` forces the frequency scalar
into the nonsquare branch over every `p`-th cyclotomic extension. -/
theorem not_isSquare_cyclotomic_frequencyScalar_of_nonresidue
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) (hd : 3 ≤ d)
    (hnr : ¬IsSquare ((d - 3 : ℕ) : ZMod p)) :
    ¬IsSquare ((d : K) - 1 - (ζ + ζ⁻¹)) := by
  intro hsq
  exact hnr
    (isSquare_zmod_of_isSquare_cyclotomic_frequencyScalar
      hζ hp2 hd hsq)

end

end Erdos85
