import Proofs.Erdos85PrimeFourierSquare
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

/-!
# Primitive order-nine Fourier divisibility

Vanishing of an integral Fourier coefficient at a primitive ninth root
forces its total mass to be divisible by three.  The proof evaluates the
cyclotomic divisibility at one: `Φ9(1)=3`.
-/

namespace Erdos85

open scoped BigOperators
open Polynomial

noncomputable section

set_option maxHeartbeats 800000 in
/-- If an integral coefficient vector of length nine vanishes at a
primitive ninth root, then three divides the sum of its coefficients. -/
theorem three_dvd_sum_of_orderNine_fourier_eq_zero
    {K : Type*} [Field K] [CharZero K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 9)
    (a : Fin 9 → ℤ)
    (hzero : ∑ i : Fin 9, (a i : K) * ζ ^ i.val = 0) :
    (3 : ℤ) ∣ ∑ i, a i := by
  let P : ℤ[X] := ∑ i : Fin 9, C (a i) * X ^ i.val
  have hPzero : aeval ζ P = 0 := by
    simpa [P, map_sum, map_mul, map_pow] using hzero
  have hdvd : cyclotomic 9 ℤ ∣ P := by
    rw [cyclotomic_eq_minpoly hζ (by norm_num : 0 < 9)]
    exact minpoly.isIntegrallyClosed_dvd
      (hζ.isIntegral (by norm_num : 0 < 9)) hPzero
  obtain ⟨Q, hQ⟩ := hdvd
  refine ⟨Q.eval 1, ?_⟩
  have hPeval : P.eval 1 = ∑ i, a i := by
    dsimp only [P]
    rw [eval_finsetSum]
    simp
  have hcyclo : (cyclotomic 9 ℤ).eval 1 = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    simpa using
      (eval_one_cyclotomic_prime_pow (R := ℤ) (p := 3) 1)
  rw [← hPeval, hQ, eval_mul, hcyclo]

theorem aeval_cyclotomic_nine_at_primitive_three
    {K : Type*} [Field K] [CharZero K]
    {η : K} (hη : IsPrimitiveRoot η 3) :
    aeval η (cyclotomic 9 ℤ) = 3 := by
  rw [show 9 = 3 ^ (1 + 1) by norm_num]
  rw [cyclotomic_prime_pow_eq_geom_sum (R := ℤ) Nat.prime_three]
  simp [map_sum, map_pow, hη.pow_eq_one]

set_option maxHeartbeats 1000000 in
/-- Simultaneous vanishing at primitive ninth and third roots forces nine
to divide the total coefficient mass.  Algebraically, `Φ9` first divides
the coefficient polynomial; evaluating its quotient at the third root
shows that `Φ3` divides the quotient as well.  Finally
`Φ9(1) * Φ3(1) = 3 * 3`. -/
theorem nine_dvd_sum_of_orderNine_and_orderThree_fourier_eq_zero
    {K : Type*} [Field K] [CharZero K]
    {ζ η : K} (hζ : IsPrimitiveRoot ζ 9)
    (hη : IsPrimitiveRoot η 3)
    (a : Fin 9 → ℤ)
    (hzero9 : ∑ i : Fin 9, (a i : K) * ζ ^ i.val = 0)
    (hzero3 : ∑ i : Fin 9, (a i : K) * η ^ i.val = 0) :
    (9 : ℤ) ∣ ∑ i, a i := by
  let P : ℤ[X] := ∑ i : Fin 9, C (a i) * X ^ i.val
  have hPzero9 : aeval ζ P = 0 := by
    simpa [P, map_sum, map_mul, map_pow] using hzero9
  have hPzero3 : aeval η P = 0 := by
    simpa [P, map_sum, map_mul, map_pow] using hzero3
  have hdvd9 : cyclotomic 9 ℤ ∣ P := by
    rw [cyclotomic_eq_minpoly hζ (by norm_num : 0 < 9)]
    exact minpoly.isIntegrallyClosed_dvd
      (hζ.isIntegral (by norm_num : 0 < 9)) hPzero9
  obtain ⟨Q, hQ⟩ := hdvd9
  have hQzero3 : aeval η Q = 0 := by
    rw [hQ, map_mul,
      aeval_cyclotomic_nine_at_primitive_three hη] at hPzero3
    exact (mul_eq_zero.mp hPzero3).resolve_left (by norm_num)
  have hdvd3 : cyclotomic 3 ℤ ∣ Q := by
    rw [cyclotomic_eq_minpoly hη (by norm_num : 0 < 3)]
    exact minpoly.isIntegrallyClosed_dvd
      (hη.isIntegral (by norm_num : 0 < 3)) hQzero3
  obtain ⟨R, hR⟩ := hdvd3
  refine ⟨R.eval 1, ?_⟩
  have hPeval : P.eval 1 = ∑ i, a i := by
    dsimp only [P]
    rw [eval_finsetSum]
    simp
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyclo9 : (cyclotomic 9 ℤ).eval 1 = 3 := by
    simpa using
      (eval_one_cyclotomic_prime_pow (R := ℤ) (p := 3) 1)
  have hcyclo3 : (cyclotomic 3 ℤ).eval 1 = 3 := by
    simpa using (eval_one_cyclotomic_prime (R := ℤ) (p := 3))
  rw [← hPeval, hQ, hR, eval_mul, eval_mul, hcyclo9, hcyclo3]
  ring

/-- Abstract terminal for the ninth-root/third-root trace dichotomy.  The
ninth-root trace always vanishes, giving `3 ∣ d`.  If `d` is a square this
already gives `9 ∣ d`; otherwise the third-root trace vanishes as well and
the product `Φ9Φ3` gives `9 ∣ d`.  The boundary order is `3 mod 9`, a
contradiction. -/
theorem false_of_orderNine_fourier_dichotomy_and_boundary
    {K : Type*} [Field K] [CharZero K]
    {ζ η : K} (hζ : IsPrimitiveRoot ζ 9)
    (hη : IsPrimitiveRoot η 3)
    (a : Fin 9 → ℤ) {d : ℕ}
    (hsum : ∑ i, a i = (d : ℤ))
    (hboundary : 9 ∣ d * (d - 1) + 3)
    (hzero9 : ∑ i : Fin 9, (a i : K) * ζ ^ i.val = 0)
    (hzero3 : ¬ IsSquare d →
      ∑ i : Fin 9, (a i : K) * η ^ i.val = 0) : False := by
  have hthreeInt : (3 : ℤ) ∣ (d : ℤ) := by
    rw [← hsum]
    exact three_dvd_sum_of_orderNine_fourier_eq_zero hζ a hzero9
  have hthree : 3 ∣ d := by
    exact_mod_cast hthreeInt
  have hnine : 9 ∣ d := by
    by_cases hsquare : IsSquare d
    · exact nine_dvd_of_three_dvd_of_isSquare hthree hsquare
    · have hnineInt : (9 : ℤ) ∣ (d : ℤ) := by
        rw [← hsum]
        exact nine_dvd_sum_of_orderNine_and_orderThree_fourier_eq_zero
          hζ hη a hzero9 (hzero3 hsquare)
      exact_mod_cast hnineInt
  exact nine_not_dvd_boundary_of_nine_dvd_degree hnine hboundary

end

end Erdos85
