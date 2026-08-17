import Mathlib

/-! # Irreducibility certificates for the H16 cycle defect factors -/

open Polynomial

namespace Erdos85

noncomputable section

def cycleDefectQuadraticFive : ℤ[X] := X ^ 2 - 11 * X + 29
def cycleDefectQuadraticSixteen : ℤ[X] := X ^ 2 - 10 * X + 23
def cycleDefectCubicSeven : ℤ[X] := X ^ 3 - 16 * X ^ 2 + 83 * X - 139
def cycleDefectCubicNine : ℤ[X] := X ^ 3 - 15 * X ^ 2 + 72 * X - 111
def cycleDefectQuinticEleven : ℤ[X] :=
  X ^ 5 - 26 * X ^ 4 + 266 * X ^ 3 - 1337 * X ^ 2 + 3298 * X - 3191
def cycleDefectSexticThirteen : ℤ[X] :=
  X ^ 6 - 31 * X ^ 5 + 395 * X ^ 4 - 2646 * X ^ 3
    + 9821 * X ^ 2 - 19138 * X + 15289

theorem cycleDefectQuadraticFive_natDegree :
    cycleDefectQuadraticFive.natDegree = 2 := by
  unfold cycleDefectQuadraticFive
  compute_degree!

theorem cycleDefectQuadraticSixteen_natDegree :
    cycleDefectQuadraticSixteen.natDegree = 2 := by
  unfold cycleDefectQuadraticSixteen
  compute_degree!

theorem cycleDefectCubicSeven_natDegree :
    cycleDefectCubicSeven.natDegree = 3 := by
  unfold cycleDefectCubicSeven
  compute_degree!

theorem cycleDefectQuinticEleven_natDegree :
    cycleDefectQuinticEleven.natDegree = 5 := by
  unfold cycleDefectQuinticEleven
  compute_degree!

theorem cycleDefectSexticThirteen_natDegree :
    cycleDefectSexticThirteen.natDegree = 6 := by
  unfold cycleDefectSexticThirteen
  compute_degree!

theorem cycleDefectQuadraticFive_monic : cycleDefectQuadraticFive.Monic := by
  unfold cycleDefectQuadraticFive
  monicity!

def cycleDefectQuadraticFiveShift : ℤ[X] := X ^ 2 - 15 * X + 55

theorem cycleDefectQuadraticFiveShift_monic :
    cycleDefectQuadraticFiveShift.Monic := by
  unfold cycleDefectQuadraticFiveShift
  monicity!

theorem cycleDefectQuadraticFiveShift_natDegree :
    cycleDefectQuadraticFiveShift.natDegree = 2 := by
  unfold cycleDefectQuadraticFiveShift
  compute_degree!

theorem cycleDefectQuadraticFiveShift_degree :
    cycleDefectQuadraticFiveShift.degree = 2 := by
  rw [degree_eq_natDegree cycleDefectQuadraticFiveShift_monic.ne_zero,
    cycleDefectQuadraticFiveShift_natDegree]
  norm_num

theorem cycleDefectQuadraticFiveShift_irreducible :
    Irreducible cycleDefectQuadraticFiveShift := by
  apply Polynomial.irreducible_of_eisenstein_criterion
    (P := Ideal.span {(5 : ℤ)})
  · rw [Ideal.span_singleton_prime (show (5 : ℤ) ≠ 0 by norm_num)]
    exact Int.prime_iff_natAbs_prime.mpr (by norm_num)
  · rw [show cycleDefectQuadraticFiveShift.leadingCoeff = 1 from
      cycleDefectQuadraticFiveShift_monic, Ideal.mem_span_singleton]
    norm_num
  · intro k hk
    rw [cycleDefectQuadraticFiveShift_degree] at hk
    have hkn : k < 2 := WithBot.coe_lt_coe.mp hk
    simp only [Ideal.mem_span_singleton]
    interval_cases k <;>
      norm_num [cycleDefectQuadraticFiveShift, coeff_sub, coeff_add,
        coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  · rw [cycleDefectQuadraticFiveShift_degree]
    norm_num
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    unfold cycleDefectQuadraticFiveShift
    norm_num
  · exact cycleDefectQuadraticFiveShift_monic.isPrimitive

theorem cycleDefectQuadraticFive_irreducible_int :
    Irreducible cycleDefectQuadraticFive := by
  have heq :
      (algEquivAevalXAddC (-2 : ℤ)) cycleDefectQuadraticFive =
        cycleDefectQuadraticFiveShift := by
    rw [algEquivAevalXAddC_apply, ← comp_eq_aeval]
    simp [cycleDefectQuadraticFive, cycleDefectQuadraticFiveShift]
    ring
  have hirr := cycleDefectQuadraticFiveShift_irreducible
  rw [← heq] at hirr
  exact (MulEquiv.irreducible_iff
    (f := (algEquivAevalXAddC (-2 : ℤ)).toMulEquiv)).mp hirr

theorem cycleDefectQuadraticFive_irreducible_rat :
    Irreducible (cycleDefectQuadraticFive.map (Int.castRingHom ℚ)) := by
  exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      cycleDefectQuadraticFive_monic.isPrimitive).mp
    cycleDefectQuadraticFive_irreducible_int

theorem cycleDefectQuadraticSixteen_monic :
    cycleDefectQuadraticSixteen.Monic := by
  unfold cycleDefectQuadraticSixteen
  monicity!

def cycleDefectQuadraticSixteenShift : ℤ[X] := X ^ 2 - 12 * X + 34

theorem cycleDefectQuadraticSixteenShift_monic :
    cycleDefectQuadraticSixteenShift.Monic := by
  unfold cycleDefectQuadraticSixteenShift
  monicity!

theorem cycleDefectQuadraticSixteenShift_natDegree :
    cycleDefectQuadraticSixteenShift.natDegree = 2 := by
  unfold cycleDefectQuadraticSixteenShift
  compute_degree!

theorem cycleDefectQuadraticSixteenShift_degree :
    cycleDefectQuadraticSixteenShift.degree = 2 := by
  rw [degree_eq_natDegree cycleDefectQuadraticSixteenShift_monic.ne_zero,
    cycleDefectQuadraticSixteenShift_natDegree]
  norm_num

theorem cycleDefectQuadraticSixteenShift_irreducible :
    Irreducible cycleDefectQuadraticSixteenShift := by
  apply Polynomial.irreducible_of_eisenstein_criterion
    (P := Ideal.span {(2 : ℤ)})
  · rw [Ideal.span_singleton_prime (show (2 : ℤ) ≠ 0 by norm_num)]
    exact Int.prime_iff_natAbs_prime.mpr (by norm_num)
  · rw [show cycleDefectQuadraticSixteenShift.leadingCoeff = 1 from
      cycleDefectQuadraticSixteenShift_monic, Ideal.mem_span_singleton]
    norm_num
  · intro k hk
    rw [cycleDefectQuadraticSixteenShift_degree] at hk
    have hkn : k < 2 := WithBot.coe_lt_coe.mp hk
    simp only [Ideal.mem_span_singleton]
    interval_cases k <;>
      norm_num [cycleDefectQuadraticSixteenShift, coeff_sub, coeff_add,
        coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  · rw [cycleDefectQuadraticSixteenShift_degree]
    norm_num
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    unfold cycleDefectQuadraticSixteenShift
    norm_num
  · exact cycleDefectQuadraticSixteenShift_monic.isPrimitive

theorem cycleDefectQuadraticSixteen_irreducible_int :
    Irreducible cycleDefectQuadraticSixteen := by
  have heq :
      (algEquivAevalXAddC (-1 : ℤ)) cycleDefectQuadraticSixteen =
        cycleDefectQuadraticSixteenShift := by
    rw [algEquivAevalXAddC_apply, ← comp_eq_aeval]
    simp [cycleDefectQuadraticSixteen, cycleDefectQuadraticSixteenShift]
    ring
  have hirr := cycleDefectQuadraticSixteenShift_irreducible
  rw [← heq] at hirr
  exact (MulEquiv.irreducible_iff
    (f := (algEquivAevalXAddC (-1 : ℤ)).toMulEquiv)).mp hirr

theorem cycleDefectQuadraticSixteen_irreducible_rat :
    Irreducible (cycleDefectQuadraticSixteen.map (Int.castRingHom ℚ)) := by
  exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      cycleDefectQuadraticSixteen_monic.isPrimitive).mp
    cycleDefectQuadraticSixteen_irreducible_int

theorem cycleDefectCubicNine_monic : cycleDefectCubicNine.Monic := by
  unfold cycleDefectCubicNine
  monicity!

theorem cycleDefectCubicNine_natDegree : cycleDefectCubicNine.natDegree = 3 := by
  unfold cycleDefectCubicNine
  compute_degree!

theorem cycleDefectCubicNine_degree : cycleDefectCubicNine.degree = 3 := by
  rw [degree_eq_natDegree cycleDefectCubicNine_monic.ne_zero,
    cycleDefectCubicNine_natDegree]
  norm_num

theorem cycleDefectCubicNine_irreducible_int :
    Irreducible cycleDefectCubicNine := by
  apply Polynomial.irreducible_of_eisenstein_criterion
    (P := Ideal.span {(3 : ℤ)})
  · rw [Ideal.span_singleton_prime (show (3 : ℤ) ≠ 0 by norm_num)]
    exact Int.prime_iff_natAbs_prime.mpr (by norm_num)
  · rw [show cycleDefectCubicNine.leadingCoeff = 1 from
      cycleDefectCubicNine_monic, Ideal.mem_span_singleton]
    norm_num
  · intro k hk
    rw [cycleDefectCubicNine_degree] at hk
    have hkn : k < 3 := WithBot.coe_lt_coe.mp hk
    simp only [Ideal.mem_span_singleton]
    interval_cases k <;>
      norm_num [cycleDefectCubicNine, coeff_sub, coeff_add,
        coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  · rw [cycleDefectCubicNine_degree]
    norm_num
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    unfold cycleDefectCubicNine
    norm_num
  · exact cycleDefectCubicNine_monic.isPrimitive

theorem cycleDefectCubicNine_irreducible_rat :
    Irreducible (cycleDefectCubicNine.map (Int.castRingHom ℚ)) := by
  exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      cycleDefectCubicNine_monic.isPrimitive).mp
    cycleDefectCubicNine_irreducible_int

theorem cycleDefectCubicSeven_monic : cycleDefectCubicSeven.Monic := by
  unfold cycleDefectCubicSeven
  monicity!

def cycleDefectCubicSevenShift : ℤ[X] := X ^ 3 - 7 * X ^ 2 + 14 * X - 7

theorem cycleDefectCubicSevenShift_monic :
    cycleDefectCubicSevenShift.Monic := by
  unfold cycleDefectCubicSevenShift
  monicity!

theorem cycleDefectCubicSevenShift_natDegree :
    cycleDefectCubicSevenShift.natDegree = 3 := by
  unfold cycleDefectCubicSevenShift
  compute_degree!

theorem cycleDefectCubicSevenShift_degree :
    cycleDefectCubicSevenShift.degree = 3 := by
  rw [degree_eq_natDegree cycleDefectCubicSevenShift_monic.ne_zero,
    cycleDefectCubicSevenShift_natDegree]
  norm_num

theorem cycleDefectCubicSevenShift_irreducible :
    Irreducible cycleDefectCubicSevenShift := by
  apply Polynomial.irreducible_of_eisenstein_criterion
    (P := Ideal.span {(7 : ℤ)})
  · rw [Ideal.span_singleton_prime (show (7 : ℤ) ≠ 0 by norm_num)]
    exact Int.prime_iff_natAbs_prime.mpr (by norm_num)
  · rw [show cycleDefectCubicSevenShift.leadingCoeff = 1 from
      cycleDefectCubicSevenShift_monic, Ideal.mem_span_singleton]
    norm_num
  · intro k hk
    rw [cycleDefectCubicSevenShift_degree] at hk
    have hkn : k < 3 := WithBot.coe_lt_coe.mp hk
    simp only [Ideal.mem_span_singleton]
    interval_cases k <;>
      norm_num [cycleDefectCubicSevenShift, coeff_sub, coeff_add,
        coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  · rw [cycleDefectCubicSevenShift_degree]
    norm_num
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    unfold cycleDefectCubicSevenShift
    norm_num
  · exact cycleDefectCubicSevenShift_monic.isPrimitive

theorem cycleDefectCubicSeven_irreducible_int :
    Irreducible cycleDefectCubicSeven := by
  have heq :
      (algEquivAevalXAddC (3 : ℤ)) cycleDefectCubicSeven =
        cycleDefectCubicSevenShift := by
    rw [algEquivAevalXAddC_apply, ← comp_eq_aeval]
    simp [cycleDefectCubicSeven, cycleDefectCubicSevenShift]
    ring
  have hirr := cycleDefectCubicSevenShift_irreducible
  rw [← heq] at hirr
  exact (MulEquiv.irreducible_iff
    (f := (algEquivAevalXAddC (3 : ℤ)).toMulEquiv)).mp hirr

theorem cycleDefectCubicSeven_irreducible_rat :
    Irreducible (cycleDefectCubicSeven.map (Int.castRingHom ℚ)) := by
  exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      cycleDefectCubicSeven_monic.isPrimitive).mp
    cycleDefectCubicSeven_irreducible_int

theorem cycleDefectQuinticEleven_monic :
    cycleDefectQuinticEleven.Monic := by
  unfold cycleDefectQuinticEleven
  monicity!

def cycleDefectQuinticElevenShift : ℤ[X] :=
  X ^ 5 - 11 * X ^ 4 + 44 * X ^ 3 - 77 * X ^ 2 + 55 * X - 11

theorem cycleDefectQuinticElevenShift_monic :
    cycleDefectQuinticElevenShift.Monic := by
  unfold cycleDefectQuinticElevenShift
  monicity!

theorem cycleDefectQuinticElevenShift_natDegree :
    cycleDefectQuinticElevenShift.natDegree = 5 := by
  unfold cycleDefectQuinticElevenShift
  compute_degree!

theorem cycleDefectQuinticElevenShift_degree :
    cycleDefectQuinticElevenShift.degree = 5 := by
  rw [degree_eq_natDegree cycleDefectQuinticElevenShift_monic.ne_zero,
    cycleDefectQuinticElevenShift_natDegree]
  norm_num

theorem cycleDefectQuinticElevenShift_irreducible :
    Irreducible cycleDefectQuinticElevenShift := by
  apply Polynomial.irreducible_of_eisenstein_criterion
    (P := Ideal.span {(11 : ℤ)})
  · rw [Ideal.span_singleton_prime (show (11 : ℤ) ≠ 0 by norm_num)]
    exact Int.prime_iff_natAbs_prime.mpr (by norm_num)
  · rw [show cycleDefectQuinticElevenShift.leadingCoeff = 1 from
      cycleDefectQuinticElevenShift_monic, Ideal.mem_span_singleton]
    norm_num
  · intro k hk
    rw [cycleDefectQuinticElevenShift_degree] at hk
    have hkn : k < 5 := WithBot.coe_lt_coe.mp hk
    simp only [Ideal.mem_span_singleton]
    interval_cases k <;>
      norm_num [cycleDefectQuinticElevenShift, coeff_sub, coeff_add,
        coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  · rw [cycleDefectQuinticElevenShift_degree]
    norm_num
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    unfold cycleDefectQuinticElevenShift
    norm_num
  · exact cycleDefectQuinticElevenShift_monic.isPrimitive

theorem cycleDefectQuinticEleven_irreducible_int :
    Irreducible cycleDefectQuinticEleven := by
  have heq :
      (algEquivAevalXAddC (3 : ℤ)) cycleDefectQuinticEleven =
        cycleDefectQuinticElevenShift := by
    rw [algEquivAevalXAddC_apply, ← comp_eq_aeval]
    simp [cycleDefectQuinticEleven, cycleDefectQuinticElevenShift]
    ring
  have hirr := cycleDefectQuinticElevenShift_irreducible
  rw [← heq] at hirr
  exact (MulEquiv.irreducible_iff
    (f := (algEquivAevalXAddC (3 : ℤ)).toMulEquiv)).mp hirr

theorem cycleDefectQuinticEleven_irreducible_rat :
    Irreducible (cycleDefectQuinticEleven.map (Int.castRingHom ℚ)) := by
  exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      cycleDefectQuinticEleven_monic.isPrimitive).mp
    cycleDefectQuinticEleven_irreducible_int

theorem cycleDefectSexticThirteen_monic :
    cycleDefectSexticThirteen.Monic := by
  unfold cycleDefectSexticThirteen
  monicity!

def cycleDefectSexticThirteenShift : ℤ[X] :=
  X ^ 6 - 13 * X ^ 5 + 65 * X ^ 4 - 156 * X ^ 3
    + 182 * X ^ 2 - 91 * X + 13

theorem cycleDefectSexticThirteenShift_monic :
    cycleDefectSexticThirteenShift.Monic := by
  unfold cycleDefectSexticThirteenShift
  monicity!

theorem cycleDefectSexticThirteenShift_natDegree :
    cycleDefectSexticThirteenShift.natDegree = 6 := by
  unfold cycleDefectSexticThirteenShift
  compute_degree!

theorem cycleDefectSexticThirteenShift_degree :
    cycleDefectSexticThirteenShift.degree = 6 := by
  rw [degree_eq_natDegree cycleDefectSexticThirteenShift_monic.ne_zero,
    cycleDefectSexticThirteenShift_natDegree]
  norm_num

theorem cycleDefectSexticThirteenShift_irreducible :
    Irreducible cycleDefectSexticThirteenShift := by
  apply Polynomial.irreducible_of_eisenstein_criterion
    (P := Ideal.span {(13 : ℤ)})
  · rw [Ideal.span_singleton_prime (show (13 : ℤ) ≠ 0 by norm_num)]
    exact Int.prime_iff_natAbs_prime.mpr (by norm_num)
  · rw [show cycleDefectSexticThirteenShift.leadingCoeff = 1 from
      cycleDefectSexticThirteenShift_monic, Ideal.mem_span_singleton]
    norm_num
  · intro k hk
    rw [cycleDefectSexticThirteenShift_degree] at hk
    have hkn : k < 6 := WithBot.coe_lt_coe.mp hk
    simp only [Ideal.mem_span_singleton]
    interval_cases k <;>
      norm_num [cycleDefectSexticThirteenShift, coeff_sub, coeff_add,
        coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  · rw [cycleDefectSexticThirteenShift_degree]
    norm_num
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    unfold cycleDefectSexticThirteenShift
    norm_num
  · exact cycleDefectSexticThirteenShift_monic.isPrimitive

theorem cycleDefectSexticThirteen_irreducible_int :
    Irreducible cycleDefectSexticThirteen := by
  have heq :
      (algEquivAevalXAddC (3 : ℤ)) cycleDefectSexticThirteen =
        cycleDefectSexticThirteenShift := by
    rw [algEquivAevalXAddC_apply, ← comp_eq_aeval]
    simp [cycleDefectSexticThirteen, cycleDefectSexticThirteenShift]
    ring
  have hirr := cycleDefectSexticThirteenShift_irreducible
  rw [← heq] at hirr
  exact (MulEquiv.irreducible_iff
    (f := (algEquivAevalXAddC (3 : ℤ)).toMulEquiv)).mp
      hirr

theorem cycleDefectSexticThirteen_irreducible_rat :
    Irreducible (cycleDefectSexticThirteen.map (Int.castRingHom ℚ)) := by
  exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      cycleDefectSexticThirteen_monic.isPrimitive).mp
    cycleDefectSexticThirteen_irreducible_int

end

end Erdos85
