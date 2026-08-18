import Mathlib

/-! # Cycle-root transport to order-64 defect polynomials -/

open Polynomial

namespace Erdos85

noncomputable section

theorem chebyshevC_three
    (K : Type*) [CommRing K] :
    Chebyshev.C K 3 = X ^ 3 - 3 * X := by
  have h3 := Chebyshev.C_add_two K 1
  norm_num [Chebyshev.C_one, Chebyshev.C_two] at h3
  rw [h3]
  ring

theorem chebyshevC_five
    (K : Type*) [CommRing K] :
    Chebyshev.C K 5 = X ^ 5 - 5 * X ^ 3 + 5 * X := by
  have h3 := Chebyshev.C_add_two K 1
  have h4 := Chebyshev.C_add_two K 2
  have h5 := Chebyshev.C_add_two K 3
  norm_num [Chebyshev.C_one, Chebyshev.C_two] at h3 h4 h5
  rw [h5, h4, h3]
  ring

theorem chebyshevC_six
    (K : Type*) [CommRing K] :
    Chebyshev.C K 6 = X ^ 6 - 6 * X ^ 4 + 9 * X ^ 2 - 2 := by
  have h3 := Chebyshev.C_add_two K 1
  have h4 := Chebyshev.C_add_two K 2
  have h5 := Chebyshev.C_add_two K 3
  have h6 := Chebyshev.C_add_two K 4
  norm_num [Chebyshev.C_one, Chebyshev.C_two] at h3 h4 h5 h6
  rw [h6, h5, h4, h3]
  ring

theorem chebyshevC_seven
    (K : Type*) [CommRing K] :
    Chebyshev.C K 7 =
      X ^ 7 - 7 * X ^ 5 + 14 * X ^ 3 - 7 * X := by
  have h3 := Chebyshev.C_add_two K 1
  have h4 := Chebyshev.C_add_two K 2
  have h5 := Chebyshev.C_add_two K 3
  have h6 := Chebyshev.C_add_two K 4
  have h7 := Chebyshev.C_add_two K 5
  norm_num [Chebyshev.C_one, Chebyshev.C_two] at h3 h4 h5 h6 h7
  rw [h7, h6, h5, h4, h3]
  ring

theorem chebyshevC_eight
    (K : Type*) [CommRing K] :
    Chebyshev.C K 8 =
      X ^ 8 - 8 * X ^ 6 + 20 * X ^ 4 - 16 * X ^ 2 + 2 := by
  have h3 := Chebyshev.C_add_two K 1
  have h4 := Chebyshev.C_add_two K 2
  have h5 := Chebyshev.C_add_two K 3
  have h6 := Chebyshev.C_add_two K 4
  have h7 := Chebyshev.C_add_two K 5
  have h8 := Chebyshev.C_add_two K 6
  norm_num [Chebyshev.C_one, Chebyshev.C_two] at h3 h4 h5 h6 h7 h8
  rw [h8, h7, h6, h5, h4, h3]
  ring

theorem chebyshevC_nine
    (K : Type*) [CommRing K] :
    Chebyshev.C K 9 =
      X ^ 9 - 9 * X ^ 7 + 27 * X ^ 5 - 30 * X ^ 3 + 9 * X := by
  have h3 := Chebyshev.C_add_two K 1
  have h4 := Chebyshev.C_add_two K 2
  have h5 := Chebyshev.C_add_two K 3
  have h6 := Chebyshev.C_add_two K 4
  have h7 := Chebyshev.C_add_two K 5
  have h8 := Chebyshev.C_add_two K 6
  have h9 := Chebyshev.C_add_two K 7
  norm_num [Chebyshev.C_one, Chebyshev.C_two] at h3 h4 h5 h6 h7 h8 h9
  rw [h9, h8, h7, h6, h5, h4, h3]
  ring

theorem chebyshevC_ten
    (K : Type*) [CommRing K] :
    Chebyshev.C K 10 =
      X ^ 10 - 10 * X ^ 8 + 35 * X ^ 6 - 50 * X ^ 4
        + 25 * X ^ 2 - 2 := by
  have h3 := Chebyshev.C_add_two K 1
  have h4 := Chebyshev.C_add_two K 2
  have h5 := Chebyshev.C_add_two K 3
  have h6 := Chebyshev.C_add_two K 4
  have h7 := Chebyshev.C_add_two K 5
  have h8 := Chebyshev.C_add_two K 6
  have h9 := Chebyshev.C_add_two K 7
  have h10 := Chebyshev.C_add_two K 8
  norm_num [Chebyshev.C_one, Chebyshev.C_two] at h3 h4 h5 h6 h7 h8 h9 h10
  rw [h10, h9, h8, h7, h6, h5, h4, h3]
  ring

theorem chebyshevC_eleven
    (K : Type*) [CommRing K] :
    Chebyshev.C K 11 =
      X ^ 11 - 11 * X ^ 9 + 44 * X ^ 7 - 77 * X ^ 5
        + 55 * X ^ 3 - 11 * X := by
  have h3 := Chebyshev.C_add_two K 1
  have h4 := Chebyshev.C_add_two K 2
  have h5 := Chebyshev.C_add_two K 3
  have h6 := Chebyshev.C_add_two K 4
  have h7 := Chebyshev.C_add_two K 5
  have h8 := Chebyshev.C_add_two K 6
  have h9 := Chebyshev.C_add_two K 7
  have h10 := Chebyshev.C_add_two K 8
  have h11 := Chebyshev.C_add_two K 9
  norm_num [Chebyshev.C_one, Chebyshev.C_two] at h3 h4 h5 h6 h7 h8 h9 h10 h11
  rw [h11, h10, h9, h8, h7, h6, h5, h4, h3]
  ring

theorem chebyshevC_thirteen
    (K : Type*) [CommRing K] :
    Chebyshev.C K 13 =
      X ^ 13 - 13 * X ^ 11 + 65 * X ^ 9 - 156 * X ^ 7
        + 182 * X ^ 5 - 91 * X ^ 3 + 13 * X := by
  have h3 := Chebyshev.C_add_two K 1
  have h4 := Chebyshev.C_add_two K 2
  have h5 := Chebyshev.C_add_two K 3
  have h6 := Chebyshev.C_add_two K 4
  have h7 := Chebyshev.C_add_two K 5
  have h8 := Chebyshev.C_add_two K 6
  have h9 := Chebyshev.C_add_two K 7
  have h10 := Chebyshev.C_add_two K 8
  have h11 := Chebyshev.C_add_two K 9
  have h12 := Chebyshev.C_add_two K 10
  have h13 := Chebyshev.C_add_two K 11
  norm_num [Chebyshev.C_one, Chebyshev.C_two] at h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  rw [h13, h12, h11, h10, h9, h8, h7, h6, h5, h4, h3]
  ring

theorem chebyshevC_sixteen
    (K : Type*) [CommRing K] :
    Chebyshev.C K 16 =
      X ^ 16 - 16 * X ^ 14 + 104 * X ^ 12 - 352 * X ^ 10
        + 660 * X ^ 8 - 672 * X ^ 6 + 336 * X ^ 4
        - 64 * X ^ 2 + 2 := by
  calc
    Chebyshev.C K 16 = (Chebyshev.C K 2).comp (Chebyshev.C K 8) := by
      simpa using Chebyshev.C_mul K 2 8
    _ = _ := by
      rw [Chebyshev.C_two, chebyshevC_eight]
      simp only [sub_comp, pow_comp, X_comp, ofNat_comp]
      ring

/-- Three-cycle roots give only the rational defect values `3` and `6`. -/
theorem cycleThree_defect_root
    {K : Type*} [Field K] [CharZero K] (α : K)
    (hα : (Chebyshev.C K 3).eval α = 2) :
    7 - α ^ 2 = 3 ∨ 7 - α ^ 2 = 6 := by
  have hfactor : (α - 2) * (α + 1) ^ 2 = 0 := by
    rw [chebyshevC_three] at hα
    simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat] at hα
    linear_combination hα
  rcases mul_eq_zero.mp hfactor with hprincipal | hrational
  · left
    have : α = 2 := sub_eq_zero.mp hprincipal
    subst α
    norm_num
  · right
    have hplus : α + 1 = 0 := by
      simpa [pow_two] using
        (mul_self_eq_zero.mp (by simpa [pow_two] using hrational))
    have : α = -1 := eq_neg_of_add_eq_zero_left hplus
    subst α
    norm_num

/-- A root of the five-cycle adjacency polynomial maps either to the
principal defect value `3` or to the quadratic defect factor. -/
theorem cycleFive_defect_root
    {K : Type*} [Field K] [CharZero K] (α : K)
    (hα : (Chebyshev.C K 5).eval α = 2) :
    7 - α ^ 2 = 3 ∨
      (7 - α ^ 2) ^ 2 - 11 * (7 - α ^ 2) + 29 = 0 := by
  have hfactor : (α - 2) * (α ^ 2 + α - 1) ^ 2 = 0 := by
    rw [chebyshevC_five] at hα
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X,
      eval_ofNat] at hα
    linear_combination hα
  rcases mul_eq_zero.mp hfactor with hprincipal | hnonlinear
  · left
    have : α = 2 := sub_eq_zero.mp hprincipal
    subst α
    norm_num
  · right
    have hquad : α ^ 2 + α - 1 = 0 := by
      simpa [pow_two] using (mul_self_eq_zero.mp (by simpa [pow_two] using hnonlinear))
    calc
      (7 - α ^ 2) ^ 2 - 11 * (7 - α ^ 2) + 29 =
          (α ^ 2 + α - 1) * (α ^ 2 - α - 1) := by ring
      _ = 0 := by rw [hquad, zero_mul]

/-- Six-cycle roots likewise give only the rational defect values. -/
theorem cycleSix_defect_root
    {K : Type*} [Field K] [CharZero K] (α : K)
    (hα : (Chebyshev.C K 6).eval α = 2) :
    7 - α ^ 2 = 3 ∨ 7 - α ^ 2 = 6 := by
  have hfactor :
      ((α - 2) * (α + 2)) * ((α - 1) ^ 2 * (α + 1) ^ 2) = 0 := by
    rw [chebyshevC_six] at hα
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X,
      eval_ofNat] at hα
    linear_combination hα
  rcases mul_eq_zero.mp hfactor with hthree | hsix
  · left
    rcases mul_eq_zero.mp hthree with hplus | hminus
    · have : α = 2 := sub_eq_zero.mp hplus
      subst α
      norm_num
    · have : α = -2 := eq_neg_of_add_eq_zero_left hminus
      subst α
      norm_num
  · right
    rcases mul_eq_zero.mp hsix with hone | hnegone
    · have h : α - 1 = 0 := by
        simpa [pow_two] using
          (mul_self_eq_zero.mp (by simpa [pow_two] using hone))
      have : α = 1 := sub_eq_zero.mp h
      subst α
      norm_num
    · have h : α + 1 = 0 := by
        simpa [pow_two] using
          (mul_self_eq_zero.mp (by simpa [pow_two] using hnegone))
      have : α = -1 := eq_neg_of_add_eq_zero_left h
      subst α
      norm_num

/-- A root of the seven-cycle adjacency polynomial maps either to the
principal defect value `3` or to its cubic defect factor. -/
theorem cycleSeven_defect_root
    {K : Type*} [Field K] [CharZero K] (α : K)
    (hα : (Chebyshev.C K 7).eval α = 2) :
    7 - α ^ 2 = 3 ∨
      (7 - α ^ 2) ^ 3 - 16 * (7 - α ^ 2) ^ 2
        + 83 * (7 - α ^ 2) - 139 = 0 := by
  have hfactor :
      (α - 2) * (α ^ 3 + α ^ 2 - 2 * α - 1) ^ 2 = 0 := by
    rw [chebyshevC_seven] at hα
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X,
      eval_ofNat] at hα
    linear_combination hα
  rcases mul_eq_zero.mp hfactor with hprincipal | hnonlinear
  · left
    have : α = 2 := sub_eq_zero.mp hprincipal
    subst α
    norm_num
  · right
    have hcubic : α ^ 3 + α ^ 2 - 2 * α - 1 = 0 := by
      simpa [pow_two] using
        (mul_self_eq_zero.mp (by simpa [pow_two] using hnonlinear))
    calc
      (7 - α ^ 2) ^ 3 - 16 * (7 - α ^ 2) ^ 2
          + 83 * (7 - α ^ 2) - 139 =
          (α ^ 3 + α ^ 2 - 2 * α - 1) *
            (-α ^ 3 + α ^ 2 + 2 * α - 1) := by ring
      _ = 0 := by rw [hcubic, zero_mul]

/-- Eight-cycle roots give exactly the rational values `3`, `5`, and `7`. -/
theorem cycleEight_defect_root
    {K : Type*} [Field K] [CharZero K] (α : K)
    (hα : (Chebyshev.C K 8).eval α = 2) :
    7 - α ^ 2 = 3 ∨ 7 - α ^ 2 = 5 ∨ 7 - α ^ 2 = 7 := by
  have hfactor :
      ((α - 2) * (α + 2)) * (α ^ 2 * (α ^ 2 - 2) ^ 2) = 0 := by
    rw [chebyshevC_eight] at hα
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X,
      eval_ofNat] at hα
    linear_combination hα
  rcases mul_eq_zero.mp hfactor with hthree | hrest
  · left
    rcases mul_eq_zero.mp hthree with hplus | hminus
    · have : α = 2 := sub_eq_zero.mp hplus
      subst α
      norm_num
    · have : α = -2 := eq_neg_of_add_eq_zero_left hminus
      subst α
      norm_num
  · rcases mul_eq_zero.mp hrest with hzero | hfive
    · right; right
      have : α = 0 :=
        mul_self_eq_zero.mp (by simpa [pow_two] using hzero)
      subst α
      norm_num
    · right; left
      have h : α ^ 2 - 2 = 0 := by
        simpa [pow_two] using
          (mul_self_eq_zero.mp (by simpa [pow_two] using hfive))
      have : α ^ 2 = 2 := sub_eq_zero.mp h
      rw [this]
      norm_num

/-- A root of the nine-cycle adjacency polynomial maps to a rational
defect value or to the nine-cycle cubic defect factor. -/
theorem cycleNine_defect_root
    {K : Type*} [Field K] [CharZero K] (α : K)
    (hα : (Chebyshev.C K 9).eval α = 2) :
    7 - α ^ 2 = 3 ∨ 7 - α ^ 2 = 6 ∨
      (7 - α ^ 2) ^ 3 - 15 * (7 - α ^ 2) ^ 2
        + 72 * (7 - α ^ 2) - 111 = 0 := by
  have hfactor :
      (α - 2) * ((α + 1) ^ 2 * (α ^ 3 - 3 * α + 1) ^ 2) = 0 := by
    rw [chebyshevC_nine] at hα
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X,
      eval_ofNat] at hα
    linear_combination hα
  rcases mul_eq_zero.mp hfactor with hprincipal | hrest
  · left
    have : α = 2 := sub_eq_zero.mp hprincipal
    subst α
    norm_num
  · rcases mul_eq_zero.mp hrest with hrational | hnonlinear
    · right; left
      have hplus : α + 1 = 0 := by
        simpa [pow_two] using
          (mul_self_eq_zero.mp (by simpa [pow_two] using hrational))
      have : α = -1 := eq_neg_of_add_eq_zero_left hplus
      subst α
      norm_num
    · right; right
      have hcubic : α ^ 3 - 3 * α + 1 = 0 := by
        simpa [pow_two] using
          (mul_self_eq_zero.mp (by simpa [pow_two] using hnonlinear))
      calc
        (7 - α ^ 2) ^ 3 - 15 * (7 - α ^ 2) ^ 2
            + 72 * (7 - α ^ 2) - 111 =
            (α ^ 3 - 3 * α + 1) * (-α ^ 3 + 3 * α + 1) := by ring
        _ = 0 := by rw [hcubic, zero_mul]

/-- Ten-cycle roots map to the principal value or the same quadratic defect
factor as the five-cycle roots. -/
theorem cycleTen_defect_root
    {K : Type*} [Field K] [CharZero K] (α : K)
    (hα : (Chebyshev.C K 10).eval α = 2) :
    7 - α ^ 2 = 3 ∨
      (7 - α ^ 2) ^ 2 - 11 * (7 - α ^ 2) + 29 = 0 := by
  let fp : K := α ^ 2 + α - 1
  let fm : K := α ^ 2 - α - 1
  have hfactor :
      ((α - 2) * (α + 2)) * (fp ^ 2 * fm ^ 2) = 0 := by
    rw [chebyshevC_ten] at hα
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X,
      eval_ofNat] at hα
    dsimp [fp, fm]
    linear_combination hα
  rcases mul_eq_zero.mp hfactor with hprincipal | hnonlinear
  · left
    rcases mul_eq_zero.mp hprincipal with hplus | hminus
    · have : α = 2 := sub_eq_zero.mp hplus
      subst α
      norm_num
    · have : α = -2 := eq_neg_of_add_eq_zero_left hminus
      subst α
      norm_num
  · right
    rcases mul_eq_zero.mp hnonlinear with hp | hm
    · have hfp : fp = 0 := by
        simpa [pow_two] using
          (mul_self_eq_zero.mp (by simpa [pow_two] using hp))
      calc
        (7 - α ^ 2) ^ 2 - 11 * (7 - α ^ 2) + 29 = fp * fm := by
          dsimp [fp, fm]; ring
        _ = 0 := by rw [hfp, zero_mul]
    · have hfm : fm = 0 := by
        simpa [pow_two] using
          (mul_self_eq_zero.mp (by simpa [pow_two] using hm))
      calc
        (7 - α ^ 2) ^ 2 - 11 * (7 - α ^ 2) + 29 = fp * fm := by
          dsimp [fp, fm]; ring
        _ = 0 := by rw [hfm, mul_zero]

/-- Eleven-cycle roots map to the principal value or the explicit quintic
defect factor. -/
theorem cycleEleven_defect_root
    {K : Type*} [Field K] [CharZero K] (α : K)
    (hα : (Chebyshev.C K 11).eval α = 2) :
    7 - α ^ 2 = 3 ∨
      (7 - α ^ 2) ^ 5 - 26 * (7 - α ^ 2) ^ 4
        + 266 * (7 - α ^ 2) ^ 3 - 1337 * (7 - α ^ 2) ^ 2
        + 3298 * (7 - α ^ 2) - 3191 = 0 := by
  let f : K := α ^ 5 + α ^ 4 - 4 * α ^ 3 - 3 * α ^ 2 + 3 * α + 1
  have hfactor : (α - 2) * f ^ 2 = 0 := by
    rw [chebyshevC_eleven] at hα
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X,
      eval_ofNat] at hα
    dsimp [f]
    linear_combination hα
  rcases mul_eq_zero.mp hfactor with hprincipal | hnonlinear
  · left
    have : α = 2 := sub_eq_zero.mp hprincipal
    subst α
    norm_num
  · right
    have hf : f = 0 := by
      simpa [pow_two] using
        (mul_self_eq_zero.mp (by simpa [pow_two] using hnonlinear))
    calc
      (7 - α ^ 2) ^ 5 - 26 * (7 - α ^ 2) ^ 4
          + 266 * (7 - α ^ 2) ^ 3 - 1337 * (7 - α ^ 2) ^ 2
          + 3298 * (7 - α ^ 2) - 3191 =
          f * (-α ^ 5 + α ^ 4 + 4 * α ^ 3 - 3 * α ^ 2
            - 3 * α + 1) := by dsimp [f]; ring
      _ = 0 := by rw [hf, zero_mul]

/-- Thirteen-cycle roots map to the principal value or the explicit sextic
defect factor. -/
theorem cycleThirteen_defect_root
    {K : Type*} [Field K] [CharZero K] (α : K)
    (hα : (Chebyshev.C K 13).eval α = 2) :
    7 - α ^ 2 = 3 ∨
      (7 - α ^ 2) ^ 6 - 31 * (7 - α ^ 2) ^ 5
        + 395 * (7 - α ^ 2) ^ 4 - 2646 * (7 - α ^ 2) ^ 3
        + 9821 * (7 - α ^ 2) ^ 2 - 19138 * (7 - α ^ 2)
        + 15289 = 0 := by
  let f : K := α ^ 6 + α ^ 5 - 5 * α ^ 4 - 4 * α ^ 3
    + 6 * α ^ 2 + 3 * α - 1
  have hfactor : (α - 2) * f ^ 2 = 0 := by
    rw [chebyshevC_thirteen] at hα
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X,
      eval_ofNat] at hα
    dsimp [f]
    linear_combination hα
  rcases mul_eq_zero.mp hfactor with hprincipal | hnonlinear
  · left
    have : α = 2 := sub_eq_zero.mp hprincipal
    subst α
    norm_num
  · right
    have hf : f = 0 := by
      simpa [pow_two] using
        (mul_self_eq_zero.mp (by simpa [pow_two] using hnonlinear))
    calc
      (7 - α ^ 2) ^ 6 - 31 * (7 - α ^ 2) ^ 5
          + 395 * (7 - α ^ 2) ^ 4 - 2646 * (7 - α ^ 2) ^ 3
          + 9821 * (7 - α ^ 2) ^ 2 - 19138 * (7 - α ^ 2)
          + 15289 =
          f * (α ^ 6 - α ^ 5 - 5 * α ^ 4 + 4 * α ^ 3
            + 6 * α ^ 2 - 3 * α - 1) := by dsimp [f]; ring
      _ = 0 := by rw [hf, zero_mul]

/-- Sixteen-cycle roots give the three rational values seen for `C₈`, or
the remaining quadratic factor `y² - 10y + 23`. -/
theorem cycleSixteen_defect_root
    {K : Type*} [Field K] [CharZero K] (α : K)
    (hα : (Chebyshev.C K 16).eval α = 2) :
    7 - α ^ 2 = 3 ∨ 7 - α ^ 2 = 5 ∨ 7 - α ^ 2 = 7 ∨
      (7 - α ^ 2) ^ 2 - 10 * (7 - α ^ 2) + 23 = 0 := by
  let f : K := α ^ 4 - 4 * α ^ 2 + 2
  have hfactor :
      ((α - 2) * (α + 2)) *
        (α ^ 2 * ((α ^ 2 - 2) ^ 2 * f ^ 2)) = 0 := by
    rw [chebyshevC_sixteen] at hα
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X,
      eval_ofNat] at hα
    dsimp [f]
    linear_combination hα
  rcases mul_eq_zero.mp hfactor with hthree | hrest
  · left
    rcases mul_eq_zero.mp hthree with hplus | hminus
    · have : α = 2 := sub_eq_zero.mp hplus
      subst α
      norm_num
    · have : α = -2 := eq_neg_of_add_eq_zero_left hminus
      subst α
      norm_num
  · rcases mul_eq_zero.mp hrest with hzero | hrest
    · right; right; left
      have : α = 0 :=
        mul_self_eq_zero.mp (by simpa [pow_two] using hzero)
      subst α
      norm_num
    · rcases mul_eq_zero.mp hrest with hfive | hquadratic
      · right; left
        have h : α ^ 2 - 2 = 0 := by
          simpa [pow_two] using
            (mul_self_eq_zero.mp (by simpa [pow_two] using hfive))
        have : α ^ 2 = 2 := sub_eq_zero.mp h
        rw [this]
        norm_num
      · right; right; right
        have hf : f = 0 := by
          simpa [pow_two] using
            (mul_self_eq_zero.mp (by simpa [pow_two] using hquadratic))
        calc
          (7 - α ^ 2) ^ 2 - 10 * (7 - α ^ 2) + 23 = f := by
            dsimp [f]; ring
          _ = 0 := hf

end

end Erdos85
