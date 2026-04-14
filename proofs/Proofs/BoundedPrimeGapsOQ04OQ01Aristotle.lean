/-
  Aristotle targets for Bounded Prime Gaps OQ-04-OQ-01 (Pólya-Vinogradov)
  Routine supporting lemmas for automated proof search.
  See BoundedPrimeGapsOQ04OQ01.lean for the main formalization.
-/
import Mathlib

namespace BoundedPrimeGapsOQ04OQ01Aristotle

open Complex Real Finset MulChar ZMod

noncomputable section

/-
The explicit exponential sum equals the abstract Gauss sum with stdAddChar.
-/
lemma sum_range_eq_gaussSum (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∑ t ∈ Finset.range q, χ t * exp (2 * ↑π * I * ↑(t : ℤ) / ↑q) =
    gaussSum χ (ZMod.stdAddChar (N := q)) := by
  unfold gaussSum;
  have h_stdAddChar : ∀ a : ZMod q, ZMod.stdAddChar a = Complex.exp (2 * Real.pi * Complex.I * (a.val : ℝ) / q) := by
    unfold ZMod.stdAddChar;
    simp +decide [ ZMod.toCircle, Circle.coeHom ];
    simp +decide [ AddCircle.toCircle_addChar, ZMod.toAddCircle ];
    simp +decide [ ZMod.lift ];
    simp +decide [ AddMonoidHom.liftOfRightInverse ];
    simp +decide [ AddMonoidHom.liftOfRightInverseAux ];
    simp +decide [ AddCircle.toCircle, Complex.exp_ne_zero ];
    exact fun a => by ring;
  rcases q with ( _ | _ | q ) <;> simp_all +decide [ Finset.sum_range, ZMod ];
  · exact False.elim <| NeZero.ne 0 rfl;
  · congr!

/-
For a MulChar on ZMod q valued in ℂ, star of a character value equals the inverse character
value.
-/
lemma star_mulChar_apply (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    starRingEnd ℂ (χ a) = χ⁻¹ a := by
  nontriviality;
  have h_conj : ∀ (z : ℂ), z ^ (Nat.totient q) = 1 → starRingEnd ℂ z = Ring.inverse z := by
    intro z hz
    have h_conj : starRingEnd ℂ z = 1 / z := by
      simp +decide [ Complex.normSq_eq_norm_sq, Complex.ext_iff ];
      have := congr_arg Norm.norm hz ; norm_num at this ; rw [ pow_eq_one_iff_of_nonneg ] at this <;> aesop;
    aesop;
  by_cases ha : IsUnit a;
  · obtain ⟨ u, rfl ⟩ := ha;
    convert h_conj _ _;
    rw [ ← map_pow, show ( u : ZMod q ) ^ q.totient = 1 from ?_, map_one ];
    norm_cast;
    norm_num;
  · rw [ χ.map_nonunit, MulChar.map_nonunit ] <;> aesop

/-
For stdAddChar on ZMod q, the star of a value equals the inverse character value.
-/
lemma star_stdAddChar_apply (q : ℕ) [NeZero q] (a : ZMod q) :
    starRingEnd ℂ ((ZMod.stdAddChar (N := q)) a) = (ZMod.stdAddChar (N := q))⁻¹ a := by
  have h_inv_apply : ZMod.stdAddChar⁻¹ a = ZMod.stdAddChar (-a) := by
    exact AddChar.inv_apply ZMod.stdAddChar a
  rw [ h_inv_apply ];
  exact Eq.symm (AddChar.map_neg_eq_conj ZMod.stdAddChar a)

/-- The complex conjugate of the Gauss sum equals the Gauss sum of inverse characters. -/
lemma star_gaussSum_eq (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    starRingEnd ℂ (gaussSum χ (ZMod.stdAddChar (N := q))) =
    gaussSum χ⁻¹ (ZMod.stdAddChar (N := q))⁻¹ := by
  simp only [gaussSum, map_sum, map_mul, star_mulChar_apply, star_stdAddChar_apply]

/-
The mulShift of stdAddChar by -1 equals stdAddChar⁻¹.
-/
lemma stdAddChar_mulShift_neg_one (q : ℕ) [NeZero q] :
    (ZMod.stdAddChar (N := q)).mulShift (-1) = (ZMod.stdAddChar (N := q))⁻¹ := by
  ext a;
  simp [AddChar.mulShift, AddChar.inv_apply]

/-
Gauss sum times conjugate via gaussSum_mulShift: χ(-1) * gaussSum χ stdAddChar⁻¹ = gaussSum χ stdAddChar.
    This follows from gaussSum_mulShift applied with unit -1.
-/
lemma gaussSum_mul_inv_eq (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    χ (-1) * gaussSum χ (ZMod.stdAddChar (N := q))⁻¹ = gaussSum χ (ZMod.stdAddChar (N := q)) := by
  convert gaussSum_mulShift χ ( ZMod.stdAddChar ( N := q ) ) ( -1 ) using 1;
  simp +decide [ stdAddChar_mulShift_neg_one ]

/-
The Gauss sum product formula from Fourier inversion:
    τ(χ) * τ(χ⁻¹) = q * χ(-1), for primitive χ mod q.
-/
lemma gaussSum_mul_gaussSum_inv (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    gaussSum χ (ZMod.stdAddChar (N := q)) * gaussSum χ⁻¹ (ZMod.stdAddChar (N := q)) =
    (q : ℂ) * χ (-1) := by
  -- By Fourier inversion, we have $\tau(\chi) \tau(\chi^{-1}) = q \chi(-1)$.
  have h_fourier_inversion : (gaussSum χ (ZMod.stdAddChar (N := q))) * (gaussSum χ⁻¹ (ZMod.stdAddChar (N := q))) = q * χ (-1) := by
    have := ZMod.dft_dft (χ : ZMod q → ℂ)
    -- By Fourier inversion, we have $\tau(\chi) \tau(\chi^{-1}) = q \chi(-1)$ for primitive $\chi$.
    have h_fourier_inv : (𝓕 (fun k => χ⁻¹ (-k) * gaussSum χ (ZMod.stdAddChar (N := q)))) 1 = q * χ (-1) := by
      convert congr_fun this 1 using 1;
      rw [ show 𝓕 ( χ : ZMod q → ℂ ) = fun k => χ⁻¹ ( -k ) * gaussSum χ ( ZMod.stdAddChar ( N := q ) ) from funext fun k => ?_ ];
      convert hprim.fourierTransform_eq_inv_mul_gaussSum k using 1;
    convert h_fourier_inv using 1 ; simp +decide [ ZMod.dft, mul_comm ] ; ring!;
    nontriviality;
    erw [ Finset.mul_sum _ _ _ ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, ZMod.dft ] ; ring!;
    refine' Finset.sum_bij ( fun x _ => -x ) _ _ _ _ <;> simp +decide [ mul_assoc, mul_comm, mul_left_comm ];
    exact fun b => ⟨ -b, neg_neg b ⟩;
  exact h_fourier_inversion

/-
The norm of a character value at a unit is 1.
-/
lemma norm_mulChar_unit (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (u : (ZMod q)ˣ) :
    ‖χ (u : ZMod q)‖ = 1 := by
  exact?

/-
The norm of gaussSum χ⁻¹ stdAddChar equals the norm of gaussSum χ stdAddChar.
-/
lemma norm_gaussSum_inv_eq (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖gaussSum χ⁻¹ (ZMod.stdAddChar (N := q))‖ = ‖gaussSum χ (ZMod.stdAddChar (N := q))‖ := by
  have := @gaussSum_mul_inv_eq q ‹_› χ⁻¹;
  replace := congr_arg Norm.norm this ; norm_num at *;
  rw [ ← this, show ‖χ⁻¹ ( -1 )‖ = 1 from ?_ ];
  · rw [ ← star_gaussSum_eq, Complex.norm_conj ];
    ring;
  · convert norm_mulChar_unit q χ⁻¹ ( -1 )

/-
The norm squared of the Gauss sum of a primitive nontrivial character equals q.
-/
lemma norm_sq_gaussSum (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) :
    ‖gaussSum χ (ZMod.stdAddChar (N := q))‖ ^ 2 = (q : ℝ) := by
  -- From gaussSum_mul_gaussSum_inv: τ * τ(χ⁻¹) = q * χ(-1)
  -- Taking norms: ‖τ‖ * ‖τ(χ⁻¹)‖ = q (since ‖χ(-1)‖ = 1)
  -- By norm_gaussSum_inv_eq: ‖τ(χ⁻¹)‖ = ‖τ‖
  -- So ‖τ‖² = q
  have h_norm : ‖gaussSum χ (ZMod.stdAddChar (N := q)) * gaussSum χ⁻¹ (ZMod.stdAddChar (N := q))‖ = q := by
    rw [ gaussSum_mul_gaussSum_inv ];
    · have := norm_mulChar_unit q χ ( -1 );
      aesop;
    · assumption;
    · assumption;
  rw [ ← h_norm, norm_mul, sq, norm_gaussSum_inv_eq ]

-- Routine: The absolute value of the Gauss sum of a primitive character equals √q.
-- |τ(χ)| = √q for χ primitive mod q.
theorem gaussSumNorm (q : ℕ) (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    ‖∑ t ∈ Finset.range q, χ t * exp (2 * ↑π * I * ↑(t : ℤ) / ↑q)‖ =
    Real.sqrt (q : ℝ) := by
  haveI : NeZero q := ⟨by omega⟩
  rw [sum_range_eq_gaussSum q χ]
  have h := norm_sq_gaussSum q χ hχ hprim
  have hnn : (0 : ℝ) ≤ ‖gaussSum χ (ZMod.stdAddChar (N := q))‖ := norm_nonneg _
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hsq : Real.sqrt (q : ℝ) ^ 2 = (q : ℝ) := Real.sq_sqrt hq0
  have hns : 0 ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  nlinarith [sq_nonneg (‖gaussSum χ (ZMod.stdAddChar (N := q))‖ - Real.sqrt (q : ℝ))]

end

end BoundedPrimeGapsOQ04OQ01Aristotle