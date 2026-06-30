/-
  The splitting field of X⁴ − 2 as a CONCRETE subfield of ℂ
  (fourth-root-2-irrational-oq-01)

  Open Question:
  "The splitting field of X⁴ − 2 is ℚ(⁴√2, i), of degree 8, with Galois group D₄."

  The roots of X⁴ − 2 in ℂ are ⁴√2 · iᵏ (k = 0,1,2,3), so the splitting field is
  ℚ(⁴√2, i).  Two siblings already cover parts of this picture:

    * `FourthRoot2Degree4.lean`   : [ℚ(⁴√2) : ℚ] = 4 (the real fourth root), via
      Eisenstein irreducibility of X⁴ − 2.
    * `InverseGaloisD4.lean`      : the ABSTRACT statement
      |Gal(X⁴−2 / ℚ)| = 8 and the dihedral group D₄, working inside the abstract
      `(X⁴ − 2).SplittingField`.

  This file is DISTINCT: it builds the splitting field as the CONCRETE subfield
  `ℚ⟮frc, I⟯ ⊆ ℂ` (with `frc = ⁴√2 ∈ ℝ ⊆ ℂ` and `I = Complex.I`) and proves
  `[ℚ⟮frc, I⟯ : ℚ] = 8` directly.  The conceptual crux — and the reason the
  splitting field is strictly larger than ℚ(⁴√2) — is the **realness obstruction**

      `Complex.I ∉ ℚ⟮frc⟯`,

  proved here cleanly: every element of `ℚ⟮frc⟯` has zero imaginary part (it is
  generated over ℚ by the *real* number `frc`), whereas `Complex.I.im = 1`.  This
  is the concrete-ℂ counterpart of the ℝ-embedding argument in `InverseGaloisD4`.

  Tags: number-theory, field-theory, galois, splitting-field, fourth-root,
        quartic, dihedral
-/

import Mathlib
import Proofs.InverseGaloisD4

open Polynomial IntermediateField

namespace FourthRoot2SplittingFieldOQ01

/-- `X² + 1` is monic over any nontrivial commutative ring. -/
private theorem monic_X2_add_1 {R : Type*} [CommRing R] [Nontrivial R] :
    (X ^ 2 + 1 : R[X]).Monic := by
  simpa using monic_X_pow_add_C (a := (1 : R)) (n := 2) (by norm_num)

/-! ## Part I: The complex fourth root of 2 -/

/-- The fourth root of `2`, viewed inside `ℂ` as the real number `√√2`. -/
noncomputable def frc : ℂ := ((Real.sqrt (Real.sqrt 2) : ℝ) : ℂ)

/-- `frc` is real: its imaginary part vanishes. -/
@[simp] theorem frc_im : frc.im = 0 := by simp [frc]

/-- `frc⁴ = 2`. -/
theorem frc_pow_four : frc ^ 4 = 2 := by
  have hr : (Real.sqrt (Real.sqrt 2)) ^ 4 = 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
      Real.sq_sqrt (Real.sqrt_nonneg 2), Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  unfold frc
  rw [← Complex.ofReal_pow, hr]
  norm_num

/-- `frc` is integral over ℚ: a root of `X⁴ − 2`. -/
theorem frc_isIntegral : IsIntegral ℚ frc :=
  ⟨X ^ 4 - C 2, monic_X_pow_sub_C _ (by norm_num), by
    simp [frc_pow_four]⟩

/-- `X⁴ − 2` is the minimal polynomial of `frc` over ℚ (reusing the Eisenstein
irreducibility established in `InverseGaloisD4`). -/
theorem minpoly_frc : minpoly ℚ frc = X ^ 4 - C 2 :=
  (minpoly.eq_of_irreducible_of_monic
    InverseGaloisExtensions.x_fourth_sub_2_irreducible
    (by simp [frc_pow_four]) (monic_X_pow_sub_C _ (by norm_num))).symm

/-- `[ℚ(⁴√2) : ℚ] = 4`, for the complex fourth root. -/
theorem finrank_adjoin_frc : Module.finrank ℚ ℚ⟮frc⟯ = 4 := by
  rw [IntermediateField.adjoin.finrank frc_isIntegral, minpoly_frc,
    natDegree_X_pow_sub_C]

/-! ## Part II: The realness obstruction `I ∉ ℚ⟮frc⟯` -/

/-- **Every element of `ℚ⟮frc⟯` is real.**  The generator `frc` is real and ℚ
embeds in the reals, and `{z : z.im = 0}` is closed under the field operations,
so `adjoin_induction` propagates `im = 0` through all of `ℚ⟮frc⟯`. -/
theorem im_eq_zero_of_mem_adjoin {z : ℂ} (hz : z ∈ ℚ⟮frc⟯) : z.im = 0 := by
  induction hz using IntermediateField.adjoin_induction with
  | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx; exact frc_im
  | algebraMap x => simp
  | add x y _ _ ihx ihy => rw [Complex.add_im, ihx, ihy, add_zero]
  | inv x _ ihx => rw [Complex.inv_im, ihx, neg_zero, zero_div]
  | mul x y _ _ ihx ihy => rw [Complex.mul_im, ihx, ihy, mul_zero, zero_mul, add_zero]

/-- **The realness obstruction.**  `Complex.I ∉ ℚ⟮frc⟯`: it would have to be real,
but `Complex.I.im = 1 ≠ 0`.  This is exactly why the splitting field is strictly
larger than `ℚ(⁴√2)`. -/
theorem I_not_mem_adjoin_frc : Complex.I ∉ ℚ⟮frc⟯ := by
  intro h
  have := im_eq_zero_of_mem_adjoin h
  rw [Complex.I_im] at this
  exact one_ne_zero this

/-! ## Part III: Adjoining `i` — the degree-2 step -/

/-- `Complex.I` is integral over `ℚ⟮frc⟯` (it already is over ℚ, a root of
`X² + 1`). -/
theorem I_isIntegral : IsIntegral ℚ⟮frc⟯ Complex.I := by
  have hQ : IsIntegral ℚ Complex.I :=
    ⟨X ^ 2 + 1, monic_X2_add_1, by simp [Complex.I_sq]⟩
  exact hQ.tower_top

/-- `X² + 1` has no root in `ℚ⟮frc⟯`: a root `y` would give `(y : ℂ)² = −1` with
`y` real, impossible. -/
theorem no_root_X2_add_1 (y : ℚ⟮frc⟯) :
    ¬ IsRoot (X ^ 2 + 1 : ℚ⟮frc⟯[X]) y := by
  intro hy
  rw [IsRoot.def] at hy
  simp only [eval_add, eval_pow, eval_X, eval_one] at hy
  -- `y² = −1` in `ℚ⟮frc⟯`, hence in ℂ after embedding.
  have hy2 : y ^ 2 = -1 := by linear_combination hy
  have hyC : ((y : ℂ)) ^ 2 = -1 := by
    have h := congrArg (fun a : ℚ⟮frc⟯ => (a : ℂ)) hy2
    push_cast at h
    simpa using h
  -- `y` is real, so `(y:ℂ)` is the cast of a real number whose square is −1.
  have hyim : (y : ℂ).im = 0 := im_eq_zero_of_mem_adjoin y.2
  have hc : (y : ℂ) = (((y : ℂ).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hyim]
  rw [hc, ← Complex.ofReal_pow] at hyC
  have hre : ((y : ℂ).re) ^ 2 = -1 := by exact_mod_cast hyC
  nlinarith [sq_nonneg ((y : ℂ).re), hre]

/-- **`X² + 1` is the minimal polynomial of `i` over `ℚ⟮frc⟯`.** -/
theorem minpoly_I : minpoly ℚ⟮frc⟯ Complex.I = X ^ 2 + 1 := by
  have hd : (X ^ 2 + 1 : ℚ⟮frc⟯[X]).natDegree = 2 := by compute_degree!
  have hirr : Irreducible (X ^ 2 + 1 : ℚ⟮frc⟯[X]) := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · rw [Finset.mem_Icc]; omega
    · exact no_root_X2_add_1
  refine (minpoly.eq_of_irreducible_of_monic hirr ?_ ?_).symm
  · simp [Complex.I_sq]
  · exact monic_X2_add_1

/-- `[ℚ⟮frc⟯⟮i⟯ : ℚ⟮frc⟯] = 2`. -/
theorem finrank_step : Module.finrank ℚ⟮frc⟯ ℚ⟮frc⟯⟮Complex.I⟯ = 2 := by
  rw [IntermediateField.adjoin.finrank I_isIntegral, minpoly_I]
  compute_degree!

/-! ## Part IV: The splitting field has degree 8 -/

/-- **Main theorem: `[ℚ(⁴√2, i) : ℚ] = 8`.**  The concrete splitting field of
`X⁴ − 2` inside ℂ has degree 8 over ℚ, via the tower
`ℚ ⊂ ℚ(⁴√2) ⊂ ℚ(⁴√2, i)` with steps `4` and `2`.  This matches the abstract
`|Gal(X⁴−2/ℚ)| = 8` of `InverseGaloisD4.lean`. -/
theorem finrank_splitting_field : Module.finrank ℚ ℚ⟮frc, Complex.I⟯ = 8 := by
  haveI : FiniteDimensional ℚ ℚ⟮frc⟯ :=
    .of_finrank_pos (by rw [finrank_adjoin_frc]; norm_num)
  haveI : FiniteDimensional ↥ℚ⟮frc⟯ ℚ⟮frc⟯⟮Complex.I⟯ :=
    .of_finrank_pos (by rw [finrank_step]; norm_num)
  have htower := Module.finrank_mul_finrank ℚ ↥ℚ⟮frc⟯ ℚ⟮frc⟯⟮Complex.I⟯
  rw [finrank_adjoin_frc, finrank_step] at htower
  have e : ℚ⟮frc⟯⟮Complex.I⟯.restrictScalars ℚ = ℚ⟮frc, Complex.I⟯ :=
    IntermediateField.adjoin_simple_adjoin_simple ℚ frc Complex.I
  rw [← e]
  -- `restrictScalars` keeps the underlying ℚ-module, so the ℚ-finrank is unchanged.
  show Module.finrank ℚ ℚ⟮frc⟯⟮Complex.I⟯ = 8
  omega

end FourthRoot2SplittingFieldOQ01
