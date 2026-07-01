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

/-! ## Part V: The explicit roots and the factorization of `X⁴ − 2` over `K`

The degree-8 result above pins down the *size* of the splitting field.  This part
supplies the missing *structural* content: the four roots of `X⁴ − 2` in ℂ are

  `⁴√2,  i·⁴√2,  −⁴√2,  −i·⁴√2`,

all four of which live in `K = ℚ⟮frc, Complex.I⟯`, so `X⁴ − 2` factors into linear
factors over `K` and hence **splits** over `K`.  This is precisely the ingredient
`inverse-galois-d4` obtains only abstractly (inside `(X⁴−2).SplittingField`); here it
is a concrete factorization inside the subfield `K ⊆ ℂ`. -/

/-- The concrete splitting field `K = ℚ(⁴√2, i) ⊆ ℂ`. -/
noncomputable abbrev SF : IntermediateField ℚ ℂ := ℚ⟮frc, Complex.I⟯

/-- `frc = ⁴√2 ∈ K`. -/
theorem frc_mem_SF : frc ∈ SF := IntermediateField.subset_adjoin ℚ _ (by simp)

/-- `i ∈ K`. -/
theorem I_mem_SF : Complex.I ∈ SF := IntermediateField.subset_adjoin ℚ _ (by simp)

/-- `⁴√2` as an element of the field `K`. -/
noncomputable def rt : SF := ⟨frc, frc_mem_SF⟩

/-- `i` as an element of the field `K`. -/
noncomputable def im_i : SF := ⟨Complex.I, I_mem_SF⟩

@[simp] theorem coe_rt : ((rt : SF) : ℂ) = frc := rfl
@[simp] theorem coe_im_i : ((im_i : SF) : ℂ) = Complex.I := rfl

/-- In `K`, `(⁴√2)⁴ = 2`. -/
theorem rt_pow_four : rt ^ 4 = 2 := by
  apply_fun (Subtype.val : SF → ℂ) using Subtype.val_injective
  push_cast
  exact frc_pow_four

/-- In `K`, `i² = −1`. -/
theorem im_i_sq : im_i ^ 2 = -1 := by
  apply_fun (Subtype.val : SF → ℂ) using Subtype.val_injective
  push_cast
  exact Complex.I_sq

/-- **Factorization of `X⁴ − 2` over `K`.**  With `α = ⁴√2` and `i` the imaginary
unit (both in `K`), `X⁴ − 2 = (X − α)(X + α)(X − iα)(X + iα)`. -/
theorem X4_sub_2_factor :
    (X ^ 4 - C 2 : SF[X])
      = (X - C rt) * (X - C (-rt)) * (X - C (im_i * rt)) * (X - C (-(im_i * rt))) := by
  have h4 : rt ^ 4 = 2 := rt_pow_four
  have h2 : im_i ^ 2 = -1 := im_i_sq
  have e1 : (X - C rt) * (X - C (-rt)) = X ^ 2 - C (rt ^ 2) := by
    rw [map_neg, map_pow]; ring
  have e2 : (X - C (im_i * rt)) * (X - C (-(im_i * rt))) = X ^ 2 + C (rt ^ 2) := by
    have hsq : C (im_i * rt) ^ 2 = - C (rt ^ 2) := by
      rw [← map_pow, mul_pow, h2, neg_one_mul, map_neg]
    rw [map_neg,
      show (X - C (im_i * rt)) * (X - -(C (im_i * rt))) = X ^ 2 - C (im_i * rt) ^ 2 from by ring,
      hsq]
    ring
  have e3 : (X ^ 2 - C (rt ^ 2)) * (X ^ 2 + C (rt ^ 2)) = X ^ 4 - C 2 := by
    have hc : C (rt ^ 2) ^ 2 = C 2 := by
      rw [← map_pow, show (rt ^ 2) ^ 2 = rt ^ 4 from by ring, h4]
    rw [show (X ^ 2 - C (rt ^ 2)) * (X ^ 2 + C (rt ^ 2)) = X ^ 4 - C (rt ^ 2) ^ 2 from by ring, hc]
  calc (X ^ 4 - C 2 : SF[X])
      = (X ^ 2 - C (rt ^ 2)) * (X ^ 2 + C (rt ^ 2)) := e3.symm
    _ = ((X - C rt) * (X - C (-rt))) * ((X - C (im_i * rt)) * (X - C (-(im_i * rt)))) := by
        rw [e1, e2]
    _ = (X - C rt) * (X - C (-rt)) * (X - C (im_i * rt)) * (X - C (-(im_i * rt))) := by ring

/-- **`X⁴ − 2` splits over the concrete splitting field `K = ℚ(⁴√2, i)`.**  All four
roots lie in `K`, so the polynomial factors into linear factors there.  This upgrades
the degree-8 statement to the genuine splitting property. -/
theorem X4_sub_2_splits : Splits (X ^ 4 - C 2 : SF[X]) := by
  rw [X4_sub_2_factor]
  exact ((((Splits.X_sub_C rt).mul (Splits.X_sub_C (-rt))).mul
    (Splits.X_sub_C (im_i * rt))).mul (Splits.X_sub_C (-(im_i * rt))))

/-- The `ℚ`-polynomial `X⁴ − 2`, mapped into `K = ℚ(⁴√2, i)`, splits — the form of the
splitting statement matching `Polynomial.IsSplittingField`. -/
theorem X4_sub_2_splits_map :
    Splits ((X ^ 4 - C 2 : ℚ[X]).map (algebraMap ℚ SF)) := by
  have hmap : (X ^ 4 - C 2 : ℚ[X]).map (algebraMap ℚ SF) = (X ^ 4 - C 2 : SF[X]) := by
    simp
  rw [hmap]; exact X4_sub_2_splits

/-- **Exactly two of the four roots are non-real.**  The roots `±⁴√2` are real, while
`±i·⁴√2` have imaginary part `±⁴√2 ≠ 0` — this is *why* the splitting field must
extend the real field `ℚ(⁴√2)` by adjoining `i`. -/
theorem two_roots_nonreal :
    (Complex.I * frc).im ≠ 0 ∧ (-(Complex.I * frc)).im ≠ 0 := by
  have hpos : (0 : ℝ) < Real.sqrt (Real.sqrt 2) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
  have him : (Complex.I * frc).im = Real.sqrt (Real.sqrt 2) := by
    simp [Complex.mul_im, frc]
  refine ⟨?_, ?_⟩
  · rw [him]; exact hpos.ne'
  · rw [Complex.neg_im, him]; exact neg_ne_zero.mpr hpos.ne'

/-! ## Part VI: `K` is a splitting field of `X⁴ − 2`

Combining the splitting property (Part V) with the fact that the roots *generate* `K`,
`K = ℚ(⁴√2, i)` is a `Polynomial.IsSplittingField` of `X⁴ − 2` over `ℚ` — the full
structural characterization, matching the abstract `(X⁴−2).SplittingField`. -/

/-- The two generators `⁴√2, i` of `K` generate the whole field: `ℚ⟮⁴√2, i⟯ = ⊤`
(inside `K` itself). -/
theorem adjoin_gens_eq_top : IntermediateField.adjoin ℚ {rt, im_i} = ⊤ := by
  apply IntermediateField.lift_injective SF
  rw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
  rw [Set.image_pair, coe_rt, coe_im_i]

/-- `⁴√2 ≠ 0` inside `K`. -/
theorem rt_ne_zero : rt ≠ 0 := by
  intro h
  have h0 : frc = 0 := by rw [← coe_rt, h]; simp
  rw [frc, Complex.ofReal_eq_zero] at h0
  exact (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by norm_num))).ne' h0

/-- **`K = ℚ(⁴√2, i)` is a splitting field of `X⁴ − 2` over `ℚ`.**  This is the full
structural statement underlying the degree-8 count and the `D₄` Galois picture: the
polynomial both splits over `K` (Part V) and its roots generate `K`. -/
theorem X4_sub_2_isSplittingField :
    (X ^ 4 - C 2 : ℚ[X]).IsSplittingField ℚ SF := by
  have hp0 : (X ^ 4 - C 2 : ℚ[X]) ≠ 0 :=
    (monic_X_pow_sub_C (2 : ℚ) (show (4 : ℕ) ≠ 0 by norm_num)).ne_zero
  -- `⁴√2` and `i·⁴√2` are roots living in `K`.
  have hrt : rt ∈ (X ^ 4 - C 2 : ℚ[X]).rootSet SF := by
    rw [Polynomial.mem_rootSet]
    refine ⟨hp0, ?_⟩
    rw [map_sub, map_pow, aeval_X, aeval_C, rt_pow_four]; simp
  have himrt : im_i * rt ∈ (X ^ 4 - C 2 : ℚ[X]).rootSet SF := by
    rw [Polynomial.mem_rootSet]
    refine ⟨hp0, ?_⟩
    have hpow : (im_i * rt) ^ 4 = 2 := by
      have h4 : im_i ^ 4 = 1 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, im_i_sq]; norm_num
      rw [mul_pow, h4, rt_pow_four, one_mul]
    rw [map_sub, map_pow, aeval_X, aeval_C, hpow]; simp
  rw [isSplittingField_iff_intermediateField]
  refine ⟨X4_sub_2_splits_map, ?_⟩
  -- The roots generate `K`: from `⁴√2` and `i·⁴√2` we recover `i = (i·⁴√2)·(⁴√2)⁻¹`.
  set R := (X ^ 4 - C 2 : ℚ[X]).rootSet SF with hR
  have h1 : rt ∈ IntermediateField.adjoin ℚ R := IntermediateField.subset_adjoin ℚ R hrt
  have h2 : im_i * rt ∈ IntermediateField.adjoin ℚ R := IntermediateField.subset_adjoin ℚ R himrt
  have him : im_i ∈ IntermediateField.adjoin ℚ R := by
    rw [← mul_inv_cancel_right₀ rt_ne_zero im_i]
    exact mul_mem h2 (inv_mem h1)
  refine top_le_iff.mp ?_
  rw [← adjoin_gens_eq_top]
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact h1
  · exact him

end FourthRoot2SplittingFieldOQ01
