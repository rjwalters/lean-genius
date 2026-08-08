import Proofs.Erdos85PrimeFourierSquare

/-!
# The order-three Fourier norm bridge

At a primitive cube root, a negation-symmetric integral Fourier coefficient
is the integer `c 0 - c 1`.  Hence a square-frequency identity
`H² = u² d` forces `H = 0` whenever the natural parameter `d` is nonsquare.
-/

namespace Erdos85

open scoped BigOperators

noncomputable section

theorem orderThree_symmetric_fourier_eq_int
    {K : Type*} [Field K] [CharZero K]
    {η : K} (hη : IsPrimitiveRoot η 3)
    (c : ZMod 3 → ℤ) (hsymm : ∀ y, c (-y) = c y) :
    (∑ y : ZMod 3, (c y : K) * primitiveRootCharacter hη y) =
      ((c 0 - c 1 : ℤ) : K) := by
  have hsum : 1 + η + η ^ 2 = 0 := by
    simpa [Finset.sum_range_succ] using
      hη.geom_sum_eq_zero (by norm_num : 1 < 3)
  have hc2 : c 2 = c 1 := by
    have h := hsymm (1 : ZMod 3)
    norm_num at h ⊢
    exact h
  calc
    (∑ y : ZMod 3, (c y : K) * primitiveRootCharacter hη y) =
        ∑ i : Fin 3, (c (ZMod.finEquiv 3 i) : K) * η ^ i.val := by
          refine Fintype.sum_equiv (ZMod.finEquiv 3).symm _ _ ?_
          intro i
          have hi := (ZMod.finEquiv 3).apply_symm_apply i
          have hval : ((ZMod.finEquiv 3).symm i).val = i.val := by
            exact congrArg ZMod.val hi
          change (c i : K) * primitiveRootCharacter hη i =
            (c ((ZMod.finEquiv 3) ((ZMod.finEquiv 3).symm i)) : K) *
              η ^ ((ZMod.finEquiv 3).symm i).val
          rw [hi, primitiveRootCharacter_eq_pow_val, hval]
    _ = (c 0 : K) + (c 1 : K) * η + (c 2 : K) * η ^ 2 := by
          norm_num [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ,
            hη.ne_zero (by norm_num)]
          apply congrArg c
          decide
    _ = ((c 0 - c 1 : ℤ) : K) := by
          rw [hc2]
          push_cast
          linear_combination (c 1 : K) * hsum

theorem orderThree_fourier_eq_zero_of_square_identity
    {η : ℂ} (hη : IsPrimitiveRoot η 3)
    (c : ZMod 3 → ℤ) (hsymm : ∀ y, c (-y) = c y)
    (d : ℕ) (hnonsquare : ¬ IsSquare d) (u : ℤ)
    (hsq :
      (∑ y : ZMod 3, (c y : ℂ) * primitiveRootCharacter hη y) *
          (∑ y : ZMod 3, (c y : ℂ) * primitiveRootCharacter hη y) =
        ((u * u : ℤ) : ℂ) * (d : ℂ)) :
    ∑ y : ZMod 3, (c y : ℂ) * primitiveRootCharacter hη y = 0 := by
  let H : ℂ := ∑ y : ZMod 3,
    (c y : ℂ) * primitiveRootCharacter hη y
  let A : ℤ := c 0 - c 1
  have hH : H = (A : ℂ) := by
    simpa only [H, A] using orderThree_symmetric_fourier_eq_int hη c hsymm
  have hsqQ : ((A : ℚ) ^ 2) = ((u : ℚ) ^ 2) * d := by
    have hsqC : ((A : ℂ) ^ 2) = ((u : ℂ) ^ 2) * (d : ℂ) := by
      rw [← hH]
      convert hsq using 1 <;> push_cast <;> ring
    exact_mod_cast hsqC
  have huQ : (u : ℚ) = 0 := by
    by_contra hu
    apply hnonsquare
    rw [← Rat.isSquare_natCast_iff]
    refine ⟨(A : ℚ) / (u : ℚ), ?_⟩
    rw [div_mul_div_comm]
    field_simp [hu]
    nlinarith [hsqQ]
  have hu : u = 0 := by exact_mod_cast huQ
  rw [hu] at hsq
  have hHzero : H * H = 0 := by
    dsimp only [H]
    calc
      (∑ y : ZMod 3, (c y : ℂ) * primitiveRootCharacter hη y) *
          (∑ y : ZMod 3, (c y : ℂ) * primitiveRootCharacter hη y) =
          (((0 : ℤ) * 0 : ℤ) : ℂ) * (d : ℂ) := hsq
      _ = 0 := by norm_num
  exact mul_self_eq_zero.mp hHzero

end

end Erdos85
