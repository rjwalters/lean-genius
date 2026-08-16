import Proofs.Erdos85FinFourPredicateCanonicalization
import Mathlib.Tactic

/-! # Pair and endpoint coordinates on eight standard-matched points -/

namespace Erdos85

/-- Split a standard root label into its mate-pair index and endpoint bit. -/
def finEightPairCoordinates : Fin 8 ≃ Fin 4 × Fin 2 where
  toFun i := (⟨i.val / 2, by omega⟩, ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩)
  invFun x := ⟨2 * x.1.val + x.2.val, by omega⟩
  left_inv i := by
    apply Fin.ext
    dsimp
    omega
  right_inv x := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega

@[simp] theorem finEightPairCoordinates_symm_val (p : Fin 4) (b : Fin 2) :
    (finEightPairCoordinates.symm (p, b)).val = 2 * p.val + b.val := rfl

def finTwoSwap : Equiv.Perm (Fin 2) := Equiv.swap 0 1

@[simp] theorem finTwoSwap_apply (i : Fin 2) :
    finTwoSwap i = ⟨1 - i.val, by omega⟩ := by
  fin_cases i <;> rfl

/-- Permute the four mate pairs and independently choose whether to flip the
two endpoints of each original pair. -/
def finFourPairEndpointPerm
    (σ : Equiv.Perm (Fin 4)) (flip : Fin 4 → Bool) :
    Equiv.Perm (Fin 4 × Fin 2) where
  toFun x := (σ x.1, if flip x.1 then finTwoSwap x.2 else x.2)
  invFun y :=
    let p := σ.symm y.1
    (p, if flip p then finTwoSwap y.2 else y.2)
  left_inv x := by
    rcases x with ⟨p, b⟩
    dsimp
    by_cases h : flip p = true
    · simp only [h, if_true, Equiv.symm_apply_apply]
      fin_cases b <;> rfl
    · have hf : flip p = false := Bool.eq_false_of_not_eq_true h
      simp [hf]
  right_inv y := by
    rcases y with ⟨p, b⟩
    dsimp
    by_cases h : flip (σ.symm p) = true
    · simp only [h, if_true, Equiv.apply_symm_apply]
      fin_cases b <;> rfl
    · have hf : flip (σ.symm p) = false := Bool.eq_false_of_not_eq_true h
      simp [hf]

/-- Lift pair permutation and endpoint flips back to the canonical `Fin 8`. -/
def finEightLiftPairPerm
    (σ : Equiv.Perm (Fin 4)) (flip : Fin 4 → Bool) :
    Equiv.Perm (Fin 8) :=
  finEightPairCoordinates.trans
    ((finFourPairEndpointPerm σ flip).trans finEightPairCoordinates.symm)

@[simp] theorem finEightPairCoordinates_liftPairPerm_symm
    (σ : Equiv.Perm (Fin 4)) (flip : Fin 4 → Bool) (i : Fin 8) :
    finEightPairCoordinates ((finEightLiftPairPerm σ flip).symm i) =
      let p := σ.symm (finEightPairCoordinates i).1
      (p, if flip p then finTwoSwap (finEightPairCoordinates i).2
        else (finEightPairCoordinates i).2) := by
  simp [finEightLiftPairPerm, finFourPairEndpointPerm]

end Erdos85
