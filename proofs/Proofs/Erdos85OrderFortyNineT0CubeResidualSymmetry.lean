import Proofs.Erdos85OrderFortyNineSevenHighT0CubeCnf

/-!
# Residual symmetry of the six nonzero `h = 7, t = 0` cubes

After the rooted pair `7--15` is fixed, the remaining three matching edges
`16--17`, `18--19`, and `20--21` may be permuted and flipped.  This action is
transitive on `16, ..., 21`, so all selector cubes `1, ..., 6` are equivalent.
-/

namespace Erdos85

/-- An involutive matching automorphism fixing index zero and sending index
one to `cube` whenever `cube` is nonzero. -/
def sevenHighT0ResidualIndexPerm (cube : Fin 7) : Fin 7 ≃ Fin 7 :=
  if cube = 2 then Equiv.swap 1 2
  else if cube = 3 then (Equiv.swap 1 3).trans (Equiv.swap 2 4)
  else if cube = 4 then (Equiv.swap 1 4).trans (Equiv.swap 2 3)
  else if cube = 5 then (Equiv.swap 1 5).trans (Equiv.swap 2 6)
  else if cube = 6 then (Equiv.swap 1 6).trans (Equiv.swap 2 5)
  else Equiv.refl _

theorem sevenHighT0ResidualIndexPerm_zero (cube : Fin 7) :
    sevenHighT0ResidualIndexPerm cube 0 = 0 := by
  revert cube
  native_decide

theorem sevenHighT0ResidualIndexPerm_one
    (cube : Fin 7) (hcube : cube ≠ 0) :
    sevenHighT0ResidualIndexPerm cube 1 = cube := by
  revert cube
  native_decide

theorem sevenHighT0ResidualIndexPerm_involutive_pointwise :
    ∀ cube index : Fin 7,
      sevenHighT0ResidualIndexPerm cube
          (sevenHighT0ResidualIndexPerm cube index) = index := by
  native_decide

theorem sevenHighT0ResidualIndexPerm_involutive (cube : Fin 7) :
    Function.Involutive (sevenHighT0ResidualIndexPerm cube) := by
  exact sevenHighT0ResidualIndexPerm_involutive_pointwise cube

theorem sevenHighT0ResidualIndexPerm_eq_cube_iff
    (cube index : Fin 7) (hcube : cube ≠ 0) :
    sevenHighT0ResidualIndexPerm cube index = cube ↔ index = 1 := by
  revert cube index
  native_decide

/-- Lift the residual action to all 49 vertices, acting only on `15..21`. -/
def sevenHighT0ResidualVertexMap (cube : Fin 7) (v : Fin 49) : Fin 49 :=
  if hv : 15 ≤ v.val ∧ v.val < 22 then
    ⟨(sevenHighT0ResidualIndexPerm cube
      ⟨v.val - 15, by omega⟩).val + 15, by omega⟩
  else v

theorem sevenHighT0ResidualVertexMap_involutive_pointwise :
    ∀ cube : Fin 7, ∀ v : Fin 49,
      sevenHighT0ResidualVertexMap cube
          (sevenHighT0ResidualVertexMap cube v) = v := by
  native_decide

theorem sevenHighT0ResidualVertexMap_involutive (cube : Fin 7) :
    Function.Involutive (sevenHighT0ResidualVertexMap cube) := by
  exact sevenHighT0ResidualVertexMap_involutive_pointwise cube

def sevenHighT0ResidualVertexPerm (cube : Fin 7) : Fin 49 ≃ Fin 49 :=
  { toFun := sevenHighT0ResidualVertexMap cube
    invFun := sevenHighT0ResidualVertexMap cube
    left_inv := sevenHighT0ResidualVertexMap_involutive cube
    right_inv := sevenHighT0ResidualVertexMap_involutive cube }

theorem sevenHighT0ResidualVertexPerm_apply_index
    (cube index : Fin 7) :
    sevenHighT0ResidualVertexPerm cube
      ⟨index.val + 15, by omega⟩ =
      ⟨(sevenHighT0ResidualIndexPerm cube index).val + 15, by omega⟩ := by
  fin_cases cube <;> fin_cases index <;> native_decide

theorem sevenHighT0ResidualVertexPerm_fix_outside
    (cube : Fin 7) (v : Fin 49)
    (hv : v.val < 15 ∨ 22 ≤ v.val) :
    sevenHighT0ResidualVertexPerm cube v = v := by
  change sevenHighT0ResidualVertexMap cube v = v
  simp only [sevenHighT0ResidualVertexMap]
  split <;> rename_i h
  · omega
  · rfl

theorem sevenHighT0ResidualIndexPerm_preserves_matching1 :
    ∀ cube a b : Fin 7,
      sevenHighT0CubeMatching1
          (min (a.val + 15) (b.val + 15))
          (max (a.val + 15) (b.val + 15)) =
        sevenHighT0CubeMatching1
          (min ((sevenHighT0ResidualIndexPerm cube a).val + 15)
            ((sevenHighT0ResidualIndexPerm cube b).val + 15))
          (max ((sevenHighT0ResidualIndexPerm cube a).val + 15)
            ((sevenHighT0ResidualIndexPerm cube b).val + 15)) := by
  native_decide

theorem sevenHighT0ResidualVertexPerm_selector
    (cube index : Fin 7) (hcube : cube ≠ 0) :
    sevenHighT0ResidualVertexPerm cube
      ⟨index.val + 15, by omega⟩ =
        ⟨cube.val + 15, by omega⟩ ↔ index = 1 := by
  revert cube index
  native_decide

end Erdos85
