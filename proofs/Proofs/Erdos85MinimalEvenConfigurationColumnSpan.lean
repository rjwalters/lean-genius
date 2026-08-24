import Proofs.Erdos85MinimalEvenConfigurationRankFormula

/-!
# Column span of a minimal binary even configuration

The point-incidence columns of a binary circuit generate every even-weight
vector on its rows.  This turns circuit rank rigidity into a combinatorial
reconstruction interface: every even row subset is a symmetric difference
of point stars.
-/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- The transpose incidence range of a nonempty minimal binary even
configuration is exactly the even-weight hyperplane on its rows. -/
theorem minimal_even_configuration_transpose_range_eq_evenWeight
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    [DecidableEq α] [DecidableEq β]
    (Inc : α → β → Prop) [DecidableRel Inc]
    (heven : ∀ y : β,
      Even (((Finset.univ : Finset α).filter fun a => Inc a y).card))
    (hminimal : ∀ U : Finset α, U ⊂ Finset.univ → U.Nonempty →
      ¬ ∀ y : β, Even ((U.filter fun a => Inc a y).card)) :
    let M : Matrix β α (ZMod 2) := fun y a => if Inc a y then 1 else 0
    let total : (α → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun x => ∑ a, x a
        map_add' := by
          intro x z
          simp only [Pi.add_apply, Finset.sum_add_distrib]
        map_smul' := by
          intro c x
          simpa [Finset.mul_sum] }
    LinearMap.range M.transpose.mulVecLin = LinearMap.ker total := by
  classical
  dsimp only
  let M : Matrix β α (ZMod 2) := fun y a => if Inc a y then 1 else 0
  let total : (α → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun x => ∑ a, x a
      map_add' := by
        intro x z
        simp only [Pi.add_apply, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        simpa [Finset.mul_sum] }
  have hcol : ∀ y : β, ∑ a : α, M y a = 0 := by
    intro y
    have hcast :
        (((((Finset.univ : Finset α).filter fun a => Inc a y).card : ℕ) :
          ZMod 2)) = 0 :=
      ZMod.natCast_eq_zero_iff_even.mpr (heven y)
    simpa [M] using hcast
  have hle : LinearMap.range M.transpose.mulVecLin ≤ LinearMap.ker total := by
    intro x hx
    obtain ⟨z, rfl⟩ := hx
    rw [LinearMap.mem_ker]
    change ∑ a : α, M.transpose.mulVec z a = 0
    calc
      (∑ a : α, M.transpose.mulVec z a) =
          ∑ a : α, ∑ y : β, M y a * z y := by
            simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      _ = ∑ y : β, ∑ a : α, M y a * z y := Finset.sum_comm
      _ = ∑ y : β, (∑ a : α, M y a) * z y := by
            apply Finset.sum_congr rfl
            intro y _hy
            rw [Finset.sum_mul]
      _ = 0 := by simp [hcol]
  have hrank : M.rank + 1 = Fintype.card α := by
    simpa [Matrix.rank] using
      (minimal_even_configuration_incidenceRank_add_one_eq_card
        Inc heven hminimal)
  have hrange :
      Module.finrank (ZMod 2) (LinearMap.range M.transpose.mulVecLin) + 1 =
        Fintype.card α := by
    rw [← Matrix.rank, Matrix.rank_transpose, hrank]
  have htotal_surj : Function.Surjective total := by
    intro c
    let a₀ : α := Classical.choice inferInstance
    let x : α → ZMod 2 := fun a => if a = a₀ then c else 0
    refine ⟨x, ?_⟩
    change ∑ a : α, x a = c
    simp [x]
  have htotal_range : LinearMap.range total = ⊤ :=
    LinearMap.range_eq_top.mpr htotal_surj
  have hnull := LinearMap.finrank_range_add_finrank_ker total
  rw [htotal_range] at hnull
  have hkerRank :
      Module.finrank (ZMod 2) (LinearMap.ker total) + 1 =
        Fintype.card α := by
    simpa [Module.finrank_fintype_fun_eq_card, add_comm] using hnull
  apply Submodule.eq_of_le_of_finrank_eq hle
  omega

/-- Every even-weight binary row vector is a sum of point-incidence
columns.  For indicator vectors this says that every even row subset is a
symmetric difference of point stars. -/
theorem minimal_even_configuration_exists_pointCoefficients
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    [DecidableEq α] [DecidableEq β]
    (Inc : α → β → Prop) [DecidableRel Inc]
    (heven : ∀ y : β,
      Even (((Finset.univ : Finset α).filter fun a => Inc a y).card))
    (hminimal : ∀ U : Finset α, U ⊂ Finset.univ → U.Nonempty →
      ¬ ∀ y : β, Even ((U.filter fun a => Inc a y).card))
    (x : α → ZMod 2) (hx : ∑ a, x a = 0) :
    ∃ z : β → ZMod 2, ∀ a : α,
      x a = ∑ y : β, (if Inc a y then z y else 0) := by
  classical
  let M : Matrix β α (ZMod 2) := fun y a => if Inc a y then 1 else 0
  let total : (α → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun w => ∑ a, w a
      map_add' := by
        intro u v
        simp only [Pi.add_apply, Finset.sum_add_distrib]
      map_smul' := by
        intro c w
        simpa [Finset.mul_sum] }
  have hrange :=
    minimal_even_configuration_transpose_range_eq_evenWeight
      Inc heven hminimal
  change LinearMap.range M.transpose.mulVecLin = LinearMap.ker total at hrange
  have hxker : x ∈ LinearMap.ker total := by
    rw [LinearMap.mem_ker]
    exact hx
  rw [← hrange] at hxker
  obtain ⟨z, hz⟩ := hxker
  refine ⟨z, fun a => ?_⟩
  have ha := congrFun hz a
  simpa [M, Matrix.vecMul, dotProduct, ite_mul, one_mul, zero_mul] using ha.symm

end

end Erdos85

#print axioms
  Erdos85.minimal_even_configuration_transpose_range_eq_evenWeight
#print axioms
  Erdos85.minimal_even_configuration_exists_pointCoefficients
