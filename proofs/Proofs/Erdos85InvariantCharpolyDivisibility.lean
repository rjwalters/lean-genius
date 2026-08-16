import Proofs.Erdos85InvariantDecomposition
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Characteristic divisibility for an invariant subspace

An invariant subspace gives an upper-triangular block after extending a basis,
so the characteristic polynomial of the restriction divides the ambient one.
-/

namespace Erdos85

noncomputable section

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

theorem charpoly_restrict_dvd_of_invariant
    (T : E →ₗ[K] E) (U : Submodule K E)
    (hU : ∀ x ∈ U, T x ∈ U) :
    (T.restrict hU).charpoly ∣ T.charpoly := by
  classical
  let bU := Module.Free.chooseBasis K U
  let v : Module.Free.ChooseBasisIndex K U → E := fun i => (bU i : E)
  have hv : LinearIndependent K v := by
    exact bU.linearIndependent.map' U.subtype U.ker_subtype
  let b := Module.Basis.sumExtend hv
  let J := Module.Basis.sumExtendIndex hv
  letI : Finite (Module.Free.ChooseBasisIndex K U ⊕ J) :=
    Module.Finite.finite_basis b
  letI : Finite J := @Finite.of_injective J
    (Module.Free.ChooseBasisIndex K U ⊕ J) _ Sum.inr Sum.inr_injective
  letI : Fintype J := Fintype.ofFinite J
  have hb_inl (i : Module.Free.ChooseBasisIndex K U) :
      b (Sum.inl i) = v i := by
    unfold b Module.Basis.sumExtend
    rw [Module.Basis.reindex_apply, Module.Basis.extend_apply_self]
    rfl
  have hrepr_basis (i : Module.Free.ChooseBasisIndex K U) :
      b.repr (bU i : E) = Finsupp.single (Sum.inl i) 1 := by
    change b.repr (v i) = Finsupp.single (Sum.inl i) 1
    rw [← hb_inl i]
    exact b.repr_self (Sum.inl i)
  have hrepr_inr (u : U) (i : J) :
      b.repr (u : E) (Sum.inr i) = 0 := by
    rw [← bU.sum_repr u]
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
    simp [hrepr_basis]
  have hrepr_inl (u : U) (i : Module.Free.ChooseBasisIndex K U) :
      b.repr (u : E) (Sum.inl i) = bU.repr u i := by
    rw [← bU.sum_repr u]
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
    simp_rw [hrepr_basis]
    have hterm : ∀ c : Module.Free.ChooseBasisIndex K U,
        (Finsupp.single (Sum.inl c :
          Module.Free.ChooseBasisIndex K U ⊕ J) (bU.repr u c))
            (Sum.inl i) =
          if c = i then bU.repr u c else 0 := by
      intro c
      by_cases hci : c = i <;> simp [hci]
    simp [hterm]
  let M := LinearMap.toMatrix b b T
  let A := LinearMap.toMatrix bU bU (T.restrict hU)
  let B : Matrix (Module.Free.ChooseBasisIndex K U) J K :=
    fun i j => M (Sum.inl i) (Sum.inr j)
  let C : Matrix J (Module.Free.ChooseBasisIndex K U) K :=
    fun i j => M (Sum.inr i) (Sum.inl j)
  let D : Matrix J J K :=
    fun i j => M (Sum.inr i) (Sum.inr j)
  have hC : C = 0 := by
    ext i j
    simp only [C, M, LinearMap.toMatrix_apply]
    change b.repr (T (b (Sum.inl j))) (Sum.inr i) = 0
    rw [hb_inl]
    exact hrepr_inr ⟨T (bU j), hU (bU j) (bU j).2⟩ i
  have hA : (fun i j => M (Sum.inl i) (Sum.inl j)) = A := by
    ext i j
    simp only [M, A, LinearMap.toMatrix_apply]
    change b.repr (T (b (Sum.inl j))) (Sum.inl i) =
      bU.repr ((T.restrict hU) (bU j)) i
    rw [hb_inl]
    exact hrepr_inl ⟨T (bU j), hU (bU j) (bU j).2⟩ i
  have hblocks : M = Matrix.fromBlocks A B C D := by
    ext i j
    cases i with
    | inl i =>
        cases j with
        | inl j => exact congrFun (congrFun hA i) j
        | inr j => rfl
    | inr i =>
        cases j <;> rfl
  have hfactor : M.charpoly = A.charpoly * D.charpoly := by
    rw [hblocks, hC]
    exact Matrix.charpoly_fromBlocks_zero₂₁
      (M₁₁ := A) (M₁₂ := B) (M₂₂ := D)
  rw [← LinearMap.charpoly_toMatrix T b,
    ← LinearMap.charpoly_toMatrix (T.restrict hU) bU]
  rw [hfactor]
  exact dvd_mul_right _ _

end

end Erdos85
