import Mathlib

/-! # Characteristic factors from independent eigenfamilies -/

open Matrix Polynomial

namespace Erdos85

noncomputable section

/-- A linearly independent `k`-element `mu`-eigenfamily forces the `k`th
power of the corresponding linear factor in the characteristic polynomial. -/
theorem matrix_charpoly_linearFactor_pow_dvd_of_eigenfamily
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℂ) (mu : ℂ) (k : ℕ)
    (f : Fin k → V → ℂ)
    (heigen : ∀ i, A.mulVec (f i) = mu • f i)
    (hli : LinearIndependent ℂ f) :
    (X - C mu) ^ k ∣ A.charpoly := by
  let T : Module.End ℂ (V → ℂ) := A.toLin'
  let fe : Fin k → T.eigenspace mu := fun i ↦ ⟨f i,
    Module.End.mem_eigenspace_iff.mpr (by
      simpa [T, Matrix.toLin'_apply] using heigen i)⟩
  have hlie : LinearIndependent ℂ fe := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    apply (Fintype.linearIndependent_iff.mp hli) g
    simpa [fe] using congrArg Subtype.val hg
  have hgeom : k ≤ Module.finrank ℂ (T.eigenspace mu) := by
    simpa using hlie.fintype_card_le_finrank
  have hmult : k ≤ T.charpoly.rootMultiplicity mu :=
    hgeom.trans (LinearMap.finrank_eigenspace_le T mu)
  have hpow : (X - C mu) ^ k ∣
      (X - C mu) ^ T.charpoly.rootMultiplicity mu :=
    pow_dvd_pow _ hmult
  have hroot : (X - C mu) ^ T.charpoly.rootMultiplicity mu ∣
      T.charpoly := T.charpoly.pow_rootMultiplicity_dvd mu
  have hdvd := hpow.trans hroot
  rwa [Matrix.charpoly_toLin'] at hdvd

end

end Erdos85

#print axioms Erdos85.matrix_charpoly_linearFactor_pow_dvd_of_eigenfamily
