import Proofs.Erdos85ThreeHighOrbitRows
import Proofs.Erdos85ThreeHighJointRelabeling
import Proofs.Erdos85ExternalBlockCapRelabeling

namespace Erdos85
attribute [local irreducible] threeHighCrossDomain

/-- Any U relabeling that permutes the three canonical blocks transports
the same completion and joint families, while keeping R fixed. -/
theorem threeHighBlockPermutation_joint_transport
    (U V : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (e : Equiv.Perm (Fin 15)) (σ : Equiv.Perm (Fin 3))
    (hrows : ∀ k, (threeHighCanonicalRow k).image (threeHighEmptyURelabel e) =
      threeHighCanonicalRow (σ k))
    (hUV : ∀ x y, U x y = V (e x) (e y))
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (hExt : encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true)
    (hJoint : ThreeHighJointWitness (threeHighEmptyAdj U R cross)) :
    ∃ cross' : ThreeHighCross, cross' ∈ threeHighCrossDomain V R ∧
      encodedExternalBlockCap (threeHighEmptyAdj V R cross') threeHighCanonicalRow = true ∧
      ThreeHighJointWitness (threeHighEmptyAdj V R cross') := by
  let E := threeHighEmptyURelabel e
  let cross' : ThreeHighCross := fun x j => cross (e.symm x) j
  have hU : (fun x y => U (e.symm x) (e.symm y)) = V := by
    funext x y
    simp only [hUV,Equiv.apply_symm_apply]
  have hAdj : threeHighEmptyAdj V R cross' =
      fun x y => threeHighEmptyAdj U R cross (E.symm x) (E.symm y) := by
    funext x y
    change threeHighEmptyAdj V R (fun x j => cross (e.symm x) j) x y = _
    rw [← hU,threeHighEmptyAdj_relabel_U,threeHighEmptyURelabel_symm]
  have hroot : E 23 = 23 := threeHighEmptyURelabel_root e
  refine ⟨cross',?_,?_,?_⟩
  · have h := threeHighCrossDomain_relabel_U U R cross e.symm hc
    rw [hU] at h
    exact h
  · have h := (encodedExternalBlockCap_relabel (threeHighEmptyAdj U R cross)
      threeHighCanonicalRow E).trans hExt
    have hr : (fun k => (threeHighCanonicalRow k).image E) =
        fun k => threeHighCanonicalRow (σ k) := funext hrows
    rw [hr,encodedExternalBlockCap_reindex,← hAdj] at h
    exact h
  · have h := hJoint.relabel (threeHighEmptyAdj U R cross) E σ hroot hrows
    rw [← hAdj] at h
    exact h

end Erdos85
#print axioms Erdos85.threeHighBlockPermutation_joint_transport
