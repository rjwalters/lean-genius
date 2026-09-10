import Proofs.Erdos85ThreeHighOrbitRows
import Proofs.Erdos85ThreeHighJointRelabeling
import Proofs.Erdos85ExternalBlockCapRelabeling

namespace Erdos85
attribute [local irreducible] threeHighCrossDomain

/-- Move the same admissible completion and its three families to an orbit
representative. R is fixed; external block caps and the full joint witness survive. -/
theorem threeHighOrbit_joint_transport
    (U V : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (p : Fin 120) (sw : Bool)
    (hUV : ∀ x y, U x y = V (threeBlockOrbitLabel p sw x) (threeBlockOrbitLabel p sw y))
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (hExt : encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true)
    (hJoint : ThreeHighJointWitness (threeHighEmptyAdj U R cross)) :
    ∃ cross' : ThreeHighCross, cross' ∈ threeHighCrossDomain V R ∧
      encodedExternalBlockCap (threeHighEmptyAdj V R cross') threeHighCanonicalRow = true ∧
      ThreeHighJointWitness (threeHighEmptyAdj V R cross') := by
  let e := threeBlockOrbitLabel p sw
  let E := threeHighEmptyURelabel e
  let σ : Equiv.Perm (Fin 3) := if sw then Equiv.swap 1 2 else Equiv.refl (Fin 3)
  let cross' : ThreeHighCross := fun x j => cross (e.symm x) j
  have hU : (fun x y => U (e.symm x) (e.symm y)) = V := by
    funext x y
    simp only [hUV,e,Equiv.apply_symm_apply]
  have hAdj : threeHighEmptyAdj V R cross' =
      fun x y => threeHighEmptyAdj U R cross (E.symm x) (E.symm y) := by
    funext x y
    change threeHighEmptyAdj V R (fun x j => cross (e.symm x) j) x y = _
    rw [← hU,threeHighEmptyAdj_relabel_U,threeHighEmptyURelabel_symm]
  have hrows (k : Fin 3) : (threeHighCanonicalRow k).image E = threeHighCanonicalRow (σ k) :=
    threeHighOrbitLabel_rows p sw k
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
#print axioms Erdos85.threeHighOrbit_joint_transport
