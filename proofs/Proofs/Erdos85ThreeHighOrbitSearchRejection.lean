import Proofs.Erdos85ThreeHighOrbitJointTransport
import Proofs.Erdos85ThreeHighOrbitRejection
import Proofs.Erdos85ThreeHighExternalSearchCertificate

namespace Erdos85
attribute [local irreducible] threeHighCrossDomain

/-- Representative search rejections exclude a source joint completion whenever
its checked orbit certificate and the two search soundness proofs are supplied. -/
theorem ThreeBlockOrbitCertificate.no_joint_of_search {n : Nat}
    (U : Fin 15 → Fin 15 → Bool) (reps : Fin n → Fin 15 → Fin 15 → Bool)
    (cert : ThreeBlockOrbitCertificate n) (hcert : cert.Valid U reps)
    (R : Fin 8 → Fin 8 → Bool)
    (search : ThreeHighExternalSearch) (hsearch : ThreeHighExternalSearchSound search)
    (accept : (Fin 24 → Fin 24 → Bool) → Bool) (hsound : ThreeHighTerminalSound accept)
    (hreject : ∀ i, search (reps i) R
      (fun cross => accept (threeHighEmptyAdj (reps i) R cross)) = false)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (hExt : encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true)
    (hJoint : ThreeHighJointWitness (threeHighEmptyAdj U R cross)) : False := by
  obtain ⟨i,p,sw,hU⟩ := cert.covered U reps hcert (threeHighCrossDomain_U_c4 U R cross hc)
  obtain ⟨cross',hc',hExt',hJoint'⟩ :=
    threeHighOrbit_joint_transport U (reps i) R p sw hU cross hc hExt hJoint
  have h := hsearch (reps i) R (fun c => accept (threeHighEmptyAdj (reps i) R c))
    cross' hc' hExt' (hsound _ hJoint')
  rw [hreject i] at h
  cases h

end Erdos85
#print axioms Erdos85.ThreeBlockOrbitCertificate.no_joint_of_search
