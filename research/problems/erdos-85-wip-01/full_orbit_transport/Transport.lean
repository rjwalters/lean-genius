import Assembly
import Proofs.Erdos85ThreeHighOrbitJointTransport
import Proofs.Erdos85ThreeHighOrbitRejection
import Proofs.Erdos85ThreeHighExternalSearchCertificate
import Proofs.Erdos85ThreeHighBranchDegreeClasses

namespace FullUOrbitTransport
open Erdos85 SimpleGraph
set_option maxRecDepth 100000
attribute [local irreducible] threeHighCrossDomain

/-- Complete full-U coverage carries every joint completion to one of55 representatives. -/
theorem joint_transport (p : ThreeBlockFirstRowParameters)
    (R : Fin 8 → Fin 8 → Bool) (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain (threeBlockCompactAdj p) R)
    (hExt : encodedExternalBlockCap (threeHighEmptyAdj (threeBlockCompactAdj p) R cross)
      threeHighCanonicalRow = true)
    (hJoint : ThreeHighJointWitness (threeHighEmptyAdj (threeBlockCompactAdj p) R cross)) :
    ∃ (r : Fin 55) (cross' : ThreeHighCross),
      cross' ∈ threeHighCrossDomain (FullURestrictedAssembly.representative r) R ∧
      encodedExternalBlockCap (threeHighEmptyAdj (FullURestrictedAssembly.representative r) R cross')
        threeHighCanonicalRow = true ∧
      ThreeHighJointWitness (threeHighEmptyAdj (FullURestrictedAssembly.representative r) R cross') := by
  obtain ⟨r,q,sw,hU⟩ := FullURestrictedAssembly.covered p
    (threeHighCrossDomain_U_c4 _ R cross hc)
  obtain ⟨cross',hc',hExt',hJoint'⟩ :=
    threeHighOrbit_joint_transport _ _ R q sw hU cross hc hExt hJoint
  exact ⟨r,cross',hc',hExt',hJoint'⟩

/-- Actual four-secondary-edge branch needs only55 U reps and13 degree-eight R reps. -/
theorem actual_full_witness
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    (s t v : Fin 49) (hst : s ≠ t) (hsv : s ≠ v) (htv : t ≠ v)
    (hS : threeHighTripleSpecialSet G z = {s,t,v})
    (hr : (G.induce (↑(threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)) :
      Set (Fin 49))).edgeFinset.card = 4) :
    ∃ (r : Fin 55) (q : Fin 21) (cross : ThreeHighCross),
      q ∈ threeHighSecondaryDegreeCodes 8 ∧
      cross ∈ threeHighCrossDomain (FullURestrictedAssembly.representative r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) ∧
      encodedExternalBlockCap (threeHighEmptyAdj (FullURestrictedAssembly.representative r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross)
        threeHighCanonicalRow = true ∧
      ThreeHighJointWitness (threeHighEmptyAdj (FullURestrictedAssembly.representative r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross) := by
  classical
  obtain ⟨e,p,q,cross,hp,hq,hc,heu,he,hExt,F,hF,hblock,hcompat,hcap⟩ :=
    threeHigh_triple_four_secondary_edges_orbit_external_candidate
      G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  have hq8 := threeHighFullUnion_secondary_degree_class (threeBlockFirstRowEmbed p) q cross hc
  obtain ⟨r,cross',hc',hExt',hJoint'⟩ := joint_transport p _ cross hc hExt
    ⟨F,hF,hblock,hcompat,hcap⟩
  exact ⟨r,q,cross',hq8,hc',hExt',hJoint'⟩

/-- The remaining finite search rejection premise is explicit:55 times13 pairs. -/
theorem actual_full_excluded
    (search : ThreeHighExternalSearch) (hsearch : ThreeHighExternalSearchSound search)
    (accept : (Fin 24 → Fin 24 → Bool) → Bool) (hsound : ThreeHighTerminalSound accept)
    (hreject : ∀ (r : Fin 55) (q : Fin 21), q ∈ threeHighSecondaryDegreeCodes 8 →
      search (FullURestrictedAssembly.representative r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q))
        (fun cross => accept (threeHighEmptyAdj (FullURestrictedAssembly.representative r)
          (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross)) = false)
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    (s t v : Fin 49) (hst : s ≠ t) (hsv : s ≠ v) (htv : t ≠ v)
    (hS : threeHighTripleSpecialSet G z = {s,t,v})
    (hr : (G.induce (↑(threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)) :
      Set (Fin 49))).edgeFinset.card = 4) : False := by
  obtain ⟨r,q,cross,hq,hc,hExt,hJoint⟩ := actual_full_witness
    G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  have h := hsearch _ _ (fun c => accept (threeHighEmptyAdj
    (FullURestrictedAssembly.representative r)
    (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) c)) cross hc hExt (hsound _ hJoint)
  rw [hreject r q hq] at h
  cases h

end FullUOrbitTransport
#print axioms FullUOrbitTransport.joint_transport
#print axioms FullUOrbitTransport.actual_full_witness
#print axioms FullUOrbitTransport.actual_full_excluded
