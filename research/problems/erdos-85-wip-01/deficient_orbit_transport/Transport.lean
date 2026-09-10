import Assembly
import Pruning
import Proofs.Erdos85ThreeHighOrbitJointTransport
import Proofs.Erdos85ThreeHighOrbitRejection
import Proofs.Erdos85ThreeHighExternalSearchCertificate
import Proofs.Erdos85ThreeHighBranchDegreeClasses

namespace DeficientUOrbitTransport
open Erdos85 SimpleGraph
set_option maxRecDepth 1000000
attribute [local irreducible] threeHighCrossDomain

/-- Complete deficient-U coverage carries every joint completion to one of370 representatives. -/
theorem joint_transport (p : ThreeBlockDeficientFirstRowParameters)
    (R : Fin 8 → Fin 8 → Bool) (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain (threeBlockDeficientCompactAdj p) R)
    (hExt : encodedExternalBlockCap (threeHighEmptyAdj (threeBlockDeficientCompactAdj p) R cross)
      threeHighCanonicalRow = true)
    (hJoint : ThreeHighJointWitness (threeHighEmptyAdj (threeBlockDeficientCompactAdj p) R cross)) :
    ∃ (r : Fin 370) (cross' : ThreeHighCross),
      cross' ∈ threeHighCrossDomain (DeficientUNormalizedAssembly.representative r) R ∧
      encodedExternalBlockCap (threeHighEmptyAdj (DeficientUNormalizedAssembly.representative r) R cross')
        threeHighCanonicalRow = true ∧
      ThreeHighJointWitness (threeHighEmptyAdj (DeficientUNormalizedAssembly.representative r) R cross') := by
  obtain ⟨r,q,sw,hU⟩ := DeficientUNormalizedAssembly.covered p
    (threeHighCrossDomain_U_c4 _ R cross hc)
  obtain ⟨cross',hc',hExt',hJoint'⟩ :=
    threeHighOrbit_joint_transport _ _ R q sw hU cross hc hExt hJoint
  exact ⟨r,cross',hc',hExt',hJoint'⟩

set_option linter.constructorNameAsVariable false in
/-- Actual three-secondary-edge branch needs only370 U reps and8 degree-six R reps. -/
theorem actual_deficient_witness
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
      Set (Fin 49))).edgeFinset.card = 3) :
    ∃ (r : Fin 370) (q : Fin 21) (cross : ThreeHighCross),
      q ∈ threeHighSecondaryDegreeCodes 6 ∧
      cross ∈ threeHighCrossDomain (DeficientUNormalizedAssembly.representative r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) ∧
      encodedExternalBlockCap (threeHighEmptyAdj (DeficientUNormalizedAssembly.representative r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross)
        threeHighCanonicalRow = true ∧
      ThreeHighJointWitness (threeHighEmptyAdj (DeficientUNormalizedAssembly.representative r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross) := by
  classical
  obtain ⟨e,p,q,cross,hp,hq,hc,heu,he,hExt,F,hF,hblock,hcompat,hcap⟩ :=
    threeHigh_triple_three_secondary_edges_orbit_external_candidate
      G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  have hq6 := threeHighDeficientUnion_secondary_degree_class (threeBlockDeficientFirstRowEmbed p) q cross hc
  obtain ⟨r,cross',hc',hExt',hJoint'⟩ := joint_transport p _ cross hc hExt
    ⟨F,hF,hblock,hcompat,hcap⟩
  exact ⟨r,q,cross',hq6,hc',hExt',hJoint'⟩

/-- Only the 1554 pairs surviving the verified structural exclusions need search rejection. -/
theorem actual_deficient_excluded
    (search : ThreeHighExternalSearch) (hsearch : ThreeHighExternalSearchSound search)
    (accept : (Fin 24 → Fin 24 → Bool) → Bool) (hsound : ThreeHighTerminalSound accept)
    (hreject : ∀ (r : Fin 370) (q : Fin 21),
      (r,q) ∈ DeficientUOrbitPruning.remainingPairs →
      search (DeficientUNormalizedAssembly.representative r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q))
        (fun cross => accept (threeHighEmptyAdj (DeficientUNormalizedAssembly.representative r)
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
      Set (Fin 49))).edgeFinset.card = 3) : False := by
  obtain ⟨r,q,cross,hq,hc,hExt,hJoint⟩ := actual_deficient_witness
    G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  have h := hsearch _ _ (fun c => accept (threeHighEmptyAdj
    (DeficientUNormalizedAssembly.representative r)
    (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) c)) cross hc hExt (hsound _ hJoint)
  have hpair := DeficientUOrbitPruning.actual_pair_mem r q cross hq hc hExt
  rw [hreject r q hpair] at h
  cases h

end DeficientUOrbitTransport
#print axioms DeficientUOrbitTransport.joint_transport
#print axioms DeficientUOrbitTransport.actual_deficient_witness
#print axioms DeficientUOrbitTransport.actual_deficient_excluded
