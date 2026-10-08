import Proofs.Erdos85ThreeHighDistinctOrbitCandidates
import Proofs.Erdos85ThreeHighDistinctOrbitTransport
import Proofs.Erdos85ThreeHighOrbitRejection
import Proofs.Erdos85ThreeHighBranchDegreeClasses
import Proofs.Erdos85ThreeBlockCompactOrbitCover

/-! Preserve distinct-neighbor witnesses through a supplied complete U orbit
cover. The coverage premise matches the retained full/deficient assemblies;
this module does not itself check their finite tables or any pair rejection. -/

namespace Erdos85
open SimpleGraph
set_option maxRecDepth 100000
attribute [local irreducible] threeHighCrossDomain

/-- Complete full-U coverage carries every joint completion to a supplied complete representative family. -/
theorem threeHigh_full_distinct_cover_transport {n : Nat}
    (reps : Fin n → Fin 15 → Fin 15 → Bool)
    (covered : ∀ p : ThreeBlockFirstRowParameters,
      encodedC4Free (threeBlockCompactAdj p) = true →
      ∃ (r : Fin n) (q : Fin 120) (sw : Bool), ∀ x y,
        threeBlockCompactAdj p x y =
          reps r (threeBlockOrbitLabel q sw x) (threeBlockOrbitLabel q sw y)) (p : ThreeBlockFirstRowParameters)
    (R : Fin 8 → Fin 8 → Bool) (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain (threeBlockCompactAdj p) R)
    (hExt : encodedExternalBlockCap (threeHighEmptyAdj (threeBlockCompactAdj p) R cross)
      threeHighCanonicalRow = true)
    (hJoint : ThreeHighDistinctJointWitness (threeHighEmptyAdj (threeBlockCompactAdj p) R cross)) :
    ∃ (r : Fin n) (cross' : ThreeHighCross),
      cross' ∈ threeHighCrossDomain (reps r) R ∧
      encodedExternalBlockCap (threeHighEmptyAdj (reps r) R cross')
        threeHighCanonicalRow = true ∧
      ThreeHighDistinctJointWitness (threeHighEmptyAdj (reps r) R cross') := by
  obtain ⟨r,q,sw,hU⟩ := covered p
    (threeHighCrossDomain_U_c4 _ R cross hc)
  obtain ⟨cross',hc',hExt',hJoint'⟩ :=
    threeHighOrbit_distinct_joint_transport _ _ R q sw hU cross hc hExt hJoint
  exact ⟨r,cross',hc',hExt',hJoint'⟩

/-- Move an actual full-branch graph to a supplied U cover and a degree-eight R representative. -/
theorem threeHigh_full_distinct_representative_witness {n : Nat}
    (reps : Fin n → Fin 15 → Fin 15 → Bool)
    (covered : ∀ p : ThreeBlockFirstRowParameters,
      encodedC4Free (threeBlockCompactAdj p) = true →
      ∃ (r : Fin n) (q : Fin 120) (sw : Bool), ∀ x y,
        threeBlockCompactAdj p x y =
          reps r (threeBlockOrbitLabel q sw x) (threeBlockOrbitLabel q sw y))
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
    ∃ (r : Fin n) (q : Fin 21) (cross : ThreeHighCross),
      q ∈ threeHighSecondaryDegreeCodes 8 ∧
      cross ∈ threeHighCrossDomain (reps r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) ∧
      encodedExternalBlockCap (threeHighEmptyAdj (reps r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross)
        threeHighCanonicalRow = true ∧
      ThreeHighDistinctJointWitness (threeHighEmptyAdj (reps r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross) := by
  classical
  obtain ⟨e,p,q,cross,hp,hq,hc,heu,he,hExt,hJoint⟩ :=
    threeHigh_triple_four_secondary_edges_distinct_orbit_external_candidate
      G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  have hq8 := threeHighFullUnion_secondary_degree_class (threeBlockFirstRowEmbed p) q cross hc
  obtain ⟨r,cross',hc',hExt',hJoint'⟩ := threeHigh_full_distinct_cover_transport reps covered p _ cross hc hExt hJoint
  exact ⟨r,q,cross',hq8,hc',hExt',hJoint'⟩


/-- Complete deficient-U coverage carries every joint completion to a supplied complete representative family. -/
theorem threeHigh_deficient_distinct_cover_transport {n : Nat}
    (reps : Fin n → Fin 15 → Fin 15 → Bool)
    (covered : ∀ p : ThreeBlockDeficientFirstRowParameters,
      encodedC4Free (threeBlockDeficientCompactAdj p) = true →
      ∃ (r : Fin n) (q : Fin 120) (sw : Bool), ∀ x y,
        threeBlockDeficientCompactAdj p x y =
          reps r (threeBlockOrbitLabel q sw x) (threeBlockOrbitLabel q sw y)) (p : ThreeBlockDeficientFirstRowParameters)
    (R : Fin 8 → Fin 8 → Bool) (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain (threeBlockDeficientCompactAdj p) R)
    (hExt : encodedExternalBlockCap (threeHighEmptyAdj (threeBlockDeficientCompactAdj p) R cross)
      threeHighCanonicalRow = true)
    (hJoint : ThreeHighDistinctJointWitness (threeHighEmptyAdj (threeBlockDeficientCompactAdj p) R cross)) :
    ∃ (r : Fin n) (cross' : ThreeHighCross),
      cross' ∈ threeHighCrossDomain (reps r) R ∧
      encodedExternalBlockCap (threeHighEmptyAdj (reps r) R cross')
        threeHighCanonicalRow = true ∧
      ThreeHighDistinctJointWitness (threeHighEmptyAdj (reps r) R cross') := by
  obtain ⟨r,q,sw,hU⟩ := covered p
    (threeHighCrossDomain_U_c4 _ R cross hc)
  obtain ⟨cross',hc',hExt',hJoint'⟩ :=
    threeHighOrbit_distinct_joint_transport _ _ R q sw hU cross hc hExt hJoint
  exact ⟨r,cross',hc',hExt',hJoint'⟩

set_option linter.constructorNameAsVariable false in
/-- Move an actual deficient-branch graph to a supplied U cover and a degree-six R representative. -/
theorem threeHigh_deficient_distinct_representative_witness {n : Nat}
    (reps : Fin n → Fin 15 → Fin 15 → Bool)
    (covered : ∀ p : ThreeBlockDeficientFirstRowParameters,
      encodedC4Free (threeBlockDeficientCompactAdj p) = true →
      ∃ (r : Fin n) (q : Fin 120) (sw : Bool), ∀ x y,
        threeBlockDeficientCompactAdj p x y =
          reps r (threeBlockOrbitLabel q sw x) (threeBlockOrbitLabel q sw y))
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
    ∃ (r : Fin n) (q : Fin 21) (cross : ThreeHighCross),
      q ∈ threeHighSecondaryDegreeCodes 6 ∧
      cross ∈ threeHighCrossDomain (reps r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) ∧
      encodedExternalBlockCap (threeHighEmptyAdj (reps r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross)
        threeHighCanonicalRow = true ∧
      ThreeHighDistinctJointWitness (threeHighEmptyAdj (reps r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross) := by
  classical
  obtain ⟨e,p,q,cross,hp,hq,hc,heu,he,hExt,hJoint⟩ :=
    threeHigh_triple_three_secondary_edges_distinct_orbit_external_candidate
      G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  have hq6 := threeHighDeficientUnion_secondary_degree_class (threeBlockDeficientFirstRowEmbed p) q cross hc
  obtain ⟨r,cross',hc',hExt',hJoint'⟩ := threeHigh_deficient_distinct_cover_transport reps covered p _ cross hc hExt hJoint
  exact ⟨r,q,cross',hq6,hc',hExt',hJoint'⟩


end Erdos85

#print axioms Erdos85.threeHigh_full_distinct_cover_transport

#print axioms Erdos85.threeHigh_full_distinct_representative_witness

#print axioms Erdos85.threeHigh_deficient_distinct_cover_transport

#print axioms Erdos85.threeHigh_deficient_distinct_representative_witness
