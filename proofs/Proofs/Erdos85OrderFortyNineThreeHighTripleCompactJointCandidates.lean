import Proofs.Erdos85OrderFortyNineThreeHighTripleCompactEmptyCandidateRows
import Proofs.Erdos85OrderFortyNineThreeHighTripleJointBlockFamilies
import Proofs.Erdos85ThreeDistinctLabels

namespace Erdos85
open SimpleGraph
noncomputable section
attribute [local irreducible] threeBlockFullCandidates threeBlockDeficientCandidates
  threeHighSecondaryDomain threeHighCrossDomain threeHighResolutionDomain

theorem threeHigh_triple_four_secondary_edges_compact_joint_candidate
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
    ∃ (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49)))
      (p : ThreeBlockFirstRowParameters) (q : ThreeHighSecondaryTuple) (cross : ThreeHighCross),
      threeBlockFirstRowEmbed p ∈ threeBlockFullCandidates ∧ q ∈ threeHighSecondaryDomain ∧
      cross ∈ threeHighCrossDomain (threeHighFullUnionAdj (threeBlockFirstRowEmbed p)) (threeHighSecondaryTupleAdj q) ∧
      (e 23).val = u ∧
      (∀ i j, decide (G.Adj (e i).val (e j).val) = threeHighEmptyAdj (threeHighFullUnionAdj (threeBlockFirstRowEmbed p)) (threeHighSecondaryTupleAdj q) cross i j) ∧
      ∃ F : Fin 3 → Finset (Finset (Fin 24)),
        (∀ k, F k ∈ threeHighResolutionDomain (threeHighEmptyAdj (threeHighFullUnionAdj (threeBlockFirstRowEmbed p)) (threeHighSecondaryTupleAdj q) cross) (threeHighCanonicalResidual k)) ∧
        (∀ k, ∀ S ∈ F k, encodedTripleBlockCap threeHighCanonicalRow S = true) ∧
        (∀ k l, encodedFamilyCompatibility (threeHighEmptyAdj (threeHighFullUnionAdj (threeBlockFirstRowEmbed p)) (threeHighSecondaryTupleAdj q) cross) (F k) (F l) = true) ∧
        (∀ k l, k ≠ l → encodedFamilyIntersectionCap (F k) (F l) = true) := by
  classical
  obtain ⟨a,b,c,hab,hac,hbc,hS',e,p,q,cross,hp,hq,hc,heu,hrow0,hrow1,hrow2,he⟩ :=
    threeHigh_triple_four_secondary_edges_compact_empty_candidate_rows G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  let P : Fin 3 → Fin 49 → Prop := fun k x => x ∈ threeHighTripleSpecialSet G z ∧
    ∀ i, (e (threeHighEmptyUIndex ((@finProdFinEquiv 3 5) (k,i)))).val ∈
      G.neighborFinset x ∩ threeHighTripleEmptySet G
  have hP0 : P 0 a := ⟨by rw [hS']; simp, hrow0⟩
  have hP1 : P 1 b := ⟨by rw [hS']; simp, hrow1⟩
  have hP2 : P 2 c := ⟨by rw [hS']; simp, hrow2⟩
  obtain ⟨roots,hinj,hroots⟩ := three_distinct_labels a b c hab hac hbc P hP0 hP1 hP2
  refine ⟨e,p,q,cross,hp,hq,hc,heu,he,?_⟩
  exact threeHigh_triple_joint_block_families G hfree hmin hHigh hone z hz hu huz roots
    (fun k => (hroots k).1) hinj e heu (fun k => (hroots k).2) _ he

theorem threeHigh_triple_three_secondary_edges_compact_joint_candidate
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
    ∃ (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49)))
      (p : ThreeBlockDeficientFirstRowParameters) (q : ThreeHighSecondaryTuple) (cross : ThreeHighCross),
      threeBlockDeficientFirstRowEmbed p ∈ threeBlockDeficientCandidates ∧ q ∈ threeHighSecondaryDomain ∧
      cross ∈ threeHighCrossDomain (threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed p)) (threeHighSecondaryTupleAdj q) ∧
      (e 23).val = u ∧
      (∀ i j, decide (G.Adj (e i).val (e j).val) = threeHighEmptyAdj (threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed p)) (threeHighSecondaryTupleAdj q) cross i j) ∧
      ∃ F : Fin 3 → Finset (Finset (Fin 24)),
        (∀ k, F k ∈ threeHighResolutionDomain (threeHighEmptyAdj (threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed p)) (threeHighSecondaryTupleAdj q) cross) (threeHighCanonicalResidual k)) ∧
        (∀ k, ∀ S ∈ F k, encodedTripleBlockCap threeHighCanonicalRow S = true) ∧
        (∀ k l, encodedFamilyCompatibility (threeHighEmptyAdj (threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed p)) (threeHighSecondaryTupleAdj q) cross) (F k) (F l) = true) ∧
        (∀ k l, k ≠ l → encodedFamilyIntersectionCap (F k) (F l) = true) := by
  classical
  obtain ⟨a,b,c,hab,hac,hbc,hS',e,p,q,cross,hp,hq,hc,heu,hrow0,hrow1,hrow2,he⟩ :=
    threeHigh_triple_three_secondary_edges_compact_empty_candidate_rows G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  let P : Fin 3 → Fin 49 → Prop := fun k x => x ∈ threeHighTripleSpecialSet G z ∧
    ∀ i, (e (threeHighEmptyUIndex ((@finProdFinEquiv 3 5) (k,i)))).val ∈
      G.neighborFinset x ∩ threeHighTripleEmptySet G
  have hP0 : P 0 a := ⟨by rw [hS']; simp, hrow0⟩
  have hP1 : P 1 b := ⟨by rw [hS']; simp, hrow1⟩
  have hP2 : P 2 c := ⟨by rw [hS']; simp, hrow2⟩
  obtain ⟨roots,hinj,hroots⟩ := three_distinct_labels a b c hab hac hbc P hP0 hP1 hP2
  refine ⟨e,p,q,cross,hp,hq,hc,heu,he,?_⟩
  exact threeHigh_triple_joint_block_families G hfree hmin hHigh hone z hz hu huz roots
    (fun k => (hroots k).1) hinj e heu (fun k => (hroots k).2) _ he

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_four_secondary_edges_compact_joint_candidate
#print axioms Erdos85.threeHigh_triple_three_secondary_edges_compact_joint_candidate
