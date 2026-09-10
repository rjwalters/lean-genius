import Proofs.Erdos85OrderFortyNineThreeHighTripleEmptyCandidateRows
import Proofs.Erdos85ThreeBlockFirstRowDomain

namespace Erdos85
open SimpleGraph
noncomputable section
attribute [local irreducible] threeBlockFullCandidates threeBlockDeficientCandidates
  threeHighSecondaryDomain threeHighCrossDomain encodedC4Free encodedDegreeProfile

theorem threeHigh_triple_four_secondary_edges_compact_empty_candidate_rows
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
    ∃ a b c : Fin 49, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      threeHighTripleSpecialSet G z = {a,b,c} ∧
    ∃ (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49)))
      (p : ThreeBlockFirstRowParameters) (t : ThreeHighSecondaryTuple) (cross : ThreeHighCross),
      threeBlockFirstRowEmbed p ∈ threeBlockFullCandidates ∧ t ∈ threeHighSecondaryDomain ∧
      cross ∈ threeHighCrossDomain (threeHighFullUnionAdj (threeBlockFirstRowEmbed p)) (threeHighSecondaryTupleAdj t) ∧
      (e 23).val = u ∧
      (∀ i, (e (threeHighEmptyUIndex ((@finProdFinEquiv 3 5) (0,i)))).val ∈
        G.neighborFinset a ∩ threeHighTripleEmptySet G) ∧
      (∀ i, (e (threeHighEmptyUIndex ((@finProdFinEquiv 3 5) (1,i)))).val ∈
        G.neighborFinset b ∩ threeHighTripleEmptySet G) ∧
      (∀ i, (e (threeHighEmptyUIndex ((@finProdFinEquiv 3 5) (2,i)))).val ∈
        G.neighborFinset c ∩ threeHighTripleEmptySet G) ∧
      ∀ a b, decide (G.Adj (e a).val (e b).val) =
        threeHighEmptyAdj (threeHighFullUnionAdj (threeBlockFirstRowEmbed p)) (threeHighSecondaryTupleAdj t) cross a b := by
  classical
  obtain ⟨rawLabel,π,masks,hmasks,hrawRow0,hrawRow1,hrawRow2,hrawEnc⟩ :=
    threeHigh_triple_four_secondary_edges_union_template_rows
      G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  let raw : ThreeBlockFullParameters := (fun k => ⟨masks k, hmasks k⟩, π)
  have hraw : raw ∈ threeBlockFullCandidates := by
    apply (threeBlockFullCandidates_mem_iff raw).mpr
    exact encodedC4Free_of_injective_graph G hfree (fun x => (rawLabel x).val)
      (fun x y h => rawLabel.injective (Subtype.ext h)) _ hrawEnc
  obtain ⟨p',σ,hp',hzero,hcanon⟩ := threeBlockFullCandidates_first_row raw hraw
  obtain ⟨small,hsmall⟩ := threeBlockFirstRowEmbed_cover p' hzero
  let p : ThreeBlockFullParameters := threeBlockFirstRowEmbed small
  have hp : p ∈ threeBlockFullCandidates := by simpa only [p,hsmall] using hp'
  let uLabel : (Fin 3 × Fin 5) ≃ (↑(threeHighTripleSpecialUnion G z) : Set (Fin 49)) :=
    (Equiv.prodCongr (Equiv.refl (Fin 3)) σ).symm.trans rawLabel
  have huEnc (a b : Fin 3 × Fin 5) : decide (G.Adj (uLabel a).val (uLabel b).val) =
      threeBlockFullParameterAdj p a b := by
    have hh := (hrawEnc (a.1,σ.symm a.2) (b.1,σ.symm b.2)).trans
      (hcanon (a.1,σ.symm a.2) (b.1,σ.symm b.2))
    simpa [uLabel,p,hsmall,Prod.map] using hh
  have hrow0 (i : Fin 5) : (uLabel (0,i)).val ∈
      G.neighborFinset s ∩ threeHighTripleEmptySet G := by
    simpa [uLabel] using hrawRow0 (σ.symm i)
  have hrow1 (i : Fin 5) : (uLabel (1,i)).val ∈
      G.neighborFinset t ∩ threeHighTripleEmptySet G := by
    simpa [uLabel] using hrawRow1 (σ.symm i)
  have hrow2 (i : Fin 5) : (uLabel (2,i)).val ∈
      G.neighborFinset v ∩ threeHighTripleEmptySet G := by
    simpa [uLabel] using hrawRow2 (σ.symm i)
  obtain ⟨q,hq,rLabel,hm,hN,hT,hrEnc⟩ := threeHigh_triple_secondary_domain_cover
    G hfree hmin hHigh hone z hz hu huz
  let lU : Fin 15 ≃ (↑(threeHighTripleSpecialUnion G z) : Set (Fin 49)) :=
    (@finProdFinEquiv 3 5).symm.trans uLabel
  obtain ⟨e,cross,heu,heU,he,hd⟩ := threeHigh_triple_empty_template_of_labelings
    G hfree hmin hHigh hone z hz hu huz lU rLabel _ hN hT hrEnc
  have hfun : (fun i j => decide (G.Adj (lU i).val (lU j).val)) = threeHighFullUnionAdj p := by
    funext i j
    exact huEnc _ _
  have he' : ∀ a b, decide (G.Adj (e a).val (e b).val) =
      threeHighEmptyAdj (threeHighFullUnionAdj p) (threeHighSecondaryTupleAdj q) cross a b := by
    simpa only [hfun] using he
  have hc := threeHigh_triple_cross_domain_mem G hfree hmin hHigh hone z hz hu huz
    e heu (threeHighFullUnionAdj p) (threeHighSecondaryTupleAdj q) cross he'
  refine ⟨s,t,v,hst,hsv,htv,hS,e,small,q,cross,hp,hq,hc,heu,?_,?_,?_,he'⟩
  · intro i
    rw [heU]
    simpa only [lU, Equiv.trans_apply, Equiv.symm_apply_apply] using hrow0 i

  · intro i
    rw [heU]
    simpa only [lU, Equiv.trans_apply, Equiv.symm_apply_apply] using hrow1 i

  · intro i
    rw [heU]
    simpa only [lU, Equiv.trans_apply, Equiv.symm_apply_apply] using hrow2 i


theorem threeHigh_triple_three_secondary_edges_compact_empty_candidate_rows
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
    ∃ a b c : Fin 49, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      threeHighTripleSpecialSet G z = {a,b,c} ∧
    ∃ (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49)))
      (p : ThreeBlockDeficientFirstRowParameters) (t : ThreeHighSecondaryTuple) (cross : ThreeHighCross),
      threeBlockDeficientFirstRowEmbed p ∈ threeBlockDeficientCandidates ∧ t ∈ threeHighSecondaryDomain ∧
      cross ∈ threeHighCrossDomain (threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed p)) (threeHighSecondaryTupleAdj t) ∧
      (e 23).val = u ∧
      (∀ i, (e (threeHighEmptyUIndex ((@finProdFinEquiv 3 5) (0,i)))).val ∈
        G.neighborFinset a ∩ threeHighTripleEmptySet G) ∧
      (∀ i, (e (threeHighEmptyUIndex ((@finProdFinEquiv 3 5) (1,i)))).val ∈
        G.neighborFinset b ∩ threeHighTripleEmptySet G) ∧
      (∀ i, (e (threeHighEmptyUIndex ((@finProdFinEquiv 3 5) (2,i)))).val ∈
        G.neighborFinset c ∩ threeHighTripleEmptySet G) ∧
      ∀ a b, decide (G.Adj (e a).val (e b).val) =
        threeHighEmptyAdj (threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed p)) (threeHighSecondaryTupleAdj t) cross a b := by
  classical
  obtain ⟨a,b,c,hab,hac,hbc,hSnew,rawLabel,π,d,masks,hmasks,hrawRow0,hrawRow1,hrawRow2,hrawEnc⟩ :=
    threeHigh_triple_three_secondary_edges_union_template_rows
      G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  let raw : ThreeBlockDeficientParameters := ((fun k => ⟨masks k, hmasks k⟩, π), d)
  have hraw : raw ∈ threeBlockDeficientCandidates := by
    apply (threeBlockDeficientCandidates_mem_iff raw).mpr
    exact encodedC4Free_of_injective_graph G hfree (fun x => (rawLabel x).val)
      (fun x y h => rawLabel.injective (Subtype.ext h)) _ hrawEnc
  obtain ⟨p',σ,hp',hzero,hcanon⟩ := threeBlockDeficientCandidates_first_row raw hraw
  obtain ⟨small,hsmall⟩ := threeBlockDeficientFirstRowEmbed_cover p' hzero
  let p : ThreeBlockDeficientParameters := threeBlockDeficientFirstRowEmbed small
  have hp : p ∈ threeBlockDeficientCandidates := by simpa only [p,hsmall] using hp'
  let uLabel : (Fin 3 × Fin 5) ≃ (↑(threeHighTripleSpecialUnion G z) : Set (Fin 49)) :=
    (Equiv.prodCongr (Equiv.refl (Fin 3)) σ).symm.trans rawLabel
  have huEnc (a b : Fin 3 × Fin 5) : decide (G.Adj (uLabel a).val (uLabel b).val) =
      threeBlockDeficientParameterAdj p a b := by
    have hh := (hrawEnc (a.1,σ.symm a.2) (b.1,σ.symm b.2)).trans
      (hcanon (a.1,σ.symm a.2) (b.1,σ.symm b.2))
    simpa [uLabel,p,hsmall,Prod.map] using hh
  have hrow0 (i : Fin 5) : (uLabel (0,i)).val ∈
      G.neighborFinset a ∩ threeHighTripleEmptySet G := by
    simpa [uLabel] using hrawRow0 (σ.symm i)
  have hrow1 (i : Fin 5) : (uLabel (1,i)).val ∈
      G.neighborFinset b ∩ threeHighTripleEmptySet G := by
    simpa [uLabel] using hrawRow1 (σ.symm i)
  have hrow2 (i : Fin 5) : (uLabel (2,i)).val ∈
      G.neighborFinset c ∩ threeHighTripleEmptySet G := by
    simpa [uLabel] using hrawRow2 (σ.symm i)
  obtain ⟨q,hq,rLabel,hm,hN,hT,hrEnc⟩ := threeHigh_triple_secondary_domain_cover
    G hfree hmin hHigh hone z hz hu huz
  let lU : Fin 15 ≃ (↑(threeHighTripleSpecialUnion G z) : Set (Fin 49)) :=
    (@finProdFinEquiv 3 5).symm.trans uLabel
  obtain ⟨e,cross,heu,heU,he,hd⟩ := threeHigh_triple_empty_template_of_labelings
    G hfree hmin hHigh hone z hz hu huz lU rLabel _ hN hT hrEnc
  have hfun : (fun i j => decide (G.Adj (lU i).val (lU j).val)) = threeHighDeficientUnionAdj p := by
    funext i j
    exact huEnc _ _
  have he' : ∀ a b, decide (G.Adj (e a).val (e b).val) =
      threeHighEmptyAdj (threeHighDeficientUnionAdj p) (threeHighSecondaryTupleAdj q) cross a b := by
    simpa only [hfun] using he
  have hc := threeHigh_triple_cross_domain_mem G hfree hmin hHigh hone z hz hu huz
    e heu (threeHighDeficientUnionAdj p) (threeHighSecondaryTupleAdj q) cross he'
  refine ⟨a,b,c,hab,hac,hbc,hSnew,e,small,q,cross,hp,hq,hc,heu,?_,?_,?_,he'⟩
  · intro i
    rw [heU]
    simpa only [lU, Equiv.trans_apply, Equiv.symm_apply_apply] using hrow0 i

  · intro i
    rw [heU]
    simpa only [lU, Equiv.trans_apply, Equiv.symm_apply_apply] using hrow1 i

  · intro i
    rw [heU]
    simpa only [lU, Equiv.trans_apply, Equiv.symm_apply_apply] using hrow2 i


end
end Erdos85
#print axioms Erdos85.threeHigh_triple_four_secondary_edges_compact_empty_candidate_rows
#print axioms Erdos85.threeHigh_triple_three_secondary_edges_compact_empty_candidate_rows
