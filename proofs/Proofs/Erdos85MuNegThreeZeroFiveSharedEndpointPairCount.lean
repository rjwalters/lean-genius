import Proofs.Erdos85EdgeIndexedServiceSharedEndpointForbiddenPairs
import Proofs.Erdos85MuNegThreeZeroFiveShoreTypePopulations

/-! # Counting shared-endpoint forbidden pairs in a corrected h305 shore -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

private def shoreEdgePairsAt
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (S : Finset V) (x : V) :
    Finset (Finset R.edgeFinset) :=
  ((shoreTypeEdgeFinset R S 2).filter fun a ↦ x ∈ a.1.toFinset).powersetCard 2

private theorem sharedEndpointShoreEdgePairFinset_eq_biUnion
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (S : Finset V) :
    sharedEndpointShoreEdgePairFinset R S =
      S.biUnion (shoreEdgePairsAt R S) := by
  classical
  ext T
  simp only [sharedEndpointShoreEdgePairFinset, shoreEdgePairsAt,
    mem_filter, mem_powersetCard, mem_biUnion]
  constructor
  · rintro ⟨⟨hsub, hcard⟩, x, hxS, hx⟩
    refine ⟨x, hxS, ?_⟩
    refine ⟨?_, hcard⟩
    intro a ha
    exact mem_filter.mpr ⟨hsub ha, hx a ha⟩
  · rintro ⟨x, hxS, hT⟩
    obtain ⟨hsub, hcard⟩ := hT
    refine ⟨⟨?_, hcard⟩, x, hxS, ?_⟩
    · intro a ha
      exact (mem_filter.mp (hsub ha)).1
    · intro a ha
      exact (mem_filter.mp (hsub ha)).2

private theorem shoreEdgePairsAt_pairwiseDisjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (S : Finset V) :
    (S : Set V).PairwiseDisjoint (shoreEdgePairsAt R S) := by
  classical
  intro x hxS y hyS hxy
  change Disjoint (shoreEdgePairsAt R S x) (shoreEdgePairsAt R S y)
  rw [Finset.disjoint_left]
  intro T hxT hyT
  have hcard : T.card = 2 := (mem_powersetCard.mp hxT).2
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  have hsubx := (mem_powersetCard.mp hxT).1
  have hsuby := (mem_powersetCard.mp hyT).1
  have hax : x ∈ a.1.toFinset :=
    (mem_filter.mp (hsubx (by simp))).2
  have hbx : x ∈ b.1.toFinset :=
    (mem_filter.mp (hsubx (by simp))).2
  have hay : y ∈ a.1.toFinset :=
    (mem_filter.mp (hsuby (by simp))).2
  have hby : y ∈ b.1.toFinset :=
    (mem_filter.mp (hsuby (by simp))).2
  have hpair : ({x, y} : Finset V).card = 2 := by simp [hxy]
  have haCard : a.1.toFinset.card = 2 :=
    R.card_toFinset_mem_edgeFinset a
  have hbCard : b.1.toFinset.card = 2 :=
    R.card_toFinset_mem_edgeFinset b
  have haeq : a.1.toFinset = {x, y} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    · omega
  have hbeq : b.1.toFinset = {x, y} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    · omega
  have hab' : a = b := by
    apply Subtype.ext
    rw [Sym2.ext_iff]
    intro z
    rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, haeq, hbeq]
  exact hab hab'

/-- Generic double count: if every shore vertex lies on exactly three
shore-type-two edges, then the shared-endpoint pair family has size
`3 * |S|`. -/
theorem sharedEndpointShoreEdgePairFinset_card_of_incident_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (S : Finset V)
    (hthree : ∀ x ∈ S,
      ((shoreTypeEdgeFinset R S 2).filter fun a ↦
        x ∈ a.1.toFinset).card = 3) :
    (sharedEndpointShoreEdgePairFinset R S).card = 3 * S.card := by
  classical
  rw [sharedEndpointShoreEdgePairFinset_eq_biUnion,
    Finset.card_biUnion (shoreEdgePairsAt_pairwiseDisjoint R S)]
  calc
    (∑ x ∈ S, (shoreEdgePairsAt R S x).card) =
        ∑ x ∈ S, 3 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [shoreEdgePairsAt, Finset.card_powersetCard, hthree x hx]
      decide
    _ = 3 * S.card := by simp [mul_comm]

private theorem shoreTypeTwo_incident_card_eq_internalNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (S : Finset V)
    (x : V) (hx : x ∈ S) :
    ((shoreTypeEdgeFinset R S 2).filter fun a ↦
      x ∈ a.1.toFinset).card =
      ((R.neighborFinset x).filter fun y ↦ y ∈ S).card := by
  classical
  let H := R.induce (↑S : Set V)
  let xs : (↑S : Set V) := ⟨x, hx⟩
  let eV : (↑S : Set V) ↪ V := Function.Embedding.subtype _
  let eR : R.edgeFinset ↪ Sym2 V := Function.Embedding.subtype _
  have hmapEdges : H.edgeFinset.map eV.sym2Map =
      R.edgeFinset ∩ S.sym2 := by
    aesop (add simp [Finset.ext_iff, Sym2.exists, Sym2.forall,
      SimpleGraph.adj_comm, H, eV])
  have hedge :
      (H.incidenceFinset xs).map eV.sym2Map =
        ((shoreTypeEdgeFinset R S 2).filter fun a ↦
          x ∈ a.1.toFinset).map eR := by
    ext a
    simp only [Finset.mem_map, SimpleGraph.mem_incidenceFinset,
      Finset.mem_filter]
    constructor
    · rintro ⟨b, hb, rfl⟩
      have hbEdge : b ∈ H.edgeFinset := by simpa using hb.1
      have hbMap := Finset.mem_map_of_mem eV.sym2Map hbEdge
      rw [hmapEdges] at hbMap
      let c : R.edgeFinset := ⟨eV.sym2Map b, (Finset.mem_inter.mp hbMap).1⟩
      refine ⟨c, ?_, rfl⟩
      refine ⟨?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        have hall : ∀ z ∈ c.1.toFinset, z ∈ S := by
          intro z hz
          have hzmap : z ∈ eV.sym2Map b := by
            rw [← Sym2.mem_toFinset]
            exact hz
          obtain ⟨w, _, hw⟩ := (Sym2.mem_map.mp hzmap)
          rw [← hw]
          exact w.2
        rw [Finset.inter_eq_left.mpr hall,
          R.card_toFinset_mem_edgeFinset c]
      · have hxb : xs ∈ b := hb.2
        apply Sym2.mem_toFinset.mpr
        exact Sym2.mem_map.mpr ⟨xs, hxb, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      have hcE := Finset.mem_filter.mp hc.1
      have hall : ∀ z ∈ c.1.toFinset, z ∈ S := by
        have hinter : c.1.toFinset ∩ S = c.1.toFinset := by
          apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
          rw [hcE.2, R.card_toFinset_mem_edgeFinset c]
        intro z hz
        exact (Finset.mem_inter.mp (hinter.symm ▸ hz)).2
      have hlift : ∀ a : Sym2 V, (∀ z ∈ a.toFinset, z ∈ S) →
          ∃ b : Sym2 (↑S : Set V), eV.sym2Map b = a := by
        intro a
        induction a using Sym2.inductionOn with
        | _ p q =>
            intro hpq
            have hp : p ∈ S := hpq p (by simp)
            have hq : q ∈ S := hpq q (by simp)
            exact ⟨s(⟨p, hp⟩, ⟨q, hq⟩), rfl⟩
      obtain ⟨b, hbmap⟩ := hlift c.1 hall
      have hbInter : eV.sym2Map b ∈ R.edgeFinset ∩ S.sym2 := by
        rw [hbmap]
        refine Finset.mem_inter.mpr ⟨c.2, Finset.mem_sym2_iff.mpr ?_⟩
        intro z hz
        exact hall z (by simpa [hbmap] using hz)
      rw [← hmapEdges] at hbInter
      obtain ⟨b', hb'Edge, hb'eq⟩ := Finset.mem_map.mp hbInter
      have hbb' : b' = b := eV.sym2Map.injective hb'eq
      subst b'
      let d : H.edgeFinset := ⟨b, hb'Edge⟩
      refine ⟨d, ?_, ?_⟩
      · change b ∈ H.incidenceSet xs
        refine ⟨(by simpa using hb'Edge), ?_⟩
        have : x ∈ eV.sym2Map b := by simpa [hbmap] using hc.2
        obtain ⟨w, hwb, hw⟩ := Sym2.mem_map.mp this
        have hwx : w = xs := by apply Subtype.ext; exact hw
        simpa [hwx] using hwb
      · exact hbmap
  have hedgeCard := congrArg Finset.card hedge
  simp only [Finset.card_map] at hedgeCard
  have hneighbor :
      (H.neighborFinset xs).map eV =
        (R.neighborFinset x).filter fun y ↦ y ∈ S := by
    ext y
    simp [H, xs, eV, SimpleGraph.mem_neighborFinset]
  have hneighborCard := congrArg Finset.card hneighbor
  simp only [Finset.card_map] at hneighborCard
  rw [hedgeCard.symm, H.card_incidenceFinset_eq_degree,
    ← H.card_neighborFinset_eq_degree, hneighborCard]

/-- Every coordinate of a corrected h305 shore lies on exactly three
shore-type-two exterior edges. -/
theorem h305_correctShoreMode_incident_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hmode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u) :
    let U := (Finset.univ : Finset (ZMod 8)).image u
    ∀ x ∈ U, ((shoreTypeEdgeFinset R U 2).filter fun a ↦
      x ∈ a.1.toFinset).card = 3 := by
  classical
  dsimp only
  let U := (Finset.univ : Finset (ZMod 8)).image u
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  rw [shoreTypeTwo_incident_card_eq_internalNeighbor R U (u i)
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)]
  let T := (Finset.univ : Finset (ZMod 8)).filter fun j ↦
    R.Adj (u i) (u j)
  let eu : ZMod 8 ↪ V := ⟨u, huinj⟩
  have heq : T.map eu =
      (R.neighborFinset (u i)).filter fun y ↦ y ∈ U := by
    ext y
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
      true_and, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hadj : R.Adj (u i) (u j) := by simpa [T] using hj
      refine ⟨?_, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
      exact hadj
    · rintro ⟨hy, hyU⟩
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hyU
      exact ⟨j, (by simpa [T] using hy), rfl⟩
  have heqCard := congrArg Finset.card heq
  rw [Finset.card_map] at heqCard
  rw [← heqCard]
  rcases hmode with htri | htf
  · have : T = (Finset.univ : Finset (ZMod 8)).filter fun j ↦
        j - i = 1 ∨ j - i = 4 ∨ j - i = 7 := by
      ext j
      simp [T, htri i j]
    rw [this]
    generalize i = k
    revert k
    decide
  · have : T = (Finset.univ : Finset (ZMod 8)).filter fun j ↦
        j - i = 3 ∨ j - i = 4 ∨ j - i = 5 := by
      ext j
      simp [T, htf i j]
    rw [this]
    generalize i = k
    revert k
    decide

/-- A corrected h305 shore has exactly 24 unordered pairs of distinct
shore-type-two edges sharing a shore endpoint. -/
theorem h305_sharedEndpointShoreEdgePairFinset_card_twentyFour
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hmode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u) :
    let U := (Finset.univ : Finset (ZMod 8)).image u
    (sharedEndpointShoreEdgePairFinset R U).card = 24 := by
  classical
  dsimp only
  let U := (Finset.univ : Finset (ZMod 8)).image u
  rw [sharedEndpointShoreEdgePairFinset_card_of_incident_three R U
    (h305_correctShoreMode_incident_three R u huinj hmode)]
  have hU : U.card = 8 := by
    rw [Finset.card_image_of_injective _ huinj]
    decide
  rw [hU]

end

end Erdos85

#print axioms Erdos85.sharedEndpointShoreEdgePairFinset_card_of_incident_three
#print axioms Erdos85.h305_correctShoreMode_incident_three
#print axioms Erdos85.h305_sharedEndpointShoreEdgePairFinset_card_twentyFour
