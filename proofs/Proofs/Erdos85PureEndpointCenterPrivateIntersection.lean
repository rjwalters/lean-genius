import Proofs.Erdos85PureEndpointCenterGraphShape

/-!
# Full centers inside the private-point transversal

At the pure endpoint the replication cap makes every private point unique
for its center.  Consequently the full centers which themselves occur in
the canonical private-point transversal are exactly the degree-one vertices
of the graph induced by the full centers.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Under the endpoint line axioms, two points private to the same line are
equal. -/
theorem privateNeighbor_eq_of_endpointProfile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (E : Finset V) (hEcard : E.card = q)
    (hline : ∀ i ∈ E, G.degree i = q)
    (hpair : ∀ i ∈ E, ∀ j ∈ E, i ≠ j →
      (G.neighborFinset i ∩ G.neighborFinset j).card = 1)
    (hcap : ∀ x, (G.neighborFinset x ∩ E).card ≤ 2)
    (i : {i // i ∈ E}) {x y : V}
    (hx : G.Adj i.1 x) (hxPrivate : G.neighborFinset x ∩ E = {i.1})
    (hy : G.Adj i.1 y) (hyPrivate : G.neighborFinset y ∩ E = {i.1}) :
    x = y := by
  classical
  let I := {i // i ∈ E}
  let L : I → Finset V := fun j => G.neighborFinset j.1
  have hindex : Fintype.card I = q := by simpa [I] using hEcard
  have hline' : ∀ j, (L j).card = q := by
    intro j
    rw [show L j = G.neighborFinset j.1 by rfl,
      G.card_neighborFinset_eq_degree, hline j.1 j.2]
  have hpair' : ∀ j k, j ≠ k → (L j ∩ L k).card = 1 := by
    intro j k hjk
    exact hpair j.1 j.2 k.1 k.2 (fun h => hjk (Subtype.ext h))
  have htriple : ∀ z j k l, z ∈ L j → z ∈ L k → z ∈ L l →
      j = k ∨ j = l ∨ k = l := by
    intro z j k l hzj hzk hzl
    by_contra h
    push Not at h
    have hsub : ({j.1, k.1, l.1} : Finset V) ⊆
        G.neighborFinset z ∩ E := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact Finset.mem_inter.mpr ⟨by
          simpa [L, SimpleGraph.mem_neighborFinset, G.adj_comm] using hzj, j.2⟩
      · exact Finset.mem_inter.mpr ⟨by
          simpa [L, SimpleGraph.mem_neighborFinset, G.adj_comm] using hzk, k.2⟩
      · exact Finset.mem_inter.mpr ⟨by
          simpa [L, SimpleGraph.mem_neighborFinset, G.adj_comm] using hzl, l.2⟩
    have hdistinct : j.1 ≠ k.1 ∧ j.1 ≠ l.1 ∧ k.1 ≠ l.1 := by
      exact ⟨fun hjk => h.1 (Subtype.ext hjk),
        fun hjl => h.2.1 (Subtype.ext hjl),
        fun hkl => h.2.2 (Subtype.ext hkl)⟩
    have hthree : ({j.1, k.1, l.1} : Finset V).card = 3 := by
      simp [hdistinct.1, hdistinct.2.1, hdistinct.2.2]
    have hle := Finset.card_le_card hsub
    rw [hthree] at hle
    have hcapz := hcap z
    exact (by omega : False)
  have hone : (partialBaerPrivatePoints L i).card = 1 :=
    partialBaer_privatePoints_card_eq_one L hindex hline' hpair' htriple i
  have hmem : ∀ {z : V}, G.Adj i.1 z →
      G.neighborFinset z ∩ E = {i.1} →
      z ∈ partialBaerPrivatePoints L i := by
    intro z hiz hzPrivate
    apply Finset.mem_sdiff.mpr
    constructor
    · simpa [L, SimpleGraph.mem_neighborFinset] using hiz
    · intro hzUnion
      obtain ⟨j, hjErase, hzInter⟩ := Finset.mem_biUnion.mp hzUnion
      have hjData := Finset.mem_erase.mp hjErase
      have hzLj := (Finset.mem_inter.mp hzInter).2
      have hjMem : j.1 ∈ G.neighborFinset z ∩ E :=
        Finset.mem_inter.mpr ⟨by
          simpa [L, SimpleGraph.mem_neighborFinset, G.adj_comm] using hzLj, j.2⟩
      rw [hzPrivate] at hjMem
      have hji : j = i := Subtype.ext (Finset.mem_singleton.mp hjMem)
      exact hjData.1 hji
  have hxm := hmem hx hxPrivate
  have hym := hmem hy hyPrivate
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hone
  rw [hz] at hxm hym
  exact (Finset.mem_singleton.mp hxm).trans (Finset.mem_singleton.mp hym).symm

/-- At the pure endpoint, one may choose the private matching so that its
intersection with the full-center family is exactly the degree-one stratum
of the induced center graph. -/
theorem c4Free_binarySquare_pureEndpoint_center_mem_privateRange_iff_degree_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    ∃ p : {i // i ∈ fullLineCenters G S q} → V,
      Function.Injective p ∧
      (∀ i, G.Adj i.1 (p i) ∧
        G.neighborFinset (p i) ∩ fullLineCenters G S q = {i.1}) ∧
      ∀ v ∈ fullLineCenters G S q,
        v ∈ (Finset.univ.image p) ↔
          (G.neighborFinset v ∩ fullLineCenters G S q).card = 1 := by
  classical
  let C := fullLineCenters G S q
  have hs :=
    c4Free_binarySquare_pureEndpoint_fullLineCenters_structure_withReplicationCap
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  obtain ⟨hDindependent, hcap, p, hpInjective, hp⟩ := hs
  have hpair : ∀ i ∈ C, ∀ j ∈ C, i ≠ j →
      (G.neighborFinset i ∩ G.neighborFinset j).card = 1 := by
    intro i hi j hj hij
    have hnotMem : j ∉ (secondOrderDefectGraph G).neighborFinset i := by
      simpa [SimpleGraph.mem_neighborFinset] using
        hDindependent i hi j hj hij
    have hcommon := card_common_eq_if_secondOrderDefect G hfree i j hij
    rw [if_neg hnotMem] at hcommon
    exact hcommon
  refine ⟨p, hpInjective, hp, ?_⟩
  intro v hvC
  constructor
  · intro hvRange
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hvRange
    rw [(hp i).2]
    simp
  · intro hvOne
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hvOne
    have hiC : i ∈ C := by
      have : i ∈ G.neighborFinset v ∩ C := by rw [hi]; simp
      exact (Finset.mem_inter.mp this).2
    let ii : {i // i ∈ C} := ⟨i, hiC⟩
    have hvi : G.Adj ii.1 v := by
      have : i ∈ G.neighborFinset v ∩ C := by rw [hi]; simp
      simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using
        (Finset.mem_inter.mp this).1
    have hvPrivate : G.neighborFinset v ∩ C = {ii.1} := by simpa [ii] using hi
    have hvp : v = p ii := privateNeighbor_eq_of_endpointProfile
      G C (by simpa [C] using hCcard) (fun x _ => hreg x)
      hpair hcap ii hvi hvPrivate (hp ii).1 (hp ii).2
    apply Finset.mem_image.mpr
    exact ⟨ii, Finset.mem_univ ii, hvp.symm⟩

end

end Erdos85

#print axioms Erdos85.privateNeighbor_eq_of_endpointProfile
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_center_mem_privateRange_iff_degree_one
