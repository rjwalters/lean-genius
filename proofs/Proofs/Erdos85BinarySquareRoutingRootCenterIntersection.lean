import Proofs.Erdos85BinarySquareRoutingRowDensityResidualStars

/-! # Cross-root compatibility of routing centers -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Local restricted-cherry pigeonhole lemma.  Kept here so the routing
algebra does not depend on the much later degree-sixteen terminal file where
the same general counting device was first introduced. -/
private theorem containsC4_of_restricted_cherry_count_routing
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
    (h : B.card.choose 2 <
      ∑ a ∈ A, ((B ∩ G.neighborFinset a).card).choose 2) :
    containsC4 V G := by
  classical
  let C : Finset (Σ _ : V, Finset V) :=
    A.sigma fun a => (B ∩ G.neighborFinset a).powersetCard 2
  let T : Finset (Finset V) := B.powersetCard 2
  have hCcard : C.card =
      ∑ a ∈ A, ((B ∩ G.neighborFinset a).card).choose 2 := by
    dsimp [C]
    rw [Finset.card_sigma]
    simp only [Finset.card_powersetCard]
  have hTcard : T.card = B.card.choose 2 := by
    simp [T]
  have hmaps : ∀ p ∈ C, p.2 ∈ T := by
    intro p hp
    simp only [C, Finset.mem_sigma] at hp
    simp only [T, Finset.mem_powersetCard]
    have hpData := Finset.mem_powersetCard.mp hp.2
    exact ⟨hpData.1.trans Finset.inter_subset_left, hpData.2⟩
  have hlt : T.card < C.card := by rw [hTcard, hCcard]; exact h
  obtain ⟨p, hp, q, hq, hpq, hfe⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  obtain ⟨v, e⟩ := p
  obtain ⟨v', e'⟩ := q
  simp only at hfe
  subst hfe
  have hvv : v ≠ v' := by
    rintro rfl
    exact hpq rfl
  simp only [C, Finset.mem_sigma] at hp hq
  obtain ⟨-, hpe⟩ := hp
  obtain ⟨-, hqe⟩ := hq
  obtain ⟨hsubv, hecard⟩ := Finset.mem_powersetCard.mp hpe
  obtain ⟨hsubv', -⟩ := Finset.mem_powersetCard.mp hqe
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hecard
  have hxMem : x ∈ ({x, y} : Finset V) := Finset.mem_insert_self x {y}
  have hyMem : y ∈ ({x, y} : Finset V) := by simp
  have hxvData := Finset.mem_inter.mp (hsubv hxMem)
  have hyvData := Finset.mem_inter.mp (hsubv hyMem)
  have hxv'Data := Finset.mem_inter.mp (hsubv' hxMem)
  have hyv'Data := Finset.mem_inter.mp (hsubv' hyMem)
  have avx : G.Adj v x := (G.mem_neighborFinset v x).mp hxvData.2
  have avy : G.Adj v y := (G.mem_neighborFinset v y).mp hyvData.2
  have av'x : G.Adj v' x := (G.mem_neighborFinset v' x).mp hxv'Data.2
  have av'y : G.Adj v' y := (G.mem_neighborFinset v' y).mp hyv'Data.2
  exact containsC4_of_two_common (x := v) (y := v') (v := x) (v' := y)
    hvv hxy avx.symm av'x.symm avy.symm av'y.symm

/-- Distinct roots in one defect component share at most one center of any
fixed owner color.  Two shared centers would form a four-cycle with the two
roots.  This is the basic cross-root compatibility law for the canonical
routing-row star decompositions. -/
theorem componentCrossNeighborFinset_inter_card_le_one_of_distinct_roots
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {source owner : (secondOrderDefectGraph G).ConnectedComponent}
    (x x' : source.supp) (hxx' : x ≠ x') :
    (componentCrossNeighborFinset G owner x ∩
      componentCrossNeighborFinset G owner x').card ≤ 1 := by
  classical
  by_contra hle
  have hlt : 1 < (componentCrossNeighborFinset G owner x ∩
      componentCrossNeighborFinset G owner x').card := by omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hlt
  have huData := Finset.mem_inter.mp hu
  have hvData := Finset.mem_inter.mp hv
  have hxu : G.Adj x.1 u.1 := (Finset.mem_filter.mp huData.1).2
  have hx'u : G.Adj x'.1 u.1 := (Finset.mem_filter.mp huData.2).2
  have hxv : G.Adj x.1 v.1 := (Finset.mem_filter.mp hvData.1).2
  have hx'v : G.Adj x'.1 v.1 := (Finset.mem_filter.mp hvData.2).2
  have hxxVal : x.1 ≠ x'.1 := by
    intro heq
    exact hxx' (Subtype.ext heq)
  have huvVal : u.1 ≠ v.1 := by
    intro heq
    exact huv (Subtype.ext heq)
  exact hfree (containsC4_of_two_common hxxVal huvVal
    hxu.symm hx'u.symm hxv.symm hx'v.symm)

/-- Restricted cherry packing for a normalized component-incidence block.
Every root in `source` selects exactly `m owner` centers in `owner`; C4-freeness
makes the resulting unordered center-pairs distinct across roots. -/
theorem binarySquare_regular_componentIncidence_cherry_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = q * m d)
    (source owner : (secondOrderDefectGraph G).ConnectedComponent) :
    q * m source * (m owner).choose 2 ≤
      (q * m owner).choose 2 := by
  classical
  let D := secondOrderDefectGraph G
  let A : Finset V := source.supp.toFinite.toFinset
  let B : Finset V := owner.supp.toFinite.toFinset
  have hdegree : ∀ x ∈ A,
      (B ∩ G.neighborFinset x).card = m owner := by
    intro x hx
    have hxSource : x ∈ source.supp := by simpa [A] using hx
    have heq : B ∩ G.neighborFinset x = componentNeighborFinset G D owner x := by
      ext y
      simp [B, D, componentNeighborFinset,
        SimpleGraph.ConnectedComponent.mem_supp_iff, and_comm]
    rw [heq]
    have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree hq hreg hcard source owner (x := x) hxSource
    rw [hm owner] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul
  have hAcard : A.card = q * m source := by
    simpa [A, hm source] using
      (Set.ncard_eq_toFinset_card source.supp source.supp.toFinite).symm
  have hBcard : B.card = q * m owner := by
    simpa [B, hm owner] using
      (Set.ncard_eq_toFinset_card owner.supp owner.supp.toFinite).symm
  by_contra hle
  apply hfree
  apply containsC4_of_restricted_cherry_count_routing G A B
  push Not at hle
  rw [hBcard]
  calc
    (q * m owner).choose 2 <
        q * m source * (m owner).choose 2 := hle
    _ = A.card * (m owner).choose 2 := by rw [hAcard]
    _ = ∑ x ∈ A, (m owner).choose 2 := by simp
    _ = ∑ x ∈ A, ((B ∩ G.neighborFinset x).card).choose 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hdegree x hx]

end

end Erdos85

#print axioms Erdos85.componentCrossNeighborFinset_inter_card_le_one_of_distinct_roots
#print axioms Erdos85.binarySquare_regular_componentIncidence_cherry_bound
