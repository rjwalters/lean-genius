import Proofs.Erdos85SizeTwoEigenlineInternalCycleSectorDichotomy
import Proofs.Erdos85SizeTwoEigenlineSixTenCycleQuotient

/-!
# Sharpened diagonal bound for an all-triangle internal cycle

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The general cycle diagonal bound removes the vertex itself and its two
distance-two vertices.  In an all-triangle cycle, the two adjacent vertices
are not defect neighbors either.  Removing all five positions sharpens the
diagonal quotient bound from `r-3` to `r-5`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- An all-triangle internal cycle of order at least six has diagonal defect
quotient at most `r-5`. -/
theorem binarySquare_regular_sizeTwoPart_allTriangle_cycleQuotient_diagonal_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (a : (G.induce c.supp).ConnectedComponent) (ha : 6 ≤ a.supp.ncard)
    (hall : ∀ x : c.supp, x ∈ a.supp →
      (triangleFreeEdgeGraph G).degree x.1 = 0) :
    componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a ≤
      a.supp.ncard - 5 := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  obtain ⟨x, p, hp, hpverts, _hpgraph, _hlen4, hnonwrap⟩ :=
    binarySquare_regular_sizeTwoPart_exists_cycle_of_internalComponent
      G hfree hq hreg hcard c hc a
  have hplen : p.length = a.supp.ncard := by
    calc
      p.length = Nat.card p.toSubgraph.verts :=
        (isCycle_card_verts_eq_length hp).symm
      _ = p.toSubgraph.verts.ncard := Nat.card_coe_set_eq _
      _ = a.supp.ncard := congrArg Set.ncard hpverts
  let x0 : c.supp := p.getVert 0
  let w : c.supp := p.getVert 1
  let u : c.supp := p.getVert 2
  let v : c.supp := p.getVert (p.length - 2)
  let t : c.supp := p.getVert (p.length - 1)
  have hmem (i : ℕ) : p.getVert i ∈ a.supp := by
    rw [← hpverts]
    simpa only [Walk.mem_verts_toSubgraph] using p.getVert_mem_support i
  have hx0mem : x0 ∈ a.supp := hmem 0
  have hwmem : w ∈ a.supp := hmem 1
  have humem : u ∈ a.supp := hmem 2
  have hvmem : v ∈ a.supp := hmem (p.length - 2)
  have htmem : t ∈ a.supp := hmem (p.length - 1)
  have hget_ne (i j : ℕ) (hi : i < p.length) (hj : j < p.length)
      (hij : i ≠ j) : p.getVert i ≠ p.getVert j := by
    intro heq
    exact hij (hp.getVert_injOn'
      (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) heq)
  have hlen : 6 ≤ p.length := by omega
  have hnotU : ¬ K.Adj x0 u := hnonwrap 0 (by omega)
  have hnotV : ¬ K.Adj x0 v := by
    intro hxv
    exact (not_secondOrderDefect_adj_cycle_wraparound_distanceTwo G hfree hp).1
      hxv.symm
  have hadjXW : G.Adj x0.1 w.1 := by
    simpa [x0, w] using p.adj_getVert_succ (show 0 < p.length by omega)
  have hadjXT : G.Adj x0.1 t.1 := by
    have hlast := p.adj_getVert_succ
      (show p.length - 1 < p.length by omega)
    have hlastIndex : p.length - 1 + 1 = p.length := by omega
    simpa [x0, t, hlastIndex, p.getVert_length] using hlast.symm
  have noDefect_of_adj (y : c.supp) (hy : y ∈ a.supp)
      (hxy : G.Adj x0.1 y.1) : ¬ K.Adj x0 y := by
    intro hD
    have hD' : (secondOrderDefectGraph G).Adj x0.1 y.1 := by
      exact hD
    change (antipodalGraph G).Adj x0.1 y.1 ∨
      (triangleFreeEdgeGraph G).Adj x0.1 y.1 at hD'
    rcases hD' with hanti | htri
    · exact ((mem_antipodalNeighbors G x0.1 y.1).mp hanti).2.1 hxy
    · have hymem : y.1 ∈ (triangleFreeEdgeGraph G).neighborFinset x0.1 :=
        ((triangleFreeEdgeGraph G).mem_neighborFinset x0.1 y.1).mpr htri
      have hpos : 0 < (triangleFreeEdgeGraph G).degree x0.1 := by
        rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree]
        exact Finset.card_pos.mpr ⟨y.1, hymem⟩
      rw [hall x0 hx0mem] at hpos
      omega
  have hnotW : ¬ K.Adj x0 w := noDefect_of_adj w hwmem hadjXW
  have hnotT : ¬ K.Adj x0 t := noDefect_of_adj t htmem hadjXT
  have hxw : x0 ≠ w := hget_ne 0 1 (by omega) (by omega) (by omega)
  have hxu : x0 ≠ u := hget_ne 0 2 (by omega) (by omega) (by omega)
  have hxv : x0 ≠ v := hget_ne 0 (p.length - 2) (by omega) (by omega) (by omega)
  have hxt : x0 ≠ t := hget_ne 0 (p.length - 1) (by omega) (by omega) (by omega)
  have hwu : w ≠ u := hget_ne 1 2 (by omega) (by omega) (by omega)
  have hwv : w ≠ v := hget_ne 1 (p.length - 2) (by omega) (by omega) (by omega)
  have hwt : w ≠ t := hget_ne 1 (p.length - 1) (by omega) (by omega) (by omega)
  have huv : u ≠ v := hget_ne 2 (p.length - 2) (by omega) (by omega) (by omega)
  have hut : u ≠ t := hget_ne 2 (p.length - 1) (by omega) (by omega) (by omega)
  have hvt : v ≠ t := hget_ne (p.length - 2) (p.length - 1)
    (by omega) (by omega) (by omega)
  let S : Finset c.supp := a.supp.toFinite.toFinset
  let T : Finset c.supp := ((((S.erase x0).erase w).erase u).erase v).erase t
  have hsub : componentNeighborFinset K H a x0 ⊆ T := by
    intro z hz
    have hzData := Finset.mem_filter.mp hz
    have hzS : z ∈ S := by
      simp only [S, Set.Finite.mem_toFinset]
      exact (ConnectedComponent.mem_supp_iff a z).mpr hzData.2
    have hzx : z ≠ x0 := K.ne_of_adj
      ((K.mem_neighborFinset x0 z).mp hzData.1) |>.symm
    have hzw : z ≠ w := by
      intro h; subst z; exact hnotW ((K.mem_neighborFinset x0 w).mp hzData.1)
    have hzu : z ≠ u := by
      intro h; subst z; exact hnotU ((K.mem_neighborFinset x0 u).mp hzData.1)
    have hzv : z ≠ v := by
      intro h; subst z; exact hnotV ((K.mem_neighborFinset x0 v).mp hzData.1)
    have hzt : z ≠ t := by
      intro h; subst z; exact hnotT ((K.mem_neighborFinset x0 t).mp hzData.1)
    simp [T, hzS, hzx, hzw, hzu, hzv, hzt]
  have hTcard : T.card = a.supp.ncard - 5 := by
    have hxS : x0 ∈ S := by simpa [S] using hx0mem
    have hwS : w ∈ S := by simpa [S] using hwmem
    have huS : u ∈ S := by simpa [S] using humem
    have hvS : v ∈ S := by simpa [S] using hvmem
    have htS : t ∈ S := by simpa [S] using htmem
    have hwE : w ∈ S.erase x0 := Finset.mem_erase.mpr ⟨hxw.symm, hwS⟩
    have huE : u ∈ (S.erase x0).erase w := Finset.mem_erase.mpr
      ⟨hwu.symm, Finset.mem_erase.mpr ⟨hxu.symm, huS⟩⟩
    have hvE : v ∈ ((S.erase x0).erase w).erase u := Finset.mem_erase.mpr
      ⟨huv.symm, Finset.mem_erase.mpr ⟨hwv.symm,
        Finset.mem_erase.mpr ⟨hxv.symm, hvS⟩⟩⟩
    have htE : t ∈ (((S.erase x0).erase w).erase u).erase v :=
      Finset.mem_erase.mpr ⟨hvt.symm, Finset.mem_erase.mpr ⟨hut.symm,
        Finset.mem_erase.mpr ⟨hwt.symm,
          Finset.mem_erase.mpr ⟨hxt.symm, htS⟩⟩⟩⟩
    change (((((S.erase x0).erase w).erase u).erase v).erase t).card =
      a.supp.ncard - 5
    rw [Finset.card_erase_of_mem htE, Finset.card_erase_of_mem hvE,
      Finset.card_erase_of_mem huE, Finset.card_erase_of_mem hwE,
      Finset.card_erase_of_mem hxS]
    have hScard : S.card = a.supp.ncard :=
      (Set.ncard_eq_toFinset_card a.supp a.supp.toFinite).symm
    omega
  obtain ⟨hHdegree, _hKdegree, _hcommZ⟩ :=
    binarySquare_regular_sizeTwoPart_commuting_regular_blocks
      G hfree hq hreg hcard c hc
  have hcommReal : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm
      G (secondOrderDefectGraph G) hglobal c).symm
  rw [componentQuotientMatrix_apply_eq K H 2 hHdegree hcommReal a a hx0mem]
  exact (Finset.card_le_card hsub).trans_eq hTcard

/-- In the q=8 `6+10` stratum, the six-cycle is forced to be wholly
triangle-free: its exact diagonal quotient entry is two, while the sharpened
all-triangle bound would make it at most one. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_shortCycle_allTriangleFree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10) :
    ∀ x : c.supp, x ∈ a.supp →
      (triangleFreeEdgeGraph G).degree x.1 = 2 := by
  rcases binarySquare_regular_sizeTwoPart_internalCycle_sector_dichotomy
    G hfree (by omega) (by decide) hreg hcard c hc a with hall | htf
  · have hle :=
      binarySquare_regular_sizeTwoPart_allTriangle_cycleQuotient_diagonal_le
        G hfree (by omega) hreg hcard c hc a (by omega) hall
    have heq := binarySquare_regular_sizeTwoPart_eight_sixTen_cycleQuotient
      G hfree hreg hcard c hc s hs_in hs_out hA_in a b ha hb
    rw [heq.1, ha] at hle
    omega
  · exact htf

end


end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_allTriangle_cycleQuotient_diagonal_le
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_shortCycle_allTriangleFree
