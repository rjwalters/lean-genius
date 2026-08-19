import Proofs.Erdos85SizeTwoEigenlineSixTenShortCycleRigidity
import Proofs.Erdos85DefectCycleBlock

/-!
# Cross-block periodicity in the q=8 six-plus-ten stratum

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The internal ambient graph and the induced second-order defect graph commute.
After cyclically parametrizing internal components of orders six and ten, the
rectangular defect block therefore has period ten in the six-coordinate and
period six in the ten-coordinate.  Equivalently, both periods reduce to the
two-step parity classes.  This is the graph-facing input for the checkerboard
classification of the `6 × 10` block.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Cyclic coordinates on the `6+10` internal components in which the cross
defect block is periodic in both coordinates by the opposite cycle length. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_crossDefect_periodic
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
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10) :
    ∃ (xa xb : c.supp)
      (p : (G.induce c.supp).Walk xa xa)
      (r : (G.induce c.supp).Walk xb xb)
      (u : ZMod p.length → c.supp) (v : ZMod r.length → c.supp),
      p.IsCycle ∧ r.IsCycle ∧ p.length = 6 ∧ r.length = 10 ∧
      Function.Injective u ∧ Function.Injective v ∧
      Set.range u = a.supp ∧ Set.range v = b.supp ∧
      (∀ z, (G.induce c.supp).neighborFinset (u z) =
        {u (z - 1), u (z + 1)}) ∧
      (∀ z, (G.induce c.supp).neighborFinset (v z) =
        {v (z - 1), v (z + 1)}) ∧
      (∀ i j,
        ((secondOrderDefectGraph G).induce c.supp).Adj
            (u (i + r.length • (1 : ZMod p.length))) (v j) ↔
          ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (v j)) ∧
      (∀ i j,
        ((secondOrderDefectGraph G).induce c.supp).Adj
            (u i) (v (j + p.length • (1 : ZMod r.length))) ↔
          ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (v j)) := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  obtain ⟨xa, p, hp, hpverts, _hpgraph, _hp4, _hpnonwrap⟩ :=
    binarySquare_regular_sizeTwoPart_exists_cycle_of_internalComponent
      G hfree (by omega) hreg hcard c hc a
  obtain ⟨xb, r, hr, hrverts, _hrgraph, _hr4, _hrnonwrap⟩ :=
    binarySquare_regular_sizeTwoPart_exists_cycle_of_internalComponent
      G hfree (by omega) hreg hcard c hc b
  have hplen : p.length = 6 := by
    calc
      p.length = Nat.card p.toSubgraph.verts :=
        (isCycle_card_verts_eq_length hp).symm
      _ = p.toSubgraph.verts.ncard := Nat.card_coe_set_eq _
      _ = a.supp.ncard := congrArg Set.ncard hpverts
      _ = 6 := ha
  have hrlen : r.length = 10 := by
    calc
      r.length = Nat.card r.toSubgraph.verts :=
        (isCycle_card_verts_eq_length hr).symm
      _ = r.toSubgraph.verts.ncard := Nat.card_coe_set_eq _
      _ = b.supp.ncard := congrArg Set.ncard hrverts
      _ = 10 := hb
  obtain ⟨hHdegree, _hKdegree, hcommHK⟩ :=
    binarySquare_regular_sizeTwoPart_commuting_regular_blocks
      G hfree (by omega) hreg hcard c hc
  have hcommKH : K.adjMatrix ℤ * H.adjMatrix ℤ =
      H.adjMatrix ℤ * K.adjMatrix ℤ := by
    simpa [K, H] using hcommHK.symm
  obtain ⟨u, v, huinj, hvinj, hurange, hvrange, hu, hv, hrow⟩ :=
    exists_cycleBlock_targetLength_periodic K H hcommKH hHdegree hp hr
  have hp3 : 3 ≤ p.length := hp.three_le_length
  have hr3 : 3 ≤ r.length := hr.three_le_length
  letI : NeZero p.length := ⟨by omega⟩
  letI : NeZero r.length := ⟨by omega⟩
  have hupair : ∀ z : ZMod p.length, u (z - 1) ≠ u (z + 1) := by
    intro z heq
    have hz : z - 1 = z + 1 := huinj heq
    have htwo : (2 : ZMod p.length) = 0 := by
      calc
        (2 : ZMod p.length) = (z + 1) - (z - 1) := by ring
        _ = 0 := by rw [← hz]; simp
    have hdvd : p.length ∣ 2 :=
      (ZMod.natCast_eq_zero_iff 2 p.length).mp htwo
    exact (not_le_of_gt hp3) (Nat.le_of_dvd (by norm_num) hdvd)
  have hvpair : ∀ z : ZMod r.length, v (z - 1) ≠ v (z + 1) := by
    intro z heq
    have hz : z - 1 = z + 1 := hvinj heq
    have htwo : (2 : ZMod r.length) = 0 := by
      calc
        (2 : ZMod r.length) = (z + 1) - (z - 1) := by ring
        _ = 0 := by rw [← hz]; simp
    have hdvd : r.length ∣ 2 :=
      (ZMod.natCast_eq_zero_iff 2 r.length).mp htwo
    exact (not_le_of_gt hr3) (Nat.le_of_dvd (by norm_num) hdvd)
  have hinterSwap := entry_cycleIntertwine_of_adjMatrix_comm
    K H v u (1 : ZMod r.length) (1 : ZMod p.length)
      hcommKH hv hu hvpair hupair
  have hcol : ∀ i j,
      K.Adj (u i) (v (j + p.length • (1 : ZMod r.length))) ↔
        K.Adj (u i) (v j) := by
    intro i j
    have hperiod := adj_iff_add_targetOrder_of_entry_cycleIntertwine
      K v u (1 : ZMod r.length) (1 : ZMod p.length) hinterSwap j i
    simpa only [ZMod.addOrderOf_one, K.adj_comm] using hperiod
  refine ⟨xa, xb, p, r, u, v, hp, hr, hplen, hrlen, huinj, hvinj,
    ?_, ?_, hu, hv, hrow, hcol⟩
  · exact hurange.trans hpverts
  · exact hvrange.trans hrverts

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_crossDefect_periodic
