import Proofs.Erdos85OrderFortyNineSevenHighT0ExteriorCapacityInequality
import Proofs.Erdos85TwoForbiddenPairsBound

/-! A six-edge H7 empty graph has at most one cubic vertex. -/
namespace Erdos85
open SimpleGraph
noncomputable section

private theorem cubic_has_two_neighbors_avoiding
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (E : Finset V)
    (u v : (↑E : Set V))
    (hu : (G.neighborFinset u.val ∩ E).card = 3) :
    ∃ a b : (↑E : Set V), a ≠ b ∧ a ≠ u ∧ a ≠ v ∧ b ≠ u ∧ b ≠ v ∧
      G.Adj u.val a.val ∧ G.Adj u.val b.val := by
  classical
  have hc := Finset.pred_card_le_card_erase (s := G.neighborFinset u.val ∩ E) (a := v.val)
  rw [hu] at hc
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show
      1 < ((G.neighborFinset u.val ∩ E).erase v.val).card by omega)
  have pa := Finset.mem_erase.mp ha
  have pb := Finset.mem_erase.mp hb
  have hua := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp pa.2).1
  have hub := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp pb.2).1
  refine ⟨⟨a, (Finset.mem_inter.mp pa.2).2⟩,
    ⟨b, (Finset.mem_inter.mp pb.2).2⟩, ?_, ?_, ?_, ?_, ?_, hua, hub⟩
  · exact fun h => hab (congrArg Subtype.val h)
  · exact fun h => hua.ne (congrArg Subtype.val h).symm
  · exact fun h => pa.1 (congrArg Subtype.val h)
  · exact fun h => hub.ne (congrArg Subtype.val h).symm
  · exact fun h => pb.1 (congrArg Subtype.val h)

theorem sevenHigh_t0_six_empty_edges_no_two_cubic
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (ha : sevenHighT0InternalEdgeCount G 0 = 6)
    (u v : (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49)))
    (huv : u ≠ v)
    (hu : (G.neighborFinset u.val ∩ sevenHighT0LowSupportFiber G 0).card = 3)
    (hv : (G.neighborFinset v.val ∩ sevenHighT0LowSupportFiber G 0).card = 3) : False := by
  classical
  let E := sevenHighT0LowSupportFiber G 0
  let F := insideCommonFreeGraph G E
  let U : Finset (↑E : Set (Fin 49)) := {u, v}
  obtain ⟨a, b, hab, hau, hav, hbu, hbv, hua, hub⟩ := cubic_has_two_neighbors_avoiding G E u v hu
  obtain ⟨c, d, hcd, hcv, hcu, hdv, hdu, hvc, hvd⟩ := cubic_has_two_neighbors_avoiding G E v u hv
  have hef : s(a, b) ≠ s(c, d) := by
    intro heq
    have hva : G.Adj v.val a.val := by
      rcases Sym2.eq_iff.mp heq with h | h
      · rw [h.1]; exact hvc
      · rw [h.1]; exact hvd
    have hvb : G.Adj v.val b.val := by
      rcases Sym2.eq_iff.mp heq with h | h
      · rw [h.2]; exact hvd
      · rw [h.2]; exact hvc
    have hc := (not_containsC4_iff_forall_common_le_one G).mp hfree
      u.val v.val (fun h => huv (Subtype.ext h))
    have ham : a.val ∈ G.neighborFinset u.val ∩ G.neighborFinset v.val := by
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hua, (G.mem_neighborFinset _ _).mpr hva⟩
    have hbm : b.val ∈ G.neighborFinset u.val ∩ G.neighborFinset v.val := by
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hub, (G.mem_neighborFinset _ _).mpr hvb⟩
    exact hab (Subtype.ext (Finset.card_le_one.mp hc a.val ham b.val hbm))
  have heG : s(a, b) ∉ F.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    intro h
    exact h.2 u ⟨hua.symm, hub.symm⟩
  have hfG : s(c, d) ∉ F.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    intro h
    exact h.2 v ⟨hvc.symm, hvd.symm⟩
  have heU : ∀ x ∈ U, x ∉ s(a, b) := by
    simp [U, Sym2.mem_iff, hau.symm, hav.symm, hbu.symm, hbv.symm]
  have hfU : ∀ x ∈ U, x ∉ s(c, d) := by
    simp [U, Sym2.mem_iff, hcu.symm, hcv.symm, hdu.symm, hdv.symm]
  have hupper := edges_avoiding_subset_add_two_le_choose F U s(a,b) s(c,d) hef
    (by simpa only [Sym2.mk_isDiag_iff] using hab)
    (by simpa only [Sym2.mk_isDiag_iff] using hcd) heG hfG heU hfU
  have hcensus := sevenHigh_t0_global_incidence G hfree hmin hHigh hzero
  have hE : E.card = 7 := by
    simpa [E, sevenHighT0LowSupportFiber, orderFortyNineHighSupport,
      orderFortyNineHighIncidenceCount] using hcensus.1
  have hcard : Fintype.card (↑E : Set (Fin 49)) = 7 := by simpa using hE
  have hU : U.card = 2 := by simp [U, huv]
  rw [hcard, hU, show Nat.choose (7 - 2) 2 = 10 from by decide] at hupper
  have hsmall : (F.edgeFinset.filter (fun e => ∀ w ∈ U, w ∉ e)).card ≤ 8 := by omega
  have hsum : (∑ w ∈ U, (7 - 2 * (G.neighborFinset w.val ∩ E).card)) = 2 := by
    simp [U, huv, E, hu, hv]
  have h := sevenHigh_t0_vertex_subset_exterior_capacity_inequality
    G hfree hmin hHigh hzero U
  change 35 ≤ 4 * sevenHighT0InternalEdgeCount G 0 +
    (∑ w ∈ U, (7 - 2 * (G.neighborFinset w.val ∩ E).card)) +
    (F.edgeFinset.filter (fun e => ∀ w ∈ U, w ∉ e)).card at h
  rw [ha, hsum] at h
  have hfinal := h.trans (Nat.add_le_add_left hsmall (4 * 6 + 2))
  norm_num at hfinal

theorem sevenHigh_t0_six_empty_edges_cubic_count_le_one
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (ha : sevenHighT0InternalEdgeCount G 0 = 6) :
    (Finset.univ.filter fun v : (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49)) =>
      (G.neighborFinset v.val ∩ sevenHighT0LowSupportFiber G 0).card = 3).card ≤ 1 := by
  classical
  by_contra h
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (show 1 <
      (Finset.univ.filter fun v : (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49)) =>
        (G.neighborFinset v.val ∩ sevenHighT0LowSupportFiber G 0).card = 3).card by omega)
  exact sevenHigh_t0_six_empty_edges_no_two_cubic G hfree hmin hHigh hzero ha u v huv
    (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2

end
end Erdos85
#print axioms Erdos85.sevenHigh_t0_six_empty_edges_no_two_cubic
#print axioms Erdos85.sevenHigh_t0_six_empty_edges_cubic_count_le_one
