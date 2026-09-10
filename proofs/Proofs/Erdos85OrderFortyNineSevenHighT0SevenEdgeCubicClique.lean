import Proofs.Erdos85OrderFortyNineSevenHighT0ExteriorCapacityInequality
import Proofs.Erdos85ForbiddenPairsBound

/-! In the seven-edge H7 empty graph, distinct cubic vertices are adjacent.
Two nonadjacent cubic roots give six distinct forbidden pairs on their
five-vertex complement, contradicting the actual exterior edge bound. -/
namespace Erdos85
open SimpleGraph
noncomputable section

private theorem induced_neighbor_count_eq_inter
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (E : Finset V)
    (w : (↑E : Set V)) :
    ((G.induce (↑E : Set V)).neighborFinset w).card =
      (G.neighborFinset w.val ∩ E).card := by
  classical
  apply Finset.card_bij (fun x _ => x.val)
  · intro x hx
    exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr
      (((G.induce (↑E : Set V)).mem_neighborFinset _ _).mp hx), x.property⟩
  · intro x hx y hy hxy
    exact Subtype.ext hxy
  · intro x hx
    refine ⟨⟨x, (Finset.mem_inter.mp hx).2⟩, ?_, rfl⟩
    exact ((G.induce (↑E : Set V)).mem_neighborFinset _ _).mpr
      ((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hx).1)

theorem sevenHigh_t0_seven_empty_edges_cubic_adj_cubic
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (ha : sevenHighT0InternalEdgeCount G 0 = 7)
    (u v : (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49)))
    (huv : u ≠ v)
    (hu : (G.neighborFinset u.val ∩ sevenHighT0LowSupportFiber G 0).card = 3)
    (hv : (G.neighborFinset v.val ∩ sevenHighT0LowSupportFiber G 0).card = 3) :
    G.Adj u.val v.val := by
  classical
  by_contra hnot
  let E := sevenHighT0LowSupportFiber G 0
  let A := G.induce (↑E : Set (Fin 49))
  let F := insideCommonFreeGraph G E
  let U : Finset (↑E : Set (Fin 49)) := {u, v}
  have hnc (w : (↑E : Set (Fin 49))) :
      (A.neighborFinset w).card = (G.neighborFinset w.val ∩ E).card := by
    exact induced_neighbor_count_eq_inter G E w
  obtain ⟨a, b, c, hab, hac, hbc, hNu⟩ := Finset.card_eq_three.mp ((hnc u).trans hu)
  obtain ⟨d, e, f, hde, hdf, hef, hNv⟩ := Finset.card_eq_three.mp ((hnc v).trans hv)
  have hua : A.Adj u a := by apply (A.mem_neighborFinset _ _).mp; rw [hNu]; simp
  have hub : A.Adj u b := by apply (A.mem_neighborFinset _ _).mp; rw [hNu]; simp
  have huc : A.Adj u c := by apply (A.mem_neighborFinset _ _).mp; rw [hNu]; simp
  have hvd : A.Adj v d := by apply (A.mem_neighborFinset _ _).mp; rw [hNv]; simp
  have hve : A.Adj v e := by apply (A.mem_neighborFinset _ _).mp; rw [hNv]; simp
  have hvf : A.Adj v f := by apply (A.mem_neighborFinset _ _).mp; rw [hNv]; simp
  have hAU : ∀ x, A.Adj u x → x ∉ U := by
    intro x hx hm
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact hx.ne rfl
    · exact hnot hx
  have hVU : ∀ x, A.Adj v x → x ∉ U := by
    intro x hx hm
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact hnot hx.symm
    · exact hx.ne rfl
  have hpair (x y w : (↑E : Set (Fin 49))) (hxy : x ≠ y)
      (hwx : A.Adj w x) (hwy : A.Adj w y) (hxU : x ∉ U) (hyU : y ∉ U) :
      ¬ s(x,y).IsDiag ∧ s(x,y) ∉ F.edgeFinset ∧ ∀ z ∈ U, z ∉ s(x,y) := by
    refine ⟨by simpa only [Sym2.mk_isDiag_iff] using hxy, ?_, ?_⟩
    · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      intro h
      exact h.2 w ⟨hwx.symm, hwy.symm⟩
    · intro z hz hm
      rcases Sym2.mem_iff.mp hm with h | h
      · exact hxU (h ▸ hz)
      · exact hyU (h ▸ hz)
  have hcross (x y p q : (↑E : Set (Fin 49))) (hxy : x ≠ y)
      (hux : A.Adj u x) (huy : A.Adj u y)
      (hvp : A.Adj v p) (hvq : A.Adj v q) : s(x,y) ≠ s(p,q) := by
    intro h
    have hvx : A.Adj v x := by
      rcases Sym2.eq_iff.mp h with hh | hh
      · rw [hh.1]; exact hvp
      · rw [hh.1]; exact hvq
    have hvy : A.Adj v y := by
      rcases Sym2.eq_iff.mp h with hh | hh
      · rw [hh.2]; exact hvq
      · rw [hh.2]; exact hvp
    have hc := (not_containsC4_iff_forall_common_le_one A).mp
      (not_containsC4_induce_finset G hfree E) u v huv
    have hx : x ∈ A.neighborFinset u ∩ A.neighborFinset v :=
      Finset.mem_inter.mpr ⟨(A.mem_neighborFinset _ _).mpr hux, (A.mem_neighborFinset _ _).mpr hvx⟩
    have hy : y ∈ A.neighborFinset u ∩ A.neighborFinset v :=
      Finset.mem_inter.mpr ⟨(A.mem_neighborFinset _ _).mpr huy, (A.mem_neighborFinset _ _).mpr hvy⟩
    exact hxy (Finset.card_le_one.mp hc x hx y hy)
  have h12 : s(a,b) ≠ s(a,c) := by simp [Sym2.eq_iff, hab, hac, hbc, hab.symm]
  have h13 : s(a,b) ≠ s(b,c) := by simp [Sym2.eq_iff, hab, hac, hbc]
  have h23 : s(a,c) ≠ s(b,c) := by simp [Sym2.eq_iff, hab, hac, hbc]
  have h14 := hcross a b d e hab hua hub hvd hve
  have h15 := hcross a b d f hab hua hub hvd hvf
  have h16 := hcross a b e f hab hua hub hve hvf
  have h24 := hcross a c d e hac hua huc hvd hve
  have h25 := hcross a c d f hac hua huc hvd hvf
  have h26 := hcross a c e f hac hua huc hve hvf
  have h34 := hcross b c d e hbc hub huc hvd hve
  have h35 := hcross b c d f hbc hub huc hvd hvf
  have h36 := hcross b c e f hbc hub huc hve hvf
  have h45 : s(d,e) ≠ s(d,f) := by simp [Sym2.eq_iff, hde, hdf, hef, hde.symm]
  have h46 : s(d,e) ≠ s(e,f) := by simp [Sym2.eq_iff, hde, hdf, hef]
  have h56 : s(d,f) ≠ s(e,f) := by simp [Sym2.eq_iff, hde, hdf, hef]
  let B : Finset (Sym2 (↑E : Set (Fin 49))) := {s(a,b), s(a,c), s(b,c), s(d,e), s(d,f), s(e,f)}
  have hB : ∀ p ∈ B, ¬ p.IsDiag ∧ p ∉ F.edgeFinset ∧ ∀ z ∈ U, z ∉ p := by
    intro p hp
    simp only [B, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hpair a b u hab hua hub (hAU a hua) (hAU b hub)
    · exact hpair a c u hac hua huc (hAU a hua) (hAU c huc)
    · exact hpair b c u hbc hub huc (hAU b hub) (hAU c huc)
    · exact hpair d e v hde hvd hve (hVU d hvd) (hVU e hve)
    · exact hpair d f v hdf hvd hvf (hVU d hvd) (hVU f hvf)
    · exact hpair e f v hef hve hvf (hVU e hve) (hVU f hvf)
  have hBcard : B.card = 6 := by
    simp only [B, Finset.card_insert_eq_ite, Finset.mem_insert, Finset.mem_singleton, h12, h13, h14, h15, h16,
      h23, h24, h25, h26, h34, h35, h36, h45, h46, h56,
      false_or, if_false, Finset.card_singleton]
  have hupper := edges_avoiding_subset_add_forbidden_card_le_choose F U B hB
  have hcensus := sevenHigh_t0_global_incidence G hfree hmin hHigh hzero
  have hE : E.card = 7 := by
    simpa [E, sevenHighT0LowSupportFiber, orderFortyNineHighSupport,
      orderFortyNineHighIncidenceCount] using hcensus.1
  have hcard : Fintype.card (↑E : Set (Fin 49)) = 7 := by simpa using hE
  have hU : U.card = 2 := by simp [U, huv]
  rw [hcard, hU, hBcard, show Nat.choose (7 - 2) 2 = 10 from by decide] at hupper
  have hsmall : (F.edgeFinset.filter (fun p => ∀ z ∈ U, z ∉ p)).card ≤ 4 := by omega
  have hsum : (∑ z ∈ U, (7 - 2 * (G.neighborFinset z.val ∩ E).card)) = 2 := by
    simp [U, huv, E, hu, hv]
  have h := sevenHigh_t0_vertex_subset_exterior_capacity_inequality G hfree hmin hHigh hzero U
  change 35 ≤ 4 * sevenHighT0InternalEdgeCount G 0 +
    (∑ z ∈ U, (7 - 2 * (G.neighborFinset z.val ∩ E).card)) +
    (F.edgeFinset.filter (fun p => ∀ z ∈ U, z ∉ p)).card at h
  rw [ha, hsum] at h
  have hfinal := h.trans (Nat.add_le_add_left hsmall (4 * 7 + 2))
  norm_num at hfinal

end
end Erdos85
#print axioms Erdos85.sevenHigh_t0_seven_empty_edges_cubic_adj_cubic
