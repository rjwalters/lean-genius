import Proofs.Erdos85OrderSixtyFourExteriorPairGraph

/-!
# Degree capacities in the exterior-pair graph

Reuse the existing exterior-pair graph. If its witnesses lie in S and
each S vertex has at most two E-neighbors, distinct exterior-pair neighbors
of a root require distinct S-neighbors of that root. C4-freeness also
forbids an inside common neighbor of an exterior-pair edge.
-/
namespace Erdos85
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

theorem exteriorPair_degree_le_routed_neighbor_count
    (G : SimpleGraph V) [DecidableRel G.Adj] (E S : Finset V)
    (hroute : ∀ (u v : (↑E : Set V)) (z : V), u ≠ v → z ∉ E →
      G.Adj u.val z → G.Adj v.val z → z ∈ S)
    (htwo : ∀ z ∈ S, (G.neighborFinset z ∩ E).card ≤ 2)
    (u : (↑E : Set V)) :
    (exteriorPairGraph G (↑E : Set V)).degree u ≤
      (G.neighborFinset u.val ∩ S).card := by
  classical
  let X := exteriorPairGraph G (↑E : Set V)
  have hwitness : ∀ v : X.neighborFinset u,
      ∃ z : {z : V // z ∈ G.neighborFinset u.val ∩ S}, G.Adj v.val.val z.val := by
    intro v
    have hadj := (X.mem_neighborFinset _ _).mp v.property
    obtain ⟨hne, z, hz, huz, hvz⟩ := hadj
    refine ⟨⟨z, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr huz,
      hroute u v.val z hne hz huz hvz⟩⟩, hvz⟩
  choose f hf using hwitness
  have hinj : Function.Injective f := by
    intro v w hfw
    apply Subtype.ext
    apply Subtype.ext
    by_contra hvw
    have huv := ((X.mem_neighborFinset _ _).mp v.property).1
    have huw := ((X.mem_neighborFinset _ _).mp w.property).1
    have huv' : u.val ≠ v.val.val := fun h => huv (Subtype.ext h)
    have huw' : u.val ≠ w.val.val := fun h => huw (Subtype.ext h)
    have hzS := (Finset.mem_inter.mp (f v).property).2
    have huz := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp (f v).property).1
    have hvz := hf v
    have hwz : G.Adj w.val.val (f v).val := by rw [hfw]; exact hf w
    have hsub : ({u.val, v.val.val, w.val.val} : Finset V) ⊆
        G.neighborFinset (f v).val ∩ E := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr huz.symm, u.property⟩
      · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hvz.symm, v.val.property⟩
      · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hwz.symm, w.val.property⟩
    have hcard := (Finset.card_le_card hsub).trans (htwo (f v).val hzS)
    have hthree : ({u.val, v.val.val, w.val.val} : Finset V).card = 3 := by
      simp [huv', huw', hvw]
    omega
  have hcard := Fintype.card_le_of_injective f hinj
  have hc : (X.neighborFinset u).card ≤ (G.neighborFinset u.val ∩ S).card := by
    simpa only [Fintype.card_coe] using hcard
  simpa only [X.card_neighborFinset_eq_degree] using hc

/-- An exterior-pair edge cannot also have a common neighbor inside E. -/
theorem exteriorPair_adj_no_inside_common
    (G : SimpleGraph V) [DecidableRel G.Adj] (E : Finset V)
    (hfree : ¬ containsC4 V G)
    {u v : (↑E : Set V)}
    (huv : (exteriorPairGraph G (↑E : Set V)).Adj u v) :
    ¬ ∃ w ∈ E, G.Adj u.val w ∧ G.Adj v.val w := by
  classical
  obtain ⟨hne, z, hz, huz, hvz⟩ := huv
  rintro ⟨w, hw, huw, hvw⟩
  have hcount := (not_containsC4_iff_forall_common_le_one G).mp hfree
    u.val v.val (fun h => hne (Subtype.ext h))
  have hzm : z ∈ G.neighborFinset u.val ∩ G.neighborFinset v.val := by
    exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr huz, (G.mem_neighborFinset _ _).mpr hvz⟩
  have hwm : w ∈ G.neighborFinset u.val ∩ G.neighborFinset v.val := by
    exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr huw, (G.mem_neighborFinset _ _).mpr hvw⟩
  have heq : z = w := Finset.card_le_one.mp hcount z hzm w hwm
  exact hz (heq.symm ▸ hw)

end
end Erdos85
#print axioms Erdos85.exteriorPair_degree_le_routed_neighbor_count
#print axioms Erdos85.exteriorPair_adj_no_inside_common
