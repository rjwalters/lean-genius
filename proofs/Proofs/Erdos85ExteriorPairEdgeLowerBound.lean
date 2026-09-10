import Proofs.Erdos85OrderSixtyFourExteriorPairGraph
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Exterior incidences force exterior-pair edges

In a C4-free graph, distinct outside vertices cannot witness the same pair
of inside vertices. Thus outside vertices with two inside neighbors inject
into the exterior-pair edges. This is the lower-bound counterpart of the
exterior-pair degree-capacity inequality.
-/
namespace Erdos85
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

theorem exteriorPair_double_neighbor_count_le_edges
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (E S : Finset V) (hdis : Disjoint S E) :
    (S.filter fun z => (G.neighborFinset z ∩ E).card = 2).card ≤
      (exteriorPairGraph G (↑E : Set V)).edgeFinset.card := by
  classical
  let D := S.filter fun z => (G.neighborFinset z ∩ E).card = 2
  let X := exteriorPairGraph G (↑E : Set V)
  have hwitness : ∀ z : D, ∃ a b : (↑E : Set V),
      a ≠ b ∧ G.Adj a.val z.val ∧ G.Adj b.val z.val := by
    intro z
    obtain ⟨a, b, hab, hp⟩ := Finset.card_eq_two.mp (Finset.mem_filter.mp z.property).2
    have ha : a ∈ G.neighborFinset z.val ∩ E := by rw [hp]; simp
    have hb : b ∈ G.neighborFinset z.val ∩ E := by rw [hp]; simp
    refine ⟨⟨a, (Finset.mem_inter.mp ha).2⟩,
      ⟨b, (Finset.mem_inter.mp hb).2⟩, ?_, ?_, ?_⟩
    · exact fun h => hab (congrArg Subtype.val h)
    · exact ((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp ha).1).symm
    · exact ((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hb).1).symm
  choose a b hab haz hbz using hwitness
  have hzoutside : ∀ z : D, z.val ∉ E := by
    intro z hz
    exact Finset.disjoint_left.mp hdis (Finset.mem_filter.mp z.property).1 hz
  let f : D → X.edgeFinset := fun z =>
    ⟨s(a z, b z), by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact ⟨hab z, z.val, hzoutside z, haz z, hbz z⟩⟩
  have hinj : Function.Injective f := by
    intro z w hzw
    have he : s(a z, b z) = s(a w, b w) := congrArg Subtype.val hzw
    have haw : G.Adj (a z).val w.val := by
      rcases Sym2.eq_iff.mp he with h | h
      · rw [h.1]; exact haz w
      · rw [h.1]; exact hbz w
    have hbw : G.Adj (b z).val w.val := by
      rcases Sym2.eq_iff.mp he with h | h
      · rw [h.2]; exact hbz w
      · rw [h.2]; exact haz w
    have hc := (not_containsC4_iff_forall_common_le_one G).mp hfree
      (a z).val (b z).val (fun h => hab z (Subtype.ext h))
    have hzmem : z.val ∈ G.neighborFinset (a z).val ∩ G.neighborFinset (b z).val := by
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (haz z),
        (G.mem_neighborFinset _ _).mpr (hbz z)⟩
    have hwmem : w.val ∈ G.neighborFinset (a z).val ∩ G.neighborFinset (b z).val := by
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr haw,
        (G.mem_neighborFinset _ _).mpr hbw⟩
    exact Subtype.ext (Finset.card_le_one.mp hc z.val hzmem w.val hwmem)
  have hc := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe] using hc

/-- If each outside vertex has at most two inside neighbors, every
incidence beyond one per outside vertex forces an exterior-pair edge. -/
theorem exteriorPair_incidence_le_vertices_add_edges
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (E S : Finset V) (hdis : Disjoint S E)
    (htwo : ∀ z ∈ S, (G.neighborFinset z ∩ E).card ≤ 2) :
    (∑ z ∈ S, (G.neighborFinset z ∩ E).card) ≤ S.card +
      (exteriorPairGraph G (↑E : Set V)).edgeFinset.card := by
  classical
  calc
    (∑ z ∈ S, (G.neighborFinset z ∩ E).card) ≤
        ∑ z ∈ S, (1 + if (G.neighborFinset z ∩ E).card = 2 then 1 else 0) := by
      apply Finset.sum_le_sum
      intro z hz
      have h := htwo z hz
      split_ifs <;> omega
    _ = S.card + (S.filter fun z => (G.neighborFinset z ∩ E).card = 2).card := by
      rw [Finset.sum_add_distrib]
      simp
    _ ≤ S.card + (exteriorPairGraph G (↑E : Set V)).edgeFinset.card :=
      Nat.add_le_add_left (exteriorPair_double_neighbor_count_le_edges G hfree E S hdis) _

end
end Erdos85
#print axioms Erdos85.exteriorPair_double_neighbor_count_le_edges
#print axioms Erdos85.exteriorPair_incidence_le_vertices_add_edges
