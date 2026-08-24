import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEqAddThreeOddDegreeTwoSector
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! # The odd `m+3` complement sector is non-bipartite -/

open Finset BigOperators SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000

/-- A finite two-regular graph has even order whenever it is bipartite. -/
theorem twoRegular_bipartite_card_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree 2) (hbip : G.IsBipartite) :
    Even (Fintype.card V) := by
  classical
  obtain ⟨s, t, hst⟩ := hbip.exists_isBipartiteWith
  have hsupport : G.support = Set.univ := by
    ext v
    simp only [Set.mem_univ, iff_true]
    rw [← G.degree_pos_iff_mem_support]
    simpa [hreg.degree_eq v]
  have hcover : s ∪ t = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    intro v _
    have hv : v ∈ G.support := by simp [hsupport]
    exact isBipartiteWith_support_subset hst hv
  let sf := s.toFinset
  let tf := t.toFinset
  have hstFin : G.IsBipartiteWith (↑sf : Set V) (↑tf : Set V) := by
    simpa [sf, tf] using hst
  have hsum := isBipartiteWith_sum_degrees_eq hstFin
  have hstCard : sf.card = tf.card := by
    have htwo : 2 * sf.card = 2 * tf.card := by
      simpa [hreg.degree_eq, mul_comm] using hsum
    omega
  have hcard : Fintype.card V = sf.card + tf.card := by
    have hunion : sf ∪ tf = Finset.univ := by
      ext v
      simpa [sf, tf] using Set.ext_iff.mp hcover v
    have hdisFin : Disjoint sf tf := by
      rw [Finset.disjoint_left]
      intro v hvs hvt
      exact Set.disjoint_left.mp hst.disjoint
        (by simpa [sf] using hvs) (by simpa [tf] using hvt)
    have hc := card_union_of_disjoint hdisFin
    rw [hunion] at hc
    simpa using hc
  refine ⟨sf.card, ?_⟩
  omega

/-- Therefore a finite two-regular graph of odd order is not bipartite. -/
theorem twoRegular_odd_card_not_bipartite
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree 2) (hodd : Odd (Fintype.card V)) :
    ¬ G.IsBipartite := by
  intro hbip
  exact Nat.not_even_iff_odd.mpr hodd (twoRegular_bipartite_card_even G hreg hbip)

end

end Erdos85

#print axioms Erdos85.twoRegular_bipartite_card_even
#print axioms Erdos85.twoRegular_odd_card_not_bipartite
