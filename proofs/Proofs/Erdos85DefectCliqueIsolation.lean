import Proofs.Erdos85DefectCliquePlateauRigidity
import Proofs.Erdos85C4FreeNeighborBlockPartition
import Proofs.Erdos85ConnectedClosedNeighborhoodEscape

/-!
# Full defect cliques are isolated

At square order, a `q`-clique in the second-order defect graph forces the
`q` open neighborhoods in the original `q`-regular graph to be a partition
of the whole vertex set.  C4-freeness then forces every point outside the
clique to have a common neighbor with every clique point, so no defect edge
leaves the clique.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The open neighborhoods indexed by a full-size defect clique cover the
whole square-order vertex set. -/
theorem defectClique_neighbor_biUnion_eq_univ
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hcard : Fintype.card V = q * q)
    (hreg : ∀ x, G.degree x = q)
    (C : Finset V) (hCcard : C.card = q)
    (hclique : (secondOrderDefectGraph G).IsClique (C : Set V)) :
    C.biUnion (fun c => G.neighborFinset c) = Finset.univ := by
  classical
  have hsafe := commonNeighborIndependent_of_secondOrderDefect_isClique
    G hfree C hclique
  have hpair : (C : Set V).PairwiseDisjoint fun c => G.neighborFinset c := by
    intro x hx y hy hxy
    change Disjoint (G.neighborFinset x) (G.neighborFinset y)
    rw [Finset.disjoint_left]
    intro z hzx hzy
    have hz : z ∈ G.neighborFinset x ∩ G.neighborFinset y :=
      Finset.mem_inter.mpr ⟨hzx, hzy⟩
    have hempty := hsafe hx hy hxy
    rw [Finset.card_eq_zero] at hempty
    exact Finset.notMem_empty z (hempty ▸ hz)
  apply Finset.eq_univ_of_card
  rw [Finset.card_biUnion hpair]
  calc
    (∑ c ∈ C, (G.neighborFinset c).card) = ∑ _c ∈ C, q := by
      apply Finset.sum_congr rfl
      intro c _
      rw [G.card_neighborFinset_eq_degree, hreg c]
    _ = q * q := by simp [hCcard]
    _ = Fintype.card V := hcard.symm

/-- In the square-order regular setting, no second-order defect edge leaves
a full-size defect clique. -/
theorem secondOrderDefect_clique_closed_of_card_eq_degree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hcard : Fintype.card V = q * q)
    (hreg : ∀ x, G.degree x = q)
    (C : Finset V) (hCcard : C.card = q)
    (hclique : (secondOrderDefectGraph G).IsClique (C : Set V)) :
    ∀ c ∈ C, ∀ y, (secondOrderDefectGraph G).Adj c y → y ∈ C := by
  classical
  intro c hc y hDcy
  by_contra hyC
  have hcover := defectClique_neighbor_biUnion_eq_univ
    G hfree hcard hreg C hCcard hclique
  have hzero : (G.neighborFinset c ∩ G.neighborFinset y).card = 0 :=
    (secondOrderDefectGraph_adj_iff_card_common_eq_zero
      G hfree ((secondOrderDefectGraph G).ne_of_adj hDcy)).mp hDcy
  have hleOne : ∀ d ∈ C,
      (G.neighborFinset d ∩ G.neighborFinset y).card ≤ 1 := by
    intro d hd
    by_cases hdy : d = y
    · subst d
      exact (hyC hd).elim
    · exact (not_containsC4_iff_forall_common_le_one G).mp hfree d y hdy
  have hpair : (C : Set V).PairwiseDisjoint
      (fun d => G.neighborFinset d ∩ G.neighborFinset y) := by
    intro d hd e he hde
    change Disjoint (G.neighborFinset d ∩ G.neighborFinset y)
      (G.neighborFinset e ∩ G.neighborFinset y)
    rw [Finset.disjoint_left]
    intro z hzd hze
    have hdc := Finset.mem_inter.mp hzd
    have hec := Finset.mem_inter.mp hze
    have hz : z ∈ G.neighborFinset d ∩ G.neighborFinset e :=
      Finset.mem_inter.mpr ⟨hdc.1, hec.1⟩
    have hsafe := commonNeighborIndependent_of_secondOrderDefect_isClique
      G hfree C hclique
    have hempty := hsafe hd he hde
    rw [Finset.card_eq_zero] at hempty
    exact Finset.notMem_empty z (hempty ▸ hz)
  have hunion : C.biUnion (fun d =>
      G.neighborFinset d ∩ G.neighborFinset y) = G.neighborFinset y := by
    ext z
    constructor
    · simp only [Finset.mem_biUnion, Finset.mem_inter]
      rintro ⟨d, _, _, hzy⟩
      exact hzy
    · intro hzy
      have hzuniv : z ∈ Finset.univ := Finset.mem_univ z
      rw [← hcover, Finset.mem_biUnion] at hzuniv
      obtain ⟨d, hd, hzd⟩ := hzuniv
      exact Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_inter.mpr ⟨hzd, hzy⟩⟩
  have hsum : ∑ d ∈ C,
      (G.neighborFinset d ∩ G.neighborFinset y).card = q := by
    rw [← Finset.card_biUnion hpair, hunion,
      G.card_neighborFinset_eq_degree, hreg y]
  have hupper : ∑ d ∈ C,
      (G.neighborFinset d ∩ G.neighborFinset y).card ≤ C.card - 1 := by
    rw [← Finset.sum_erase_add _ _ hc, hzero, add_zero]
    calc
      (∑ d ∈ C.erase c,
          (G.neighborFinset d ∩ G.neighborFinset y).card) ≤
          ∑ _d ∈ C.erase c, 1 := by
            exact Finset.sum_le_sum fun d hd =>
              hleOne d (Finset.mem_of_mem_erase hd)
      _ = C.card - 1 := by simp [hc]
  rw [hsum, hCcard] at hupper
  have hqpos : 0 < q := by
    rw [← hCcard]
    exact Finset.card_pos.mpr ⟨c, hc⟩
  omega

/-- A connected square-order defect graph has no clique whose cardinality is
the degree of the original graph. -/
theorem connected_secondOrderDefect_no_clique_card_eq_degree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 2 ≤ q)
    (hcard : Fintype.card V = q * q)
    (hreg : ∀ x, G.degree x = q)
    (hconn : (secondOrderDefectGraph G).Connected)
    (C : Finset V) (hCcard : C.card = q) :
    ¬ (secondOrderDefectGraph G).IsClique (C : Set V) := by
  intro hclique
  have hCne : (C : Set V).Nonempty := by
    obtain ⟨c, hc⟩ := Finset.card_pos.mp (show 0 < C.card by omega)
    exact ⟨c, hc⟩
  have hproper : (C : Set V) ≠ Set.univ := by
    intro hCu
    have hCuniv : C = Finset.univ := by
      ext x
      simpa using Set.ext_iff.mp hCu x
    have : q = q * q := by
      calc
        q = C.card := hCcard.symm
        _ = Fintype.card V := by rw [hCuniv]; simp
        _ = q * q := hcard
    exact (Nat.ne_of_lt
      (lt_mul_of_one_lt_left (show 0 < q by omega) (show 1 < q by omega))) this
  obtain ⟨c, hc, y, hy, hcy⟩ :=
    connected_exists_adj_outside_of_nonempty_proper
      (secondOrderDefectGraph G) hconn (C : Set V) hCne hproper
  exact hy (secondOrderDefect_clique_closed_of_card_eq_degree
    G hfree hcard hreg C hCcard hclique c hc y hcy)

end

end Erdos85

#print axioms Erdos85.defectClique_neighbor_biUnion_eq_univ
#print axioms Erdos85.secondOrderDefect_clique_closed_of_card_eq_degree
#print axioms Erdos85.connected_secondOrderDefect_no_clique_card_eq_degree
