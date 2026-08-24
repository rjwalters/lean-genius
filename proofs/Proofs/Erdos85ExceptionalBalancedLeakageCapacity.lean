import Proofs.Erdos85ExceptionalEmptyCliqueIncidenceCapacity

/-!
# Local capacity of exceptional leakage at a balanced center

If an outside center is defect-adjacent to several empty poles, their
degree-`q` neighborhood blocks avoid both the shore and the outside center's
neighborhood.  Replication one therefore packs them into the complement of
that union.  At the final dyadic scale the outside center is balanced, so
half a block of additional capacity is unavailable.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Empty-pole leakage into `x` packs outside `S ∪ N(x)`. -/
theorem emptyClique_defectNeighbors_mul_degree_add_union_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ v, G.degree v = q) (S : Finset V)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    (x : V) :
    q * (((secondOrderDefectGraph G).neighborFinset x ∩
          emptyLineCenters G S).card) +
        (S ∪ G.neighborFinset x).card ≤ Fintype.card V := by
  let E := emptyLineCenters G S
  let Ex := (secondOrderDefectGraph G).neighborFinset x ∩ E
  let U := S ∪ G.neighborFinset x
  have hline : ∀ e ∈ Ex, (G.neighborFinset e ∩ U).card = 0 := by
    intro e he
    have heData := Finset.mem_inter.mp he
    have heEmpty : G.neighborFinset e ∩ S = ∅ :=
      Finset.card_eq_zero.mp ((mem_emptyLineCenters G S e).mp heData.2)
    have hxe : (secondOrderDefectGraph G).Adj x e :=
      ((secondOrderDefectGraph G).mem_neighborFinset x e).mp heData.1
    have hxeNe : x ≠ e := by
      intro h
      subst e
      exact (secondOrderDefectGraph G).loopless.irrefl x hxe
    have hcommon : G.neighborFinset x ∩ G.neighborFinset e = ∅ := by
      apply Finset.card_eq_zero.mp
      exact (secondOrderDefectGraph_adj_iff_card_common_eq_zero
        G hfree hxeNe).mp hxe
    apply Finset.card_eq_zero.mpr
    ext y
    constructor
    · intro hy
      have hyData := Finset.mem_inter.mp hy
      rcases Finset.mem_union.mp hyData.2 with hyS | hyNx
      · have : y ∈ G.neighborFinset e ∩ S :=
          Finset.mem_inter.mpr ⟨hyData.1, hyS⟩
        simpa [heEmpty] using this
      · have : y ∈ G.neighborFinset x ∩ G.neighborFinset e :=
          Finset.mem_inter.mpr ⟨hyNx, hyData.1⟩
        simpa [hcommon] using this
    · simp
  have hcap : ∀ v ∉ U, (G.neighborFinset v ∩ Ex).card ≤ 1 := by
    intro v _hv
    calc
      (G.neighborFinset v ∩ Ex).card ≤
          (G.neighborFinset v ∩ E).card := by
        apply Finset.card_le_card
        intro e he
        exact Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp he).1,
            (Finset.mem_inter.mp (Finset.mem_inter.mp he).2).2⟩
      _ ≤ 1 := secondOrderDefectClique_replicationAtMostOne
        G hfree E hemptyClique v
  have hpack := regular_emptyLines_mul_card_le_complement_card
    G hreg U Ex hline hcap
  have hUcard : U.card ≤ Fintype.card V := by
    simpa only [Finset.card_univ] using
      Finset.card_le_card (show U ⊆ (Finset.univ : Finset V) from Finset.subset_univ U)
  change q * Ex.card + U.card ≤ Fintype.card V
  omega

/-- At a balanced center the local leakage load loses an additional half
neighborhood of capacity, stated without division. -/
theorem binarySquare_balancedCenter_emptyLeakage_capacity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    (x : V) (hbalanced :
      2 * (G.neighborFinset x ∩ S).card = q) :
    2 * q * (((secondOrderDefectGraph G).neighborFinset x ∩
          emptyLineCenters G S).card) + 2 * S.card + q ≤ 2 * q * q := by
  have hlocal := emptyClique_defectNeighbors_mul_degree_add_union_card_le
    G hfree hreg S hemptyClique x
  rw [hcard] at hlocal
  have hNcard : (G.neighborFinset x).card = q := by
    rw [G.card_neighborFinset_eq_degree, hreg]
  have hinter : (S ∩ G.neighborFinset x).card =
      (G.neighborFinset x ∩ S).card := by
    rw [Finset.inter_comm]
  have hunion := Finset.card_inter_add_card_union S (G.neighborFinset x)
  have hU : 2 * (S ∪ G.neighborFinset x).card = 2 * S.card + q := by
    rw [hinter] at hunion
    omega
  nlinarith

/-- A center outside the final exceptional support is balanced, hence obeys
the sharpened local leakage capacity. -/
theorem binarySquare_finalDyadic_outsideExceptional_emptyLeakage_capacity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j : ℕ}
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    (x : V) (hx : x ∉ exceptionalSignedSupport G S q) :
    2 * q * (((secondOrderDefectGraph G).neighborFinset x ∩
          emptyLineCenters G S).card) + 2 * S.card + q ≤ 2 * q * q := by
  have htri := finalDyadic_occupancy_trichotomy G hqa hreg S hdiv x
  have hxNot :
      ¬ ((G.neighborFinset x ∩ S).card = q ∨
        (G.neighborFinset x ∩ S).card = 0) := by
    simpa [mem_exceptionalSignedSupport] using hx
  have hbalanced : 2 * (G.neighborFinset x ∩ S).card = q := by
    rcases htri with hempty | hmiddle | hfull
    · exact False.elim (hxNot (Or.inr hempty))
    · exact hmiddle
    · exact False.elim (hxNot (Or.inl hfull))
  exact binarySquare_balancedCenter_emptyLeakage_capacity
    G hfree hreg hcard S hemptyClique x hbalanced

end

end Erdos85

#print axioms Erdos85.emptyClique_defectNeighbors_mul_degree_add_union_card_le
#print axioms Erdos85.binarySquare_balancedCenter_emptyLeakage_capacity
#print axioms
  Erdos85.binarySquare_finalDyadic_outsideExceptional_emptyLeakage_capacity
