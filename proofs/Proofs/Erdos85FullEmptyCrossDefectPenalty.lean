import Proofs.Erdos85FinalDyadicExceptionalSupportBridge
import Proofs.Erdos85DyadicStoppingSupportDefectPenalizedCherrySqueeze

/-!
# Unconditional full-empty cross defect penalty

Every full line center is second-order-defect adjacent to every empty line
center.  Since the two canonical populations are disjoint, their Cartesian
product injects into the unordered defect pairs of the exceptional support.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Two disjoint families with complete cross adjacency contribute their
product many unordered defect pairs to any containing set. -/
theorem card_mul_card_le_secondOrderDefectPairs_of_cross
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (F E C : Finset V) (hdisj : Disjoint F E)
    (hFC : F ⊆ C) (hEC : E ⊆ C)
    (hcross : ∀ x ∈ F, ∀ y ∈ E,
      (secondOrderDefectGraph G).Adj x y) :
    F.card * E.card ≤ (secondOrderDefectPairs G C).card := by
  let P : Finset (V × V) := F ×ˢ E
  have hcardP : P.card = F.card * E.card := by simp [P]
  rw [← hcardP]
  apply Finset.card_le_card_of_injOn
    (fun p : V × V => ({p.1, p.2} : Finset V))
  · rintro ⟨x, y⟩ hxy
    have hxF : x ∈ F := (Finset.mem_product.mp hxy).1
    have hyE : y ∈ E := (Finset.mem_product.mp hxy).2
    have hxyNe : x ≠ y := by
      intro h
      subst y
      exact Finset.disjoint_left.mp hdisj hxF hyE
    change {x, y} ∈ secondOrderDefectPairs G C
    simp only [secondOrderDefectPairs, Finset.mem_filter,
      Finset.mem_powersetCard]
    refine ⟨⟨?_, by simp [hxyNe]⟩, ?_⟩
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hFC hxF
      · exact hEC hyE
    · intro u hu v hv huv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with hu | hu
      · rcases hv with hv | hv
        · exact (huv (hu.trans hv.symm)).elim
        · simpa [hu, hv] using hcross x hxF y hyE
      · rcases hv with hv | hv
        · simpa [hu, hv] using (hcross x hxF y hyE).symm
        · exact (huv (hu.trans hv.symm)).elim
  · rintro ⟨x, y⟩ hxy ⟨x', y'⟩ hx'y' heq
    change ({x, y} : Finset V) = {x', y'} at heq
    have hxF : x ∈ F := (Finset.mem_product.mp hxy).1
    have hyE : y ∈ E := (Finset.mem_product.mp hxy).2
    have hx'F : x' ∈ F := (Finset.mem_product.mp hx'y').1
    have hy'E : y' ∈ E := (Finset.mem_product.mp hx'y').2
    have hxMem : x ∈ ({x', y'} : Finset V) := by
      rw [← heq]
      simp
    have hyMem : y ∈ ({x', y'} : Finset V) := by
      rw [← heq]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxMem hyMem
    have hxx' : x = x' := hxMem.resolve_right fun hxy' => by
      subst y'
      exact Finset.disjoint_left.mp hdisj hxF hy'E
    have hyy' : y = y' := hyMem.resolve_left fun hyx' => by
      exact Finset.disjoint_left.mp hdisj hx'F (hyx' ▸ hyE)
    simp [hxx', hyy']

/-- The canonical exceptional support contains at least `|F||E|` internal
defect pairs, unconditionally. -/
theorem full_mul_empty_le_exceptionalSupport_secondOrderDefectPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 0 < q)
    (hreg : ∀ v, G.degree v = q) (S : Finset V) :
    (fullLineCenters G S q).card * (emptyLineCenters G S).card ≤
      (secondOrderDefectPairs G (exceptionalSignedSupport G S q)).card := by
  apply card_mul_card_le_secondOrderDefectPairs_of_cross
    G (fullLineCenters G S q) (emptyLineCenters G S)
      (exceptionalSignedSupport G S q)
    (fullLineCenters_disjoint_emptyLineCenters G S hq)
  · rw [exceptionalSignedSupport_eq_full_union_empty]
    exact Finset.subset_union_left
  · rw [exceptionalSignedSupport_eq_full_union_empty]
    exact Finset.subset_union_right
  · intro x hx y hy
    exact binarySquare_full_empty_secondOrderDefect_adj
      G hfree hq hreg S
      ((mem_fullLineCenters G S q x).mp hx)
      ((mem_emptyLineCenters G S y).mp hy)

/-- Final dyadic form: the full-empty product is an internal defect-pair
penalty in the complement of the marked half-occupancy support. -/
theorem full_mul_empty_le_compl_finalDyadicSupport_secondOrderDefectPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j : ℕ}
    (hq : 0 < q) (hqa : q = 2 * 2 ^ j)
    (hreg : ∀ v, G.degree v = q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card) :
    (fullLineCenters G S q).card * (emptyLineCenters G S).card ≤
      (secondOrderDefectPairs G ((dyadicOccupancySupport G S j)ᶜ)).card := by
  rw [compl_dyadicOccupancySupport_eq_exceptionalSignedSupport
    G hqa hreg S hdiv]
  exact full_mul_empty_le_exceptionalSupport_secondOrderDefectPairs
    G hfree hq hreg S

end

end Erdos85

#print axioms Erdos85.card_mul_card_le_secondOrderDefectPairs_of_cross
#print axioms Erdos85.full_mul_empty_le_compl_finalDyadicSupport_secondOrderDefectPairs
