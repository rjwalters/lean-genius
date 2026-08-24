import Proofs.Erdos85CanonicalExceptionalLineFamilies
import Proofs.Erdos85FinalDyadicExceptionalSupportBridge

/-!
# Defect-degree capacity of the exceptional support

An empty line center is defect-adjacent to every full line center.  If the
empty family is itself a defect clique, one empty pole sees every other
vertex of the canonical exceptional support.  At square order the defect
degree is `q-1`, so the whole support has size at most `q`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A nonempty canonical empty clique forces the full/empty exceptional
support into one closed defect neighborhood. -/
theorem binarySquare_full_union_empty_card_le_of_emptyClique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    (hemptyNonempty : (emptyLineCenters G S).Nonempty) :
    (fullLineCenters G S q ∪ emptyLineCenters G S).card ≤ q := by
  obtain ⟨pole, hpole⟩ := hemptyNonempty
  let C := fullLineCenters G S q ∪ emptyLineCenters G S
  change C.card ≤ q
  have hpoleC : pole ∈ C := Finset.mem_union_right _ hpole
  have hsub : C.erase pole ⊆
      (secondOrderDefectGraph G).neighborFinset pole := by
    intro x hx
    have hxC := (Finset.mem_erase.mp hx).2
    have hxpole : x ≠ pole := (Finset.mem_erase.mp hx).1
    rw [(secondOrderDefectGraph G).mem_neighborFinset]
    rcases Finset.mem_union.mp hxC with hxFull | hxEmpty
    · exact (binarySquare_full_empty_secondOrderDefect_adj
        G hfree (by omega) hreg S
          ((mem_fullLineCenters G S q x).mp hxFull)
          ((mem_emptyLineCenters G S pole).mp hpole)).symm
    · exact hemptyClique hpole hxEmpty hxpole.symm
  have hdegree :
      ((secondOrderDefectGraph G).neighborFinset pole).card = q - 1 := by
    rw [(secondOrderDefectGraph G).card_neighborFinset_eq_degree,
      binarySquare_regular_secondOrderDefect_degree_eq
        G hfree hq hreg hcard]
  have herase : (C.erase pole).card = C.card - 1 :=
    Finset.card_erase_of_mem hpoleC
  have hcap := Finset.card_le_card hsub
  rw [herase, hdegree] at hcap
  have hCpos : 0 < C.card := Finset.card_pos.mpr ⟨pole, hpoleC⟩
  omega

/-- Final-dyadic form: whenever an empty pole exists and the empty family is
a defect clique, the complement of the stopping support has size at most
`q`. -/
theorem c4Free_binarySquare_compl_finalDyadicSupport_card_le_of_emptyClique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j : ℕ} (hq : 3 ≤ q)
    (hqa : q = 2 * 2 ^ j)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    (hemptyNonempty : (emptyLineCenters G S).Nonempty) :
    ((dyadicOccupancySupport G S j)ᶜ : Finset V).card ≤ q := by
  rw [compl_dyadicOccupancySupport_eq_full_union_empty
    G hqa hreg S hdiv]
  exact binarySquare_full_union_empty_card_le_of_emptyClique
    G hfree hq hreg hcard S hemptyClique hemptyNonempty

end

end Erdos85

#print axioms Erdos85.binarySquare_full_union_empty_card_le_of_emptyClique
#print axioms
  Erdos85.c4Free_binarySquare_compl_finalDyadicSupport_card_le_of_emptyClique
