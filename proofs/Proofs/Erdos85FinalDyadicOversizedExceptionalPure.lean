import Proofs.Erdos85ExceptionalSupportDefectCapacity

/-!
# Oversized final exceptional support is pure

The empty-pole defect-capacity bound has a useful contrapositive: above
cardinality `q`, the canonical exceptional support cannot contain an empty
center.  The final dyadic complement is therefore exactly the full-center
population, providing the graph-facing entrance to the pure exceptional
normal form.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- If the final exceptional complement exceeds the defect-neighborhood
capacity `q`, its canonical empty population vanishes. -/
theorem c4Free_binarySquare_emptyLineCenters_eq_empty_of_q_lt_compl_finalDyadicSupport
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
    (hoversized : q <
      ((dyadicOccupancySupport G S j)ᶜ : Finset V).card) :
    emptyLineCenters G S = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  intro hemptyNonempty
  have hcap :=
    c4Free_binarySquare_compl_finalDyadicSupport_card_le_of_emptyClique
      G hfree hq hqa hreg hcard S hdiv hemptyClique hemptyNonempty
  omega

/-- Branch extractor: an oversized final exceptional complement is exactly
the pure full-center family. -/
theorem c4Free_binarySquare_compl_finalDyadicSupport_eq_fullLineCenters_of_q_lt
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
    (hoversized : q <
      ((dyadicOccupancySupport G S j)ᶜ : Finset V).card) :
    (dyadicOccupancySupport G S j)ᶜ = fullLineCenters G S q := by
  rw [compl_dyadicOccupancySupport_eq_full_union_empty
    G hqa hreg S hdiv,
    c4Free_binarySquare_emptyLineCenters_eq_empty_of_q_lt_compl_finalDyadicSupport
      G hfree hq hqa hreg hcard S hdiv hemptyClique hoversized,
    Finset.union_empty]

/-- Equivalent canonical-support form of the pure oversized branch. -/
theorem c4Free_binarySquare_exceptionalSignedSupport_eq_fullLineCenters_of_q_lt
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
    (hoversized : q <
      ((dyadicOccupancySupport G S j)ᶜ : Finset V).card) :
    exceptionalSignedSupport G S q = fullLineCenters G S q := by
  rw [exceptionalSignedSupport_eq_full_union_empty,
    c4Free_binarySquare_emptyLineCenters_eq_empty_of_q_lt_compl_finalDyadicSupport
      G hfree hq hqa hreg hcard S hdiv hemptyClique hoversized,
    Finset.union_empty]

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_emptyLineCenters_eq_empty_of_q_lt_compl_finalDyadicSupport
#print axioms
  Erdos85.c4Free_binarySquare_compl_finalDyadicSupport_eq_fullLineCenters_of_q_lt
#print axioms
  Erdos85.c4Free_binarySquare_exceptionalSignedSupport_eq_fullLineCenters_of_q_lt
