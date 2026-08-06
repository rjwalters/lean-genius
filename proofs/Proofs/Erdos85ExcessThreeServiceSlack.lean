import Proofs.Erdos85ExcessThreeServicePincer

/-!
# Exact slack in the excess-three service pincer

The pincer inequality is lossless after retaining the service above the
mandatory one unit on each negative commutator slot.  This file records that
exact identity.  Consequently any future lower bound which saturates the
pincer automatically forces every negative slot to have service exactly one.
-/

open SimpleGraph

namespace Erdos85

/-- Antipodal service in excess of the mandatory unit on every negative
commutator slot. -/
def negativeSlotServiceSlack
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] : ℤ :=
  ∑ p ∈ matchingNegativeSlots G,
    ((G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) p.1 p.2 - 1)

/-- The negative-slot slack is nonnegative: each negative commutator slot
demands at least one unit of antipodal service. -/
theorem negativeSlotServiceSlack_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d) :
    0 ≤ negativeSlotServiceSlack G := by
  classical
  rw [negativeSlotServiceSlack]
  apply Finset.sum_nonneg
  intro p hp
  have hs := one_le_service_of_matchingNegativeSlot G hfree hreg hp
  omega

/-- **Exact excess-three pincer identity.**  The negative-slot excess,
symmetric claw-leg service, and the mixed chord moment partition the complete
budget `4|V| + 2a`. -/
theorem excessThree_serviceSlack_add_symmetric_add_chord_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) :
    negativeSlotServiceSlack G +
        (∑ p ∈ symmetricServicePairs G,
          (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) p.1 p.2) +
        Matrix.trace ((triangleFreeEdgeGraph G).adjMatrix ℤ *
          (antipodalGraph G).adjMatrix ℤ *
          (antipodalGraph G).adjMatrix ℤ) =
      4 * (Fintype.card V : ℤ) + 2 *
        ((Finset.univ.filter fun x : V =>
          (triangleFreeEdgeGraph G).degree x = 3).card : ℤ) := by
  classical
  have hmoment := excessThree_trace_serviceMoment_add_triangleFree_antipodal_sq
    G hfree hd hodd hreg hcard
  dsimp only at hmoment
  have hsplit := trace_serviceMoment_eq_sum_negative_add_symmetric G hfree
  dsimp only at hsplit
  have hcount := card_matchingNegativeSlots_excessThree
    G hfree hd hodd hreg hcard
  rw [hsplit] at hmoment
  rw [negativeSlotServiceSlack, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcount]
  linarith

/-- Saturating the symmetric-service/chord budget rigidifies every negative
slot: none can consume more than its mandatory single unit of service. -/
theorem service_eq_one_of_excessThree_pincer_saturated
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6)
    (hsaturated :
      4 * (Fintype.card V : ℤ) + 2 *
          ((Finset.univ.filter fun x : V =>
            (triangleFreeEdgeGraph G).degree x = 3).card : ℤ) ≤
        (∑ p ∈ symmetricServicePairs G,
          (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) p.1 p.2) +
        Matrix.trace ((triangleFreeEdgeGraph G).adjMatrix ℤ *
          (antipodalGraph G).adjMatrix ℤ *
          (antipodalGraph G).adjMatrix ℤ))
    {p : V × V} (hp : p ∈ matchingNegativeSlots G) :
    (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) p.1 p.2 = 1 := by
  classical
  have hexact := excessThree_serviceSlack_add_symmetric_add_chord_eq
    G hfree hd hodd hreg hcard
  have hslack_nonneg := negativeSlotServiceSlack_nonneg G hfree hreg
  have hslack : negativeSlotServiceSlack G = 0 := by
    linarith
  have hterms : ∀ q ∈ matchingNegativeSlots G,
      0 ≤ (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) q.1 q.2 - 1 := by
    intro q hq
    have hs := one_le_service_of_matchingNegativeSlot G hfree hreg hq
    omega
  have hsum :
      (∑ q ∈ matchingNegativeSlots G,
        ((G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) q.1 q.2 - 1)) = 0 := by
    simpa [negativeSlotServiceSlack] using hslack
  have hpzero := (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hsum p hp
  omega

end Erdos85
