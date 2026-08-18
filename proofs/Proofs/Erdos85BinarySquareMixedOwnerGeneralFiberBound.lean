import Proofs.Erdos85BinarySquareMixedOwnerFiberBound

/-! # Mixed-owner fiber bounds for arbitrary binary component sizes -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A same-defect-component mixed-owner fiber has the uniform two-step-walk
bound dictated by the normalized sizes of its source and first two owner
colors.  This is the size-sensitive version of the earlier `16 * 2 * 2`
bound used in the all-size-two branch. -/
theorem binarySquare_regular_mixedOwnerFiber_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (source a b c : (secondOrderDefectGraph G).ConnectedComponent)
    {m_source m_a m_b : ℕ}
    (hsource : source.supp.ncard = q * m_source)
    (ha : a.supp.ncard = q * m_a)
    (hb : b.supp.ncard = q * m_b) :
    (cyclicColoredTriplesInComponent (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) source).card ≤
        q * m_source * (m_a * (m_source - 1)) *
          (m_b * (m_source - 1)) := by
  rw [card_owner_cyclicColoredTriplesInComponent_eq_restricted]
  have hbound := card_cyclicColoredTriples_le_card_mul_degrees
    (restrictedComponentOwnerGraph G source a)
    (restrictedComponentOwnerGraph G source b)
    (restrictedComponentOwnerGraph G source c)
    (m_a * (m_source - 1)) (m_b * (m_source - 1))
    (fun x => binarySquare_regular_restrictedComponentOwnerGraph_degree
      G hfree hq hreg hcard source a hsource ha x)
    (fun x => binarySquare_regular_restrictedComponentOwnerGraph_degree
      G hfree hq hreg hcard source b hsource hb x)
  have hcardSource : Fintype.card source.supp = q * m_source := by
    calc
      Fintype.card source.supp = source.supp.ncard := by
        simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq source.supp
      _ = q * m_source := hsource
  simpa [hcardSource] using hbound

/-- Summing the size-sensitive fiber bound over every source component gives
an invariant global bound for the same-component portion of a mixed-owner
census. -/
theorem binarySquare_regular_sameComponent_mixedOwner_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = q * m d)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent) :
    (sameComponentCyclicColoredTriples (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c)).card ≤
        ∑ source : (secondOrderDefectGraph G).ConnectedComponent,
          q * m source * (m a * (m source - 1)) *
            (m b * (m source - 1)) := by
  rw [← sum_card_cyclicColoredTriplesInComponent_eq_card_sameComponent]
  exact Finset.sum_le_sum fun source _ =>
    binarySquare_regular_mixedOwnerFiber_card_le
      G hfree hq hreg hcard source a b c
        (hm source) (hm a) (hm b)

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_mixedOwnerFiber_card_le
#print axioms Erdos85.binarySquare_regular_sameComponent_mixedOwner_card_le
