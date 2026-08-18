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

/-- At order 64, subtracting the global same-component bound from the exact
mixed cubic trace gives a uniform lower bound on the cross-component census.
The coefficient `448 = 8² * 7` is the binary-square mixed-trace constant. -/
theorem orderSixtyFour_regular_crossComponent_mixedOwner_card_ge
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = 8 * m d)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    448 * m a * m b * m c -
        (∑ source : (secondOrderDefectGraph G).ConnectedComponent,
          8 * m source * (m a * (m source - 1)) *
            (m b * (m source - 1))) ≤
      (crossComponentCyclicColoredTriples (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)
        (componentOwnerGraph G (secondOrderDefectGraph G) c)).card := by
  let D := secondOrderDefectGraph G
  let A := componentOwnerGraph G D a
  let B := componentOwnerGraph G D b
  let C := componentOwnerGraph G D c
  have hsame := binarySquare_regular_sameComponent_mixedOwner_card_le
    G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm a b c
  have htrace := binarySquare_regular_trace_three_distinct_ownerMatrices
    G hfree (q := 8) (by norm_num) hreg (by norm_num)
      a b c hab hac hbc (hm a) (hm b) (hm c)
  have htotal : (cyclicColoredTriples A B C).card =
      448 * m a * m b * m c := by
    rw [trace_three_adjMatrices_eq_card_cyclicColoredTriples] at htrace
    change (cyclicColoredTriples A B C).card = _
    exact_mod_cast htrace
  have hsplit :=
    card_sameComponent_add_card_crossComponent_eq_card_cyclicColoredTriples
      D A B C
  change (sameComponentCyclicColoredTriples D A B C).card +
      (crossComponentCyclicColoredTriples D A B C).card =
        (cyclicColoredTriples A B C).card at hsplit
  rw [htotal] at hsplit
  dsimp [D, A, B, C] at hsame hsplit ⊢
  omega

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_mixedOwnerFiber_card_le
#print axioms Erdos85.binarySquare_regular_sameComponent_mixedOwner_card_le
#print axioms Erdos85.orderSixtyFour_regular_crossComponent_mixedOwner_card_ge
