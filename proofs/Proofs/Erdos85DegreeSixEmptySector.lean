import Proofs.Erdos85MixedSectorMassQuotient

/-!
# Degree-six empty-sector carrier extraction

In the empty color-sector branch of the degree-six exact boundary, every
defect component is antipodal.  The nonsquare trace identity pins the
total diagonal quotient mass at six, so a positive-diagonal component
exists; and since the boundary order `33` is odd, an odd-order component
always exists.  The carrier lemma packages the two: once odd components
are known to be zero-diagonal (the forward-orientation mass reduction),
the diagonal mass must be carried by an even-order component.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- The degree-six boundary order `33` is odd, so some defect component
has odd order. -/
theorem degreeSix_exists_odd_order_component
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hcard : Fintype.card V = 33) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      Odd c.supp.ncard := by
  classical
  by_contra hnone
  push Not at hnone
  have hparts : (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard) = Fintype.card V := by
    calc
      (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
          c.supp.ncard) =
          ∑ c : (secondOrderDefectGraph G).ConnectedComponent,
            Fintype.card c.supp := by
        apply Finset.sum_congr rfl
        intro c _
        simpa [Nat.card_eq_fintype_card] using
          (Nat.card_coe_set_eq c.supp).symm
      _ = Fintype.card
          (Σ c : (secondOrderDefectGraph G).ConnectedComponent, c.supp) :=
        Fintype.card_sigma.symm
      _ = Fintype.card V := by
        apply Fintype.card_congr
        exact (Equiv.sigmaFiberEquiv
          (secondOrderDefectGraph G).connectedComponentMk)
  have hdvd : 2 ∣ ∑ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard := by
    apply Finset.dvd_sum
    intro c _
    exact (Nat.not_odd_iff_even.mp (hnone c)).two_dvd
  rw [hparts, hcard] at hdvd
  omega

/-- Carrier extraction: the nonsquare trace identity gives total diagonal
mass six, so once every odd-order component is zero-diagonal, an
even-order component with positive diagonal quotient exists. -/
theorem degreeSix_exists_even_carrier_of_odd_zero_diagonal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (hodd0 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      Odd c.supp.ncard →
        componentQuotientMatrix G (secondOrderDefectGraph G) c c = 0) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      Even c.supp.ncard ∧
        0 < componentQuotientMatrix G (secondOrderDefectGraph G) c c := by
  classical
  have htrace := secondOrder_componentQuotient_trace_eq_degree_of_nonsquare
    G hfree (d := 6) (by norm_num) (by norm_num) hmin
      (by norm_num at hcard ⊢; exact hcard) (by norm_num)
  by_contra hnone
  push Not at hnone
  have hzero : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      componentQuotientMatrix G (secondOrderDefectGraph G) c c = 0 := by
    intro c
    by_cases hoddc : Odd c.supp.ncard
    · exact hodd0 c hoddc
    · have heven : Even c.supp.ncard := Nat.not_odd_iff_even.mp hoddc
      have := hnone c heven
      omega
  have hsum : (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
      componentQuotientMatrix G (secondOrderDefectGraph G) c c) = 0 :=
    Finset.sum_eq_zero fun c _ => hzero c
  rw [hsum] at htrace
  exact absurd htrace.symm (by norm_num)

end

end Erdos85
