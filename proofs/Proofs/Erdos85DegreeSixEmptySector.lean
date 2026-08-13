import Proofs.Erdos85DegreeSixColorSectorSplit
import Proofs.Erdos85DegreeSixOddDiagonal

/-!
# Degree-six empty-sector assembly

Carrier lemmas for the empty color-sector branch of the degree-six exact
boundary.  The master contradiction is assembled here once the remaining
odd-diagonal discharge is available.
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
    simpa using sum_connectedComponent_supp_ncard (secondOrderDefectGraph G)
  have hdvd : 2 ∣ ∑ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard := by
    apply Finset.dvd_sum
    intro c _
    exact (Nat.not_odd_iff_even.mp (hnone c)).two_dvd
  rw [hparts, hcard] at hdvd
  omega

/-- Once all odd components are zero-diagonal, the nonsquare trace six
must be carried by a positive-diagonal even component. -/
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

/-- An order-thirteen component cannot have diagonal quotient two at the
degree-six boundary. -/
theorem false_of_degreeSix_orderThirteen_diagonal_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (w : (secondOrderDefectGraph G).ConnectedComponent)
    (hw13 : w.supp.ncard = 13)
    (hdiag : componentQuotientMatrix G (secondOrderDefectGraph G) w w = 2) :
    False := by
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  let size : D.ConnectedComponent → ℕ := fun c ↦ c.supp.ncard
  have htotal : (∑ c : D.ConnectedComponent, size c) = 33 := by
    simpa [size, D, hcard] using sum_connectedComponent_supp_ncard D
  have hsize : ∀ t, t ≠ w → size t ≤ 20 := by
    intro t htw
    have hle := two_distinct_terms_le_sum size htw
    rw [htotal] at hle
    dsimp [size] at hle ⊢
    rw [hw13] at hle
    omega
  have hrow (c : D.ConnectedComponent) : (∑ t, Q c t) = 6 :=
    sum_secondOrder_componentQuotientMatrix_row_eq_degree
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) c
  have hrev : ∀ t, Q w t ≤ 6 ∧ Q t w ≤ 6 := by
    intro t
    constructor
    · exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ t)).trans_eq (hrow w)
    · exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ w)).trans_eq (hrow t)
  have hbal : ∀ t, size w * Q w t = size t * Q t w := by
    intro t
    exact secondOrder_componentQuotientMatrix_balance
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) w t
  have hsq : (∑ t, Q w t * Q t w) = 16 := by
    have hs := secondOrder_componentQuotientMatrix_sq_apply
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) w w
    simpa [Q, size, D, Matrix.mul_apply, hw13] using hs
  exact OddDiagonal.false_of_thirteen_diag_two
    Q size w hw13 hsize hrev hbal hdiag (hrow w) hsq

/-- A component of prime order at least seventeen cannot have diagonal
quotient two at the degree-six boundary. -/
theorem false_of_degreeSix_largePrime_diagonal_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (w : (secondOrderDefectGraph G).ConnectedComponent) {o : ℕ}
    (hwo : w.supp.ncard = o) (hop : o.Prime) (ho17 : 17 ≤ o)
    (hdiag : componentQuotientMatrix G (secondOrderDefectGraph G) w w = 2) :
    False := by
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  let size : D.ConnectedComponent → ℕ := fun c ↦ c.supp.ncard
  have htotal : (∑ c : D.ConnectedComponent, size c) = 33 := by
    simpa [size, D, hcard] using sum_connectedComponent_supp_ncard D
  have hsize : ∀ t, t ≠ w → size t ≤ 33 - o := by
    intro t htw
    have hle := two_distinct_terms_le_sum size htw
    rw [htotal] at hle
    dsimp [size] at hle ⊢
    rw [hwo] at hle
    omega
  have hrow (c : D.ConnectedComponent) : (∑ t, Q c t) = 6 :=
    sum_secondOrder_componentQuotientMatrix_row_eq_degree
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) c
  have hrev : ∀ t, Q w t ≤ 6 ∧ Q t w ≤ 6 := by
    intro t
    constructor
    · exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ t)).trans_eq (hrow w)
    · exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ w)).trans_eq (hrow t)
  have hbal : ∀ t, size w * Q w t = size t * Q t w := by
    intro t
    exact secondOrder_componentQuotientMatrix_balance
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) w t
  exact OddDiagonal.false_of_large_prime_diag_two
    Q size w hwo hop ho17 hsize hrev hbal hdiag (hrow w)

end

end Erdos85
