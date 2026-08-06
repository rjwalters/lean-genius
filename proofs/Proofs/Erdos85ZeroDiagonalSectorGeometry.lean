import Proofs.Erdos85BoundaryQuotientExcess

/-!
# Geometry forced by a zero diagonal defect block

For a minimum-order defect component, all positive local excess is carried
by equal-order quotient blocks.  If the diagonal block is absent and the
component order exceeds three, some *distinct* equal-order component must
therefore meet it with quotient multiplicity at least two.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- Every positive quotient neighbor of a globally minimum component has
order divisible by the minimum component order.  In particular, every
prime sector containing the minimum component is closed across its entire
quotient row. -/
theorem minimumComponent_order_dvd_of_quotient_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcmin : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard ≤ e.supp.ncard)
    (e : (secondOrderDefectGraph G).ConnectedComponent)
    (hpos : 0 < componentQuotientMatrix G
      (secondOrderDefectGraph G) c e) :
    c.supp.ncard ∣ e.supp.ncard := by
  rcases secondOrder_componentQuotientMatrix_pos_imp_size_dvd_or_dvd
      G hfree hd heven hmin hcard c e hpos with hce | hec
  · exact hce
  · have hecLe : e.supp.ncard ≤ c.supp.ncard :=
      Nat.le_of_dvd c.nonempty_supp.ncard_pos hec
    have heq : e.supp.ncard = c.supp.ncard :=
      Nat.le_antisymm hecLe (hcmin e)
    rw [heq]

/-- Prime-sector form of `minimumComponent_order_dvd_of_quotient_pos`. -/
theorem prime_dvd_neighbor_order_of_minimumComponent_quotient_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcmin : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard ≤ e.supp.ncard)
    (hpc : p ∣ c.supp.ncard)
    (e : (secondOrderDefectGraph G).ConnectedComponent)
    (hpos : 0 < componentQuotientMatrix G
      (secondOrderDefectGraph G) c e) :
    p ∣ e.supp.ncard := by
  exact dvd_trans hpc
    (minimumComponent_order_dvd_of_quotient_pos
      G hfree hd heven hmin hcard c hcmin e hpos)

/-- **Zero diagonal forces a same-size companion.** A minimum defect
component of order at least four with `Q(c,c)=0` has a distinct component
of the same order with quotient multiplicity at least two. -/
theorem exists_equalSize_quotient_ge_two_of_minimum_diagonal_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcmin : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard ≤ e.supp.ncard)
    (hc4 : 4 ≤ c.supp.ncard)
    (hdiag : componentQuotientMatrix G (secondOrderDefectGraph G) c c = 0) :
    ∃ e : (secondOrderDefectGraph G).ConnectedComponent,
      e ≠ c ∧ e.supp.ncard = c.supp.ncard ∧
        2 ≤ componentQuotientMatrix G (secondOrderDefectGraph G) c e := by
  classical
  by_contra hnone
  push_neg at hnone
  have hterm : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      (if e.supp.ncard = c.supp.ncard then
        (componentQuotientMatrix G (secondOrderDefectGraph G) c e : ℤ) *
          ((componentQuotientMatrix G (secondOrderDefectGraph G) c e : ℤ) - 1)
       else 0) = 0 := by
    intro e
    by_cases hsize : e.supp.ncard = c.supp.ncard
    · rw [if_pos hsize]
      by_cases hec : e = c
      · subst e
        simp [hdiag]
      · have hle : componentQuotientMatrix G
            (secondOrderDefectGraph G) c e ≤ 1 := by
          have hlt := hnone e hec hsize
          omega
        have hzero_or_one : componentQuotientMatrix G
            (secondOrderDefectGraph G) c e = 0 ∨
            componentQuotientMatrix G (secondOrderDefectGraph G) c e = 1 := by
          omega
        rcases hzero_or_one with hzero | hone
        · simp [hzero]
        · simp [hone]
    · rw [if_neg hsize]
  have hexcess := secondOrder_minimumComponent_equalSize_excess
    G hfree hd heven hmin hcard c hcmin
  have hsumzero :
      (∑ e, if e.supp.ncard = c.supp.ncard then
        (componentQuotientMatrix G (secondOrderDefectGraph G) c e : ℤ) *
          ((componentQuotientMatrix G (secondOrderDefectGraph G) c e : ℤ) - 1)
       else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    exact hterm e
  rw [hsumzero] at hexcess
  omega

end

end Erdos85
