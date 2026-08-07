import Proofs.Erdos85BoundaryQuotientExcess
import Proofs.Erdos85BoundaryQuotientIrreducibleClean

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

/-- If a prime divides the order of a globally minimum defect component but
does not divide every component order, then it divides the order of some
*strictly larger* component.  Thus a prime sector containing a minimum
component cannot consist only of copies of the minimum cycle unless it is
the whole irreducible quotient.

This is the first genuinely global consequence of minimum-row closure: if
all `p`-divisible components had minimum order, each of their quotient rows
would remain in the `p`-sector, contradicting irreducibility in the presence
of a complementary component. -/
theorem exists_strictlyLarger_pDivisibleComponent_of_minimum_and_complement
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcmin : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard ≤ e.supp.ncard)
    (hpc : p ∣ c.supp.ncard)
    (t : (secondOrderDefectGraph G).ConnectedComponent)
    (hpt : ¬ p ∣ t.supp.ncard) :
    ∃ e : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ e.supp.ncard ∧ c.supp.ncard < e.supp.ncard := by
  classical
  letI : Nonempty V :=
    ⟨componentRepresentative (secondOrderDefectGraph G) c⟩
  by_contra hnone
  push_neg at hnone
  have hsizeEq (e : (secondOrderDefectGraph G).ConnectedComponent)
      (hpe : p ∣ e.supp.ncard) : e.supp.ncard = c.supp.ncard := by
    exact Nat.le_antisymm (hnone e hpe) (hcmin e)
  have hclosed (a b : (secondOrderDefectGraph G).ConnectedComponent)
      (hpa : p ∣ a.supp.ncard)
      (hab : 0 < componentQuotientMatrix G
        (secondOrderDefectGraph G) a b) :
      p ∣ b.supp.ncard := by
    have hac : a.supp.ncard = c.supp.ncard := hsizeEq a hpa
    have hamin : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
        a.supp.ncard ≤ e.supp.ncard := by
      intro e
      rw [hac]
      exact hcmin e
    exact prime_dvd_neighbor_order_of_minimumComponent_quotient_pos
      G hfree hd heven hmin hcard a hamin hpa b hab
  have hwalk := secondOrder_componentQuotientMatrix_irreducible_clean
    G hfree hd heven hmin hcard c t
  have hpropagate : ∀ {a b : (secondOrderDefectGraph G).ConnectedComponent},
      Relation.ReflTransGen
        (fun x y => 0 < componentQuotientMatrix G
          (secondOrderDefectGraph G) x y) a b →
      p ∣ a.supp.ncard → p ∣ b.supp.ncard := by
    intro a b hab hpa
    induction hab with
    | refl => exact hpa
    | tail hab hbc ih => exact hclosed _ _ ih hbc
  exact hpt (hpropagate hwalk hpc)

/-- Sharpened first-exit form of sector propagation.  If the prime sector
containing a global minimum is proper, some minimum-order `p`-component has
a positive quotient edge directly to a strictly larger `p`-component.  The
rectangular block on that edge is therefore a genuine integral cover: its
reverse quotient is one and its forward quotient is the ratio of orders. -/
theorem exists_minimumToLarger_pDivisible_quotient_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcmin : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard ≤ e.supp.ncard)
    (hpc : p ∣ c.supp.ncard)
    (t : (secondOrderDefectGraph G).ConnectedComponent)
    (hpt : ¬ p ∣ t.supp.ncard) :
    ∃ a e : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ a.supp.ncard ∧ a.supp.ncard = c.supp.ncard ∧
      p ∣ e.supp.ncard ∧ c.supp.ncard < e.supp.ncard ∧
      0 < componentQuotientMatrix G (secondOrderDefectGraph G) a e ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) e a = 1 ∧
      c.supp.ncard ∣ e.supp.ncard ∧
      c.supp.ncard *
        componentQuotientMatrix G (secondOrderDefectGraph G) a e =
          e.supp.ncard := by
  classical
  letI : Nonempty V :=
    ⟨componentRepresentative (secondOrderDefectGraph G) c⟩
  have hedge : ∃ a e : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ a.supp.ncard ∧ a.supp.ncard = c.supp.ncard ∧
      0 < componentQuotientMatrix G (secondOrderDefectGraph G) a e ∧
      c.supp.ncard < e.supp.ncard := by
    by_contra hnone
    push_neg at hnone
    have hclosed (a b : (secondOrderDefectGraph G).ConnectedComponent)
        (ha : p ∣ a.supp.ncard ∧ a.supp.ncard = c.supp.ncard)
        (hab : 0 < componentQuotientMatrix G
          (secondOrderDefectGraph G) a b) :
        p ∣ b.supp.ncard ∧ b.supp.ncard = c.supp.ncard := by
      have hamin : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
          a.supp.ncard ≤ e.supp.ncard := by
        intro e
        rw [ha.2]
        exact hcmin e
      have hpb :=
        prime_dvd_neighbor_order_of_minimumComponent_quotient_pos
          G hfree hd heven hmin hcard a hamin ha.1 b hab
      refine ⟨hpb, Nat.le_antisymm ?_ (by simpa [ha.2] using hcmin b)⟩
      exact hnone a b ha.1 ha.2 hab
    have hwalk := secondOrder_componentQuotientMatrix_irreducible_clean
      G hfree hd heven hmin hcard c t
    have hpropagate : ∀ {a b :
        (secondOrderDefectGraph G).ConnectedComponent},
        Relation.ReflTransGen
          (fun x y => 0 < componentQuotientMatrix G
            (secondOrderDefectGraph G) x y) a b →
        (p ∣ a.supp.ncard ∧ a.supp.ncard = c.supp.ncard) →
        p ∣ b.supp.ncard ∧ b.supp.ncard = c.supp.ncard := by
      intro a b hab ha
      induction hab with
      | refl => exact ha
      | tail hab hbc ih => exact hclosed _ _ ih hbc
    exact hpt (hpropagate hwalk ⟨hpc, rfl⟩).1
  rcases hedge with ⟨a, e, hpa, hac, hpos, hlt⟩
  have haelt : a.supp.ncard < e.supp.ncard := by simpa [hac] using hlt
  have hentries := secondOrder_componentQuotientMatrix_entries_of_size_lt
    G hfree hd heven hmin hcard a e haelt hpos
  have hpe : p ∣ e.supp.ncard :=
    dvd_trans hpa hentries.2.1
  refine ⟨a, e, hpa, hac, hpe, hlt, hpos, hentries.1, ?_, ?_⟩
  · simpa [hac] using hentries.2.1
  · simpa [hac] using hentries.2.2

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
