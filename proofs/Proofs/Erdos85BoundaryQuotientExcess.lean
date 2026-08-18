import Proofs.Erdos85BoundaryQuotientDivisibility

/-!
# Local excess identities for the boundary quotient

Subtracting the quotient row sum from the diagonal square equation expresses
the excess of a defect-cycle order above three as a sum of nonnegative local
interaction terms.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- The internal quotient degree on a defect component obeys the handshake
parity constraint: component order times internal degree is even. -/
theorem secondOrder_componentQuotientMatrix_diagonal_mul_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    Even (c.supp.ncard *
      componentQuotientMatrix G (secondOrderDefectGraph G) c c) := by
  classical
  let D := secondOrderDefectGraph G
  let cs : Finset V := c.supp.toFinite.toFinset
  let H := G.induce (↑cs : Set V)
  letI : DecidableRel H.Adj := Classical.decRel _
  have hdeg (x : (↑cs : Set V)) :
      H.degree x = componentQuotientMatrix G D c c := by
    have hx : x.1 ∈ c.supp := by simpa [cs] using x.2
    have hQ := componentQuotientMatrix_apply_eq
      G D 2
      (secondOrderDefectGraph_degree_eq_two G hfree hd heven hmin hcard)
      (adjMatrix_comm_secondOrderDefect_of_even_real
        G hfree hd heven hmin hcard)
      c c hx
    have hinduced : H.degree x =
        (cs.filter (fun y => G.Adj x.1 y)).card := by
      show (H.neighborFinset x).card = _
      apply Finset.card_bij (fun y _ => y.1)
      · intro y hy
        rw [SimpleGraph.mem_neighborFinset] at hy
        exact Finset.mem_filter.mpr ⟨y.2, hy⟩
      · intro y₁ h₁ y₂ h₂ hy
        exact Subtype.ext hy
      · intro y hy
        rw [Finset.mem_filter] at hy
        refine ⟨⟨y, hy.1⟩, ?_, rfl⟩
        exact (H.mem_neighborFinset x ⟨y, hy.1⟩).mpr hy.2
    rw [hQ]
    calc
      H.degree x = (cs.filter (fun y => G.Adj x.1 y)).card := hinduced
      _ = (componentNeighborFinset G D c x.1).card := by
        congr 1
        ext y
        simp [cs, componentNeighborFinset,
          SimpleGraph.mem_neighborFinset,
          SimpleGraph.ConnectedComponent.mem_supp_iff, D, and_comm]
  have hsum := H.sum_degrees_eq_twice_card_edges
  have hsum' : Fintype.card (↑cs : Set V) *
      componentQuotientMatrix G D c c = 2 * H.edgeFinset.card := by
    calc
      Fintype.card (↑cs : Set V) * componentQuotientMatrix G D c c =
          ∑ x : (↑cs : Set V), componentQuotientMatrix G D c c := by simp
      _ = ∑ x : (↑cs : Set V), H.degree x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hdeg]
      _ = 2 * H.edgeFinset.card := hsum
  have hcardcs : Fintype.card (↑cs : Set V) = c.supp.ncard := by
    simpa [cs, Nat.card_eq_fintype_card] using
      (Nat.card_coe_set_eq c.supp)
  rw [hcardcs] at hsum'
  change Even (c.supp.ncard * componentQuotientMatrix G D c c)
  exact ⟨H.edgeFinset.card, by omega⟩

/-- For every defect component `c`, the diagonal square equation minus the
row-sum equation is `|c|-3`.  The integer formulation avoids truncated
subtraction and is the natural input for splitting targets by cycle order. -/
theorem secondOrder_componentQuotientMatrix_local_excess
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    (∑ e, ((componentQuotientMatrix G (secondOrderDefectGraph G) c e : ℤ) *
          (componentQuotientMatrix G (secondOrderDefectGraph G) e c : ℤ) -
        (componentQuotientMatrix G (secondOrderDefectGraph G) c e : ℤ))) =
      (c.supp.ncard : ℤ) - 3 := by
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  have hrow : (∑ e, Q c e) = d := by
    exact sum_secondOrder_componentQuotientMatrix_row_eq_degree
      G hfree hd heven hmin hcard c
  have hsq0 := secondOrder_componentQuotientMatrix_sq_apply
    G hfree hd heven hmin hcard c c
  have hsq : (∑ e, Q c e * Q e c) = d - 3 + c.supp.ncard := by
    simpa only [Matrix.mul_apply, Q, D, if_pos, mul_one] using hsq0
  change (∑ e, ((Q c e : ℤ) * (Q e c : ℤ) - (Q c e : ℤ))) = _
  rw [Finset.sum_sub_distrib]
  have hsqZ : (∑ e, (Q c e : ℤ) * (Q e c : ℤ)) =
      ((d - 3 : ℕ) : ℤ) + (c.supp.ncard : ℤ) := by
    exact_mod_cast hsq
  have hrowZ : (∑ e, (Q c e : ℤ)) = (d : ℤ) := by
    exact_mod_cast hrow
  rw [hsqZ, hrowZ]
  rw [Nat.cast_sub (by omega : 3 ≤ d)]
  ring

/-- For a minimum-order defect component, all interactions with longer
components have zero excess.  The entire local excess is carried by quotient
entries to components of the same order. -/
theorem secondOrder_minimumComponent_equalSize_excess
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcmin : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard ≤ e.supp.ncard) :
    (∑ e, if e.supp.ncard = c.supp.ncard then
        (componentQuotientMatrix G (secondOrderDefectGraph G) c e : ℤ) *
          ((componentQuotientMatrix G (secondOrderDefectGraph G) c e : ℤ) - 1)
      else 0) = (c.supp.ncard : ℤ) - 3 := by
  rw [← secondOrder_componentQuotientMatrix_local_excess
    G hfree hd heven hmin hcard c]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hsize : e.supp.ncard = c.supp.ncard
  · have hbalance := secondOrder_componentQuotientMatrix_balance
      G hfree hd heven hmin hcard c e
    rw [hsize] at hbalance
    have hposSize : 0 < c.supp.ncard := c.nonempty_supp.ncard_pos
    have hsym : componentQuotientMatrix G (secondOrderDefectGraph G) c e =
        componentQuotientMatrix G (secondOrderDefectGraph G) e c := by
      exact Nat.eq_of_mul_eq_mul_left hposSize hbalance
    simp only [hsize, if_true, hsym]
    ring
  · have hlt : c.supp.ncard < e.supp.ncard := by
      have := hcmin e
      omega
    by_cases hzero :
        componentQuotientMatrix G (secondOrderDefectGraph G) c e = 0
    · simp [hsize, hzero]
    · have hpos : 0 <
          componentQuotientMatrix G (secondOrderDefectGraph G) c e := by omega
      have hentries := secondOrder_componentQuotientMatrix_entries_of_size_lt
        G hfree hd heven hmin hcard c e hlt hpos
      simp [hsize, hentries.1]

/-- Every minimum-order defect cycle at an even second-order boundary has
odd order.  This is a parity consequence of the equal-size excess identity,
since every summand is a product of consecutive integers. -/
theorem secondOrder_minimumComponent_order_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcmin : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard ≤ e.supp.ncard) :
    Odd c.supp.ncard := by
  have hexcess := secondOrder_minimumComponent_equalSize_excess
    G hfree hd heven hmin hcard c hcmin
  have hevenTerm (e : (secondOrderDefectGraph G).ConnectedComponent) :
      Even (if e.supp.ncard = c.supp.ncard then
        (componentQuotientMatrix G (secondOrderDefectGraph G) c e : ℤ) *
          ((componentQuotientMatrix G (secondOrderDefectGraph G) c e : ℤ) - 1)
        else 0) := by
    split
    · exact Int.even_mul_pred_self _
    · exact Even.zero
  have hevenSum : Even (∑ e, if e.supp.ncard = c.supp.ncard then
      (componentQuotientMatrix G (secondOrderDefectGraph G) c e : ℤ) *
        ((componentQuotientMatrix G (secondOrderDefectGraph G) c e : ℤ) - 1)
      else 0) := by
    rw [even_iff_two_dvd]
    apply Finset.dvd_sum
    intro e he
    exact even_iff_two_dvd.mp (hevenTerm e)
  have hevenDiff : Even ((c.supp.ncard : ℤ) - 3) := hexcess ▸ hevenSum
  rw [← Nat.not_even_iff_odd]
  intro hevenCard
  obtain ⟨a, ha⟩ := hevenCard
  obtain ⟨b, hb⟩ := hevenDiff
  have haZ := congrArg (fun n : ℕ => (n : ℤ)) ha
  push_cast at haZ
  omega

/-- The internal quotient degree of a minimum-order defect component is even:
its component order is odd, while their product is even by handshake. -/
theorem secondOrder_minimumComponent_diagonal_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcmin : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard ≤ e.supp.ncard) :
    Even (componentQuotientMatrix G (secondOrderDefectGraph G) c c) := by
  have hprod := secondOrder_componentQuotientMatrix_diagonal_mul_even
    G hfree hd heven hmin hcard c
  have hodd := secondOrder_minimumComponent_order_odd
    G hfree hd heven hmin hcard c hcmin
  exact (Nat.even_mul.mp hprod).resolve_left
    (Nat.not_even_iff_odd.mpr hodd)

end

end Erdos85
