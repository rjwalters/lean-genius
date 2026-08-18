import Proofs.Erdos85BoundaryQuotientDivisibility
import Proofs.Erdos85ComponentFactorization

/-!
# Interfaces for minimum-sector assembly

This file exposes three bookkeeping facts used by the large-prime sector
terminal: the reverse quotient entry on a proper minimum-to-larger edge,
detailed balance after normalizing component orders by a common prime, and
summation over the partition into connected-component supports.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- A positive quotient edge from a minimum component to a strictly larger
component has reverse quotient entry one.  This names the first projection
of `secondOrder_componentQuotientMatrix_entries_of_size_lt` for downstream
assembly proofs. -/
theorem secondOrder_minimumComponent_larger_reverseEntry_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hlt : c.supp.ncard < e.supp.ncard)
    (hpos : 0 < componentQuotientMatrix G
      (secondOrderDefectGraph G) c e) :
    componentQuotientMatrix G (secondOrderDefectGraph G) e c = 1 := by
  exact (secondOrder_componentQuotientMatrix_entries_of_size_lt
    G hfree hd heven hmin hcard c e hlt hpos).1

/-- Detailed balance with a common positive factor cancelled.  If the source
and target orders are `a*p` and `m*p`, and the reverse quotient entry is one,
then the forward entry is the normalized target order `m/a`. -/
theorem componentQuotientMatrix_normalized_balance
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    (k : ℕ) (hreg : ∀ x : V, D.degree x = k)
    (hcomm : G.adjMatrix ℝ * D.adjMatrix ℝ =
      D.adjMatrix ℝ * G.adjMatrix ℝ)
    (c e : D.ConnectedComponent) (p a m : ℕ) (hp : 0 < p)
    (hc : c.supp.ncard = a * p) (he : e.supp.ncard = m * p)
    (hrev : componentQuotientMatrix G D e c = 1) :
    a * componentQuotientMatrix G D c e = m := by
  have hbalance := componentQuotientMatrix_balance
    G D k hreg hcomm c e
  rw [hc, he, hrev, mul_one] at hbalance
  have hpEq : p * (a * componentQuotientMatrix G D c e) = p * m := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hbalance
  exact Nat.eq_of_mul_eq_mul_left hp hpEq

/-- Reindex a finite vertex sum by the canonical partition into connected
component supports. -/
theorem sum_vertex_eq_sum_connectedComponent_supp
    {V R : Type*} [Fintype V] (D : SimpleGraph V)
    [Fintype D.ConnectedComponent]
    [∀ c : D.ConnectedComponent, Fintype c.supp]
    [AddCommMonoid R] (f : V → R) :
    (∑ x : V, f x) =
      ∑ c : D.ConnectedComponent, ∑ x : c.supp, f x.1 := by
  have hreindex := Equiv.sum_comp (vertexConnectedComponentEquiv D)
    (fun z : Σ c : D.ConnectedComponent, c.supp ↦ f z.2.1)
  rw [Fintype.sum_sigma] at hreindex
  simpa [vertexConnectedComponentEquiv] using hreindex

/-- If a natural-valued function is constant on every connected-component
support, its global sum is the component-order-weighted sum of those values. -/
theorem sum_vertex_eq_sum_component_ncard_mul
    {V : Type*} [Fintype V] (D : SimpleGraph V)
    [Fintype D.ConnectedComponent]
    [∀ c : D.ConnectedComponent, Fintype c.supp]
    (f : V → ℕ) (g : D.ConnectedComponent → ℕ)
    (hconst : ∀ c : D.ConnectedComponent, ∀ x : V,
      x ∈ c.supp → f x = g c) :
    (∑ x : V, f x) =
      ∑ c : D.ConnectedComponent, c.supp.ncard * g c := by
  rw [sum_vertex_eq_sum_connectedComponent_supp D f]
  apply Finset.sum_congr rfl
  intro c hc
  calc
    (∑ x : c.supp, f x.1) = ∑ _x : c.supp, g c := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hconst c x.1 x.2
    _ = Fintype.card c.supp * g c := by simp
    _ = c.supp.ncard * g c := by
      congr 1
      simpa [Nat.card_eq_fintype_card] using
        (Nat.card_coe_set_eq c.supp).symm

end

end Erdos85
