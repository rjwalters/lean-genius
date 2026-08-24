import Proofs.Erdos85SquareOrderTwoHighTerminal

/-!
# Cut parity in an even-degree relay graph

The Baer owner-routing audit constructs an auxiliary relay graph `P` of
even degree and uses that every componentwise flip cut has even size.  This
file isolates the graph-theoretic statement in the vertex-incidence form
needed by that construction.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Number of oriented incidences leaving `S`.  In a simple undirected graph
each crossing edge contributes exactly once, at its endpoint in `S`. -/
def graphCutMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) : ℕ :=
  ∑ v ∈ S, (H.neighborFinset v \ S).card

/-- The internal-neighbor incidence sum is twice the number of edges of the
induced graph, hence even. -/
theorem even_sum_internalNeighbor_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) :
    Even (∑ v ∈ S, (H.neighborFinset v ∩ S).card) := by
  let K := H.induce (↑S : Set V)
  have hhand := K.sum_degrees_eq_twice_card_edges
  have hsum :
      (∑ v ∈ S, (H.neighborFinset v ∩ S).card) =
        ∑ x : ↥(↑S : Set V), K.degree x := by
    simp only [K, degree_induce_finset_eq_card_inter]
    exact Finset.sum_subtype S (fun _ => Iff.rfl)
      (fun v => (H.neighborFinset v ∩ S).card)
  rw [hsum, hhand]
  exact even_two_mul _

/-- **Eulerian cut parity.**  If every vertex of `H` has even degree, then
the number of incidences leaving any finite vertex set is even. -/
theorem even_graphCutMass_of_even_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdegree : ∀ v, Even (H.degree v)) (S : Finset V) :
    Even (graphCutMass H S) := by
  have hdegreeSum : Even (∑ v ∈ S, H.degree v) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert v S hv ih =>
        rw [Finset.sum_insert hv]
        exact (hdegree v).add ih
  have hinternal := even_sum_internalNeighbor_card H S
  have hsplit :
      (∑ v ∈ S, H.degree v) =
        graphCutMass H S +
          ∑ v ∈ S, (H.neighborFinset v ∩ S).card := by
    simp only [graphCutMass, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    calc
      H.degree v = (H.neighborFinset v).card :=
        (H.card_neighborFinset_eq_degree v).symm
      _ = (H.neighborFinset v \ S).card +
          (H.neighborFinset v ∩ S).card :=
        (Finset.card_sdiff_add_card_inter _ _).symm
  obtain ⟨a, ha⟩ := hdegreeSum
  obtain ⟨b, hb⟩ := hinternal
  use a - b
  omega

end

end Erdos85

#print axioms Erdos85.even_sum_internalNeighbor_card
#print axioms Erdos85.even_graphCutMass_of_even_degree
