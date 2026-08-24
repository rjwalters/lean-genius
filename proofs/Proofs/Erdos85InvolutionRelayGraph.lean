import Proofs.Erdos85EulerianCutParity

/-!
# Relay graphs obtained from an involution matching

The Baer routing graph `P` is the union of its base `T` edges with one
chosen pairing edge at every endpoint.  Abstractly that pairing is a
fixed-point-free involution.  This file constructs the resulting matching
graph and proves the exact neighbor and degree formulas needed for the
Eulerian cut argument.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The perfect matching encoded by a fixed-point-free involution. -/
def involutionMatchingGraph
    {V : Type*} (mate : V → V)
    (hinvol : Function.Involutive mate)
    (hfixed : ∀ v, mate v ≠ v) : SimpleGraph V where
  Adj u v := mate u = v
  symm := by
    constructor
    intro u v huv
    have h := congrArg mate huv
    rw [hinvol u] at h
    exact h.symm
  loopless := by
    constructor
    intro v hv
    exact hfixed v hv

instance involutionMatchingGraph_decidableAdj
    {V : Type*} [DecidableEq V] (mate : V → V)
    (hinvol : Function.Involutive mate) (hfixed : ∀ v, mate v ≠ v) :
    DecidableRel (involutionMatchingGraph mate hinvol hfixed).Adj :=
  fun u v => inferInstanceAs (Decidable (mate u = v))

/-- Every vertex has its involutive mate as its unique matching neighbor. -/
theorem involutionMatchingGraph_neighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (mate : V → V) (hinvol : Function.Involutive mate)
    (hfixed : ∀ v, mate v ≠ v) (v : V) :
    (involutionMatchingGraph mate hinvol hfixed).neighborFinset v =
      {mate v} := by
  classical
  ext w
  simp [SimpleGraph.mem_neighborFinset, involutionMatchingGraph, eq_comm]

/-- Adjoin one pairing edge at every vertex to a base relay graph. -/
def involutionRelayGraph
    {V : Type*} (T : SimpleGraph V) (mate : V → V)
    (hinvol : Function.Involutive mate)
    (hfixed : ∀ v, mate v ≠ v) : SimpleGraph V :=
  T ⊔ involutionMatchingGraph mate hinvol hfixed

instance involutionRelayGraph_decidableAdj
    {V : Type*} [DecidableEq V] (T : SimpleGraph V)
    [DecidableRel T.Adj] (mate : V → V)
    (hinvol : Function.Involutive mate) (hfixed : ∀ v, mate v ≠ v) :
    DecidableRel (involutionRelayGraph T mate hinvol hfixed).Adj := by
  intro u v
  change Decidable (T.Adj u v ∨ mate u = v)
  infer_instance

/-- The relay neighborhood is the union of the base neighborhood and the
single matching mate. -/
theorem involutionRelayGraph_neighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj]
    (mate : V → V) (hinvol : Function.Involutive mate)
    (hfixed : ∀ v, mate v ≠ v) (v : V) :
    (involutionRelayGraph T mate hinvol hfixed).neighborFinset v =
      T.neighborFinset v ∪ {mate v} := by
  classical
  ext w
  simp [SimpleGraph.mem_neighborFinset, involutionRelayGraph,
    involutionMatchingGraph, or_comm, eq_comm]

/-- If the chosen matching edge was not already a base edge, adjoining it
raises the degree by exactly one. -/
theorem involutionRelayGraph_degree_eq_add_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj]
    (mate : V → V) (hinvol : Function.Involutive mate)
    (hfixed : ∀ v, mate v ≠ v)
    (hdisjoint : ∀ v, ¬ T.Adj v (mate v)) (v : V) :
    (involutionRelayGraph T mate hinvol hfixed).degree v =
      T.degree v + 1 := by
  classical
  rw [← (involutionRelayGraph T mate hinvol hfixed).card_neighborFinset_eq_degree,
    involutionRelayGraph_neighborFinset]
  have hnotMem : mate v ∉ T.neighborFinset v := by
    simpa [SimpleGraph.mem_neighborFinset] using hdisjoint v
  rw [Finset.card_union_of_disjoint]
  · simp [T.card_neighborFinset_eq_degree]
  · simp [Finset.disjoint_singleton_right, hnotMem]

/-- An odd-degree base graph plus its disjoint involution matching is
Eulerian. -/
theorem involutionRelayGraph_even_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj]
    (mate : V → V) (hinvol : Function.Involutive mate)
    (hfixed : ∀ v, mate v ≠ v)
    (hdisjoint : ∀ v, ¬ T.Adj v (mate v))
    (hodd : ∀ v, Odd (T.degree v)) (v : V) :
    Even ((involutionRelayGraph T mate hinvol hfixed).degree v) := by
  classical
  rw [involutionRelayGraph_degree_eq_add_one T mate hinvol hfixed hdisjoint]
  exact (hodd v).add_one

end

end Erdos85

#print axioms Erdos85.involutionMatchingGraph_neighborFinset
#print axioms Erdos85.involutionRelayGraph_degree_eq_add_one
#print axioms Erdos85.involutionRelayGraph_even_degree
