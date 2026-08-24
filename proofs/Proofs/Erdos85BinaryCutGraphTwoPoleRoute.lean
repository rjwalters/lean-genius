import Proofs.Erdos85TwoOddVerticesRoute

/-!
# Binary cut graphs and the two-pole route

For an even-valent graph, the parity of a vertex's degree across a cut is
the parity of its number of neighbors on either shore.  Therefore a binary
potential whose adjacency syndrome is supported at two poles makes the cut
graph odd exactly at those poles; the two-odd-vertices theorem then supplies
the route from (73rnz_bl).
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The spanning subgraph consisting of edges crossing the vertex cut `X`. -/
def binaryVertexCutGraph
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (X : Finset V) :
    SimpleGraph V where
  Adj u v := G.Adj u v ∧ (u ∈ X) ≠ (v ∈ X)
  symm := ⟨by
    rintro u v ⟨huv, hcut⟩
    exact ⟨huv.symm, fun h => hcut h.symm⟩⟩
  loopless := ⟨by
    intro u h
    exact G.loopless.irrefl u h.1⟩

instance binaryVertexCutGraph_instDecidableRelAdj
    {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (X : Finset V) :
    DecidableRel (binaryVertexCutGraph G X).Adj := fun u v => by
  change Decidable (G.Adj u v ∧ (u ∈ X) ≠ (v ∈ X))
  infer_instance

/-- The cut neighbors are the opposite-shore ambient neighbors. -/
theorem binaryVertexCutGraph_neighborFinset_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) (u : V) :
    (binaryVertexCutGraph G X).neighborFinset u =
      if u ∈ X then G.neighborFinset u \ X
      else G.neighborFinset u ∩ X := by
  classical
  ext v
  by_cases hu : u ∈ X <;>
    simp [binaryVertexCutGraph, SimpleGraph.mem_neighborFinset, hu]

/-- Degree form of the cut-neighbor identity. -/
theorem binaryVertexCutGraph_degree_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) (u : V) :
    (binaryVertexCutGraph G X).degree u =
      if u ∈ X then (G.neighborFinset u \ X).card
      else (G.neighborFinset u ∩ X).card := by
  rw [← (binaryVertexCutGraph G X).card_neighborFinset_eq_degree,
    binaryVertexCutGraph_neighborFinset_eq]
  split <;> rfl

private theorem odd_iff_odd_of_even_add {a b : ℕ} (heven : Even (a + b)) :
    Odd a ↔ Odd b := by
  rcases heven with ⟨k, hk⟩
  constructor
  · rintro ⟨m, hm⟩
    use k - m - 1
    omega
  · rintro ⟨m, hm⟩
    use k - m - 1
    omega

/-- In an even-valent ambient graph, cut-degree parity is exactly the
neighbor-incidence parity of the chosen shore. -/
theorem binaryVertexCutGraph_degree_odd_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) (u : V)
    (heven : Even (G.degree u)) :
    Odd ((binaryVertexCutGraph G X).degree u) ↔
      Odd ((G.neighborFinset u ∩ X).card) := by
  by_cases hu : u ∈ X
  · rw [binaryVertexCutGraph_degree_eq, if_pos hu]
    have hpartition := Finset.card_inter_add_card_sdiff
      (G.neighborFinset u) X
    have hcard : (G.neighborFinset u).card = G.degree u :=
      G.card_neighborFinset_eq_degree u
    have hevenSum : Even
        ((G.neighborFinset u ∩ X).card +
          (G.neighborFinset u \ X).card) := by
      rw [hpartition, hcard]
      exact heven
    exact (odd_iff_odd_of_even_add hevenSum).symm
  · rw [binaryVertexCutGraph_degree_eq, if_neg hu]

/-- **Potential-to-route bridge.**  If the ambient graph is even-valent and
the parity of `|N(u)∩X|` is supported exactly at two poles, the cut graph
contains a pole-to-pole walk whose F₂ edge boundary is their endpoint
switch. -/
theorem exists_binaryVertexCutGraph_twoPole_walk
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (pole₁ pole₂ : V)
    (heven : ∀ u, Even (G.degree u))
    (hsyndrome : ∀ u,
      Odd ((G.neighborFinset u ∩ X).card) ↔
        u = pole₁ ∨ u = pole₂) :
    ∃ p : (binaryVertexCutGraph G X).Walk pole₁ pole₂,
      f2WalkEdgeBoundary p = f2EndpointSwitch pole₁ pole₂ := by
  apply exists_walk_of_odd_degree_iff_eq_two
  intro u
  rw [binaryVertexCutGraph_degree_odd_iff G X u (heven u)]
  exact hsyndrome u

end

end Erdos85

#print axioms Erdos85.binaryVertexCutGraph_degree_odd_iff
#print axioms Erdos85.exists_binaryVertexCutGraph_twoPole_walk
