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

/-- Support of a binary potential, represented by its one-coordinates. -/
def f2PotentialSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    (x : V → ZMod 2) : Finset V :=
  Finset.univ.filter fun v => x v = 1

private theorem sum_f2_eq_card_filter_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (s : Finset V) (x : V → ZMod 2) :
    (∑ v ∈ s, x v) = ((s.filter fun v => x v = 1).card : ZMod 2) := by
  have hz : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  calc
    (∑ v ∈ s, x v) = ∑ v ∈ s, if x v = 1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      rcases hz (x v) with hv | hv
      · simp [hv]
      · simp [hv]
    _ = ((s.filter fun v => x v = 1).card : ZMod 2) := by
      simp

/-- The adjacency action of a binary potential is the parity of the number
of neighbors in its support. -/
theorem f2Potential_neighborSupport_card_cast
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → ZMod 2) (u : V) :
    ((G.neighborFinset u ∩ f2PotentialSupport x).card : ZMod 2) =
      (G.adjMatrix (ZMod 2)).mulVec x u := by
  rw [SimpleGraph.adjMatrix_mulVec_apply,
    sum_f2_eq_card_filter_one]
  congr 2
  ext v
  simp [f2PotentialSupport]

/-- A two-pole binary adjacency equation gives exactly the odd-neighbor
syndrome required by the cut-route theorem. -/
theorem f2Potential_twoPole_odd_neighborSupport_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → ZMod 2) (pole₁ pole₂ : V) (hpoles : pole₁ ≠ pole₂)
    (hpotential : (G.adjMatrix (ZMod 2)).mulVec x =
      f2EndpointSwitch pole₁ pole₂) (u : V) :
    Odd ((G.neighborFinset u ∩ f2PotentialSupport x).card) ↔
      u = pole₁ ∨ u = pole₂ := by
  rw [← ZMod.natCast_eq_one_iff_odd,
    f2Potential_neighborSupport_card_cast, hpotential]
  simp only [f2EndpointSwitch, Pi.add_apply, Pi.single_apply]
  by_cases hu₁ : u = pole₁
  · subst u
    simp [hpoles]
  · by_cases hu₂ : u = pole₂
    · subst u
      simp [hu₁]
    · simp [hu₁, hu₂]

/-- **Binary adjacency potential capstone.**  In an even-valent graph, an
equation `A x = e_pole₁ + e_pole₂` produces an actual walk between the two
poles inside the support cut, with the correct F₂ endpoint boundary. -/
theorem exists_binaryVertexCutGraph_twoPole_walk_of_adjMatrix_mulVec
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → ZMod 2) (pole₁ pole₂ : V) (hpoles : pole₁ ≠ pole₂)
    (heven : ∀ u, Even (G.degree u))
    (hpotential : (G.adjMatrix (ZMod 2)).mulVec x =
      f2EndpointSwitch pole₁ pole₂) :
    ∃ p : (binaryVertexCutGraph G (f2PotentialSupport x)).Walk pole₁ pole₂,
      f2WalkEdgeBoundary p = f2EndpointSwitch pole₁ pole₂ := by
  apply exists_binaryVertexCutGraph_twoPole_walk G
    (f2PotentialSupport x) pole₁ pole₂ heven
  exact f2Potential_twoPole_odd_neighborSupport_iff
    G x pole₁ pole₂ hpoles hpotential

end

end Erdos85

#print axioms Erdos85.binaryVertexCutGraph_degree_odd_iff
#print axioms Erdos85.exists_binaryVertexCutGraph_twoPole_walk
#print axioms Erdos85.f2Potential_neighborSupport_card_cast
#print axioms Erdos85.exists_binaryVertexCutGraph_twoPole_walk_of_adjMatrix_mulVec
