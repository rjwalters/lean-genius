import Proofs.Erdos85ActiveBrokenRelayResidualPricePreservation
import Proofs.Erdos85GraphEdgeIndicatorPotential
import Proofs.Erdos85EulerianCutParity
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Odd residual price forces odd holonomy in an Eulerian routing graph

On an even-valent routing graph, an additive K-edge potential makes the
K-edges exactly a vertex cut, whose size is even.  Consequently an odd
number of K-edges rules out the additive branch of the price dichotomy and
forces a closed walk of odd K-weight.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The edge count of a binary vertex cut equals its oriented cut mass. -/
theorem binaryVertexCutGraph_card_edges_eq_graphCutMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V) [DecidableRel P.Adj] (S : Finset V) :
    (binaryVertexCutGraph P S).edgeFinset.card = graphCutMass P S := by
  let C := binaryVertexCutGraph P S
  have hbip : C.IsBipartiteWith (↑S : Set V) (↑(Sᶜ) : Set V) := by
    refine ⟨Set.disjoint_left.mpr (by simp), ?_⟩
    intro u v huv
    change P.Adj u v ∧ (u ∈ S) ≠ (v ∈ S) at huv
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp_all
  change (binaryVertexCutGraph P S).IsBipartiteWith
    (↑S : Set V) (↑(Sᶜ) : Set V) at hbip
  rw [← SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hbip]
  rw [graphCutMass]
  apply Finset.sum_congr rfl
  intro v hv
  rw [binaryVertexCutGraph_degree_eq, if_pos hv]

/-- An endpoint potential makes the priced routing edges exactly a vertex
cut of the routing graph. -/
theorem inf_eq_binaryVertexCutGraph_of_graphEdgeIndicator_potential
    {V : Type*} [Fintype V] [DecidableEq V]
    (P K : SimpleGraph V) [DecidableRel P.Adj] [DecidableRel K.Adj]
    (lam : V → ZMod 2)
    (hpotential : ∀ {u v}, P.Adj u v →
      graphEdgeIndicator K u v = lam u + lam v) :
    P ⊓ K = binaryVertexCutGraph P (f2PotentialSupport lam) := by
  ext u v
  change (P.Adj u v ∧ K.Adj u v) ↔
    (P.Adj u v ∧
      (u ∈ f2PotentialSupport lam) ≠ (v ∈ f2PotentialSupport lam))
  have hbinary : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hbinary (lam u) with hu | hu <;>
    rcases hbinary (lam v) with hv | hv
  all_goals
    constructor
    · rintro ⟨hP, hK⟩
      refine ⟨hP, ?_⟩
      have hi : lam u + lam v = 1 := by
        calc
          lam u + lam v = graphEdgeIndicator K u v := (hpotential hP).symm
          _ = 1 := (graphEdgeIndicator_eq_one_iff K).mpr hK
      simp [f2PotentialSupport, hu, hv] at hi ⊢
    · rintro ⟨hP, hdiff⟩
      have hi : lam u + lam v = 1 := by
        simp [f2PotentialSupport, hu, hv] at hdiff ⊢
      exact ⟨hP, (graphEdgeIndicator_eq_one_iff K).mp ((hpotential hP).trans hi)⟩

/-- If `P` is even-valent and the additive K-potential exists, then `P∩K`
has an even number of edges. -/
theorem even_card_inf_of_even_degree_of_graphEdgeIndicator_potential
    {V : Type*} [Fintype V] [DecidableEq V]
    (P K : SimpleGraph V) [DecidableRel P.Adj] [DecidableRel K.Adj]
    (heven : ∀ v, Even (P.degree v)) (lam : V → ZMod 2)
    (hpotential : ∀ {u v}, P.Adj u v →
      graphEdgeIndicator K u v = lam u + lam v) :
    Even ((P ⊓ K).edgeFinset.card) := by
  have hgraph := inf_eq_binaryVertexCutGraph_of_graphEdgeIndicator_potential
    P K lam hpotential
  have hcard : (P ⊓ K).edgeFinset.card =
      (binaryVertexCutGraph P (f2PotentialSupport lam)).edgeFinset.card := by
    congr 1
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    have hm := congrArg (fun H : SimpleGraph V => e ∈ H.edgeSet) hgraph
    constructor
    · exact Eq.mp hm
    · exact Eq.mpr hm
  rw [hcard, binaryVertexCutGraph_card_edges_eq_graphCutMass]
  exact even_graphCutMass_of_even_degree P heven (f2PotentialSupport lam)

/-- **Eulerian odd-price terminal.**  In a connected even-valent routing
graph, odd total K-price forces a closed walk with odd K-holonomy. -/
theorem exists_closedWalk_odd_graphEdgeIndicator_of_even_degree_of_odd_inf
    {V : Type*} [Fintype V] [DecidableEq V]
    (P K : SimpleGraph V) [DecidableRel P.Adj] [DecidableRel K.Adj]
    (root : V) (hconn : ∀ v, Nonempty (P.Walk root v))
    (heven : ∀ v, Even (P.degree v))
    (hodd : Odd ((P ⊓ K).edgeFinset.card)) :
    ∃ (u : V) (p : P.Walk u u),
      f2WalkWeight (graphEdgeIndicator K) p = 1 := by
  rcases exists_closedWalk_odd_graphEdgeIndicator_or_exists_vertexPotential
    P K root hconn with hwalk | ⟨lam, hpotential⟩
  · exact hwalk
  · have he := even_card_inf_of_even_degree_of_graphEdgeIndicator_potential
        P K heven lam hpotential
    obtain ⟨a, ha⟩ := hodd
    obtain ⟨b, hb⟩ := he
    omega

/-- Specialization to the exact active-broken Eulerization `Q_s`.  On a
connected `Q_s` component, odd residual K-price forces odd K-holonomy. -/
theorem activeBrokenRelay_exists_closedWalk_odd_residual_of_odd_inf
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A) {q : ℕ} (hq : Even q)
    (hreg : ∀ v, A.degree v = q) (x : V → ZMod 2)
    (mate : V → V → V)
    (hclosed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      (triangleFreeEdgeGraph A).Adj w (mate w v))
    (hinvol : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w (mate w v) = v)
    (hfixed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w v ≠ v)
    (root : V)
    (hconn : ∀ v, Nonempty ((graphF2SymmetricDifference
      (activeBrokenWitnessRelayGraph A (fun w => x w = 1) mate
        hclosed hinvol hfixed)
      (binaryVertexCutGraph (triangleFreeEdgeGraph A)
        (f2PotentialSupport x))).Walk root v))
    (hodd : Odd (((graphF2SymmetricDifference
      (activeBrokenWitnessRelayGraph A (fun w => x w = 1) mate
        hclosed hinvol hfixed)
      (binaryVertexCutGraph (triangleFreeEdgeGraph A)
        (f2PotentialSupport x))) ⊓
      binaryTransportResidualGraph A hq hreg).edgeFinset.card)) :
    ∃ (u : V) (p : (graphF2SymmetricDifference
        (activeBrokenWitnessRelayGraph A (fun w => x w = 1) mate
          hclosed hinvol hfixed)
        (binaryVertexCutGraph (triangleFreeEdgeGraph A)
          (f2PotentialSupport x))).Walk u u),
      f2WalkWeight (graphEdgeIndicator
        (binaryTransportResidualGraph A hq hreg)) p = 1 := by
  apply exists_closedWalk_odd_graphEdgeIndicator_of_even_degree_of_odd_inf
    _ _ root hconn
  · exact activeBrokenRelay_cut_symmDiff_even_degree_of_evenRegular
      A hfree q hreg hq x mate hclosed hinvol hfixed
  · exact hodd

end

end Erdos85

#print axioms Erdos85.binaryVertexCutGraph_card_edges_eq_graphCutMass
#print axioms Erdos85.inf_eq_binaryVertexCutGraph_of_graphEdgeIndicator_potential
#print axioms Erdos85.even_card_inf_of_even_degree_of_graphEdgeIndicator_potential
#print axioms Erdos85.exists_closedWalk_odd_graphEdgeIndicator_of_even_degree_of_odd_inf
#print axioms Erdos85.activeBrokenRelay_exists_closedWalk_odd_residual_of_odd_inf
