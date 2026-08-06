import Proofs.Erdos85AdjacentCloneEdgeDelete

/-!
# Local rigidity at the sharp adjacent-clone threshold

The adjacent-clone and edge-deletion surgeries combine into a concise
equality-case description.  If a `C₄`-free minimum-degree-`d` witness cannot
be extended by one vertex and a vertex reaches degree `2d-2`, then:

* its degree is exactly `2d-2`;
* `d` is even;
* every component of its induced neighbourhood has two vertices (so the
  neighbourhood is a perfect matching); and
* every edge of that matching has an endpoint of degree exactly `d`.

This is a uniform local structure theorem for an arbitrary plateau
obstruction, not only for a Moore-boundary graph.
-/

open SimpleGraph

namespace Erdos85

/-- **Sharp-threshold local rigidity.**  Failure of every one-vertex
extension at a vertex of degree at least `2d-2` forces the unique parity
obstruction to adjacent cloning, together with the tight-endpoint condition
forced by edge deletion. -/
theorem local_threshold_rigidity_of_not_witness_succ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    {N d : ℕ} (hVcard : Fintype.card V = N)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G)
    (hd : 1 ≤ d) (hno : ¬ C4FreeMinDegreeWitness (N + 1) d)
    (hxdegree : 2 * d - 2 ≤ G.degree x) :
    G.degree x = 2 * d - 2 ∧
      Even d ∧
      (∀ c : (deletedNeighborhoodInducedGraph G x).ConnectedComponent,
        c.supp.ncard = 2) ∧
      (∀ a b : V, G.Adj a x → G.Adj b x → G.Adj a b →
        G.degree a = d ∨ G.degree b = d) := by
  have hupper := degree_le_two_mul_sub_two_of_not_witness_succ
    G hVcard hmin hfree hd hno x
  have hxeq : G.degree x = 2 * d - 2 := by omega
  have hdeven : Even d := by
    rcases Nat.even_or_odd d with heven | hodd
    · exact heven
    · have hdOdd : d % 2 = 1 := Nat.odd_iff.mp hodd
      exact (hno
        (c4FreeMinDegreeWitness_succ_of_odd_vertex_degree_ge_two_mul_sub_two
          G x hVcard hmin hfree hd hdOdd hxdegree)).elim
  refine ⟨hxeq, hdeven, ?_, ?_⟩
  · exact
      localComponents_eq_two_of_not_witness_succ_of_degree_ge_two_mul_sub_two
        G x hVcard hmin hfree hd hno hxdegree
  · intro a b hax hbx hab
    exact threshold_localEdge_has_tight_endpoint_of_not_witness_succ
      G x a b hVcard hmin hfree hd hno hxdegree hax hbx hab

/-- Global contrapositive form: in a nonextendable witness, every vertex at
the sharp upper-degree threshold carries the rigid matched neighbourhood
described above. -/
theorem every_threshold_vertex_locally_rigid_of_not_witness_succ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {N d : ℕ} (hVcard : Fintype.card V = N)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G)
    (hd : 1 ≤ d) (hno : ¬ C4FreeMinDegreeWitness (N + 1) d) :
    ∀ x : V, 2 * d - 2 ≤ G.degree x →
      G.degree x = 2 * d - 2 ∧
        Even d ∧
        (∀ c : (deletedNeighborhoodInducedGraph G x).ConnectedComponent,
          c.supp.ncard = 2) ∧
        (∀ a b : V, G.Adj a x → G.Adj b x → G.Adj a b →
          G.degree a = d ∨ G.degree b = d) := by
  intro x hx
  exact local_threshold_rigidity_of_not_witness_succ
    G x hVcard hmin hfree hd hno hx

end Erdos85
