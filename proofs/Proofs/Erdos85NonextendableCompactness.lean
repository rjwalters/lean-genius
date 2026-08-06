import Proofs.Erdos85QuadraticConductor
import Proofs.Erdos85LocalThresholdRigidity
import Proofs.Erdos85ProblemConflict

/-!
# Compactness and rigidity of any nonextendable witness

The quadratic conductor and the two universal one-vertex surgeries combine
into a single normal form.  A nonextendable C₄-free minimum-degree-`d`
witness has quadratic order, sharply bounded maximum degree, and conflict
independence number below `d`.
-/

namespace Erdos85

open SimpleGraph

/-- Type-generic conflict-graph extension criterion.  The existing `Fin n`
version is recovered by transporting `Option V`; this form is needed for
induced connected components. -/
theorem c4FreeMinDegreeWitness_succ_of_conflict_indepNum_generic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {N d : ℕ} (hcardV : Fintype.card V = N)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G)
    (hind : d ≤ (commonNeighborConflict G).indepNum) :
    C4FreeMinDegreeWitness (N + 1) d := by
  obtain ⟨S, hsafe, hcardS⟩ :=
    exists_commonNeighborIndependent_card_eq_indepNum G
  let A := attachVertex G S
  have hcardA : Fintype.card (Option V) = N + 1 := by
    simp [hcardV]
  apply c4FreeMinDegreeWitness_of_card_eq A hcardA
  · apply SimpleGraph.le_minDegree_of_forall_le_degree
    rintro (_ | x)
    · exact (hcardS ▸ hind).trans (card_le_attachVertex_degree_none G S)
    · exact (hmin.trans (G.minDegree_le_degree x)).trans
        (degree_le_attachVertex_degree_some G S x)
  · exact (attachVertex_not_containsC4_iff).2 ⟨hfree, hsafe⟩

/-- **Nonextendable-witness compactness.** This statement is independent of
plateau-core packaging and therefore applies verbatim to induced connected
components. -/
theorem nonextendable_witness_compactness
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {N d : ℕ} (hcard : Fintype.card V = N) (hd : 2 ≤ d)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G)
    (hno : ¬ C4FreeMinDegreeWitness (N + 1) d) :
    N + 1 < 36 * d * d ∧
      (∀ v : V, G.degree v ≤ 2 * d - 2) ∧
      (Odd d → ∀ v : V, G.degree v ≤ 2 * d - 3) ∧
      (commonNeighborConflict G).indepNum < d := by
  have horder : N + 1 < 36 * d * d := by
    by_contra hnot
    exact hno (c4FreeMinDegreeWitness_quadratic hd (by omega))
  have hupper : ∀ v : V, G.degree v ≤ 2 * d - 2 :=
    degree_le_two_mul_sub_two_of_not_witness_succ
      G hcard hmin hfree (by omega) hno
  have hoddUpper : Odd d → ∀ v : V, G.degree v ≤ 2 * d - 3 := by
    intro hodd
    exact degree_le_two_mul_sub_three_of_odd_not_witness_succ
      G hcard hmin hfree (by omega) (Nat.odd_iff.mp hodd) hno
  have hind : (commonNeighborConflict G).indepNum < d := by
    by_contra hnot
    have hdind : d ≤ (commonNeighborConflict G).indepNum := by omega
    exact hno (c4FreeMinDegreeWitness_succ_of_conflict_indepNum_generic
      G hcard hmin hfree hdind)
  exact ⟨horder, hupper, hoddUpper, hind⟩

/-- The sharp-threshold equality case is included in the compact normal
form: a vertex of degree `2d-2` forces even `d` and a perfectly matched
deleted neighborhood with tight endpoints. -/
theorem nonextendable_witness_threshold_rigidity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {N d : ℕ} (hcard : Fintype.card V = N) (hd : 2 ≤ d)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G)
    (hno : ¬ C4FreeMinDegreeWitness (N + 1) d) :
    ∀ x : V, 2 * d - 2 ≤ G.degree x →
      G.degree x = 2 * d - 2 ∧
        Even d ∧
        (∀ c : (deletedNeighborhoodInducedGraph G x).ConnectedComponent,
          c.supp.ncard = 2) ∧
        (∀ a b : V, G.Adj a x → G.Adj b x → G.Adj a b →
          G.degree a = d ∨ G.degree b = d) := by
  exact every_threshold_vertex_locally_rigid_of_not_witness_succ
    G hcard hmin hfree (by omega) hno

end Erdos85
