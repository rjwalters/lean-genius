import Proofs.Erdos85DefectCliqueEscapeHatch
import Proofs.Erdos85ConflictDefectDuality
import Proofs.Erdos85SafeSetCounting

/-!
# Defect-clique rigidity in a nonextendable graph

The escape-hatch surgery is most naturally triggered by a clique in the
second-order defect graph.  Conflict--defect duality turns such a clique
into the pairwise zero-common-neighbor set required by the surgery.  Hence,
under one-step nonextension, every sufficiently large defect clique must
meet or reach every open neighborhood within two graph edges.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A clique in the second-order defect graph is a safe attachment set in
the original graph. -/
theorem commonNeighborIndependent_of_secondOrderDefect_isClique
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (C : Finset V)
    (hclique : (secondOrderDefectGraph G).IsClique (C : Set V)) :
    CommonNeighborIndependent G C := by
  have hdual := commonNeighborConflict_compl_eq_secondOrderDefectGraph
    G hfree
  apply (commonNeighborIndependent_iff_isIndepSet G C).2
  rw [SimpleGraph.isIndepSet_iff]
  intro a ha b hb hab hconf
  have hD : (secondOrderDefectGraph G).Adj a b := hclique ha hb hab
  have hcomp : (commonNeighborConflict G)ᶜ.Adj a b := by
    rw [hdual]
    exact hD
  rw [SimpleGraph.compl_adj] at hcomp
  exact hcomp.2 hconf

/-- If a safe set is also independent in `G`, then the set itself is
disjoint from all of its already pairwise-disjoint open neighborhoods. -/
theorem CommonNeighborIndependent.card_add_sum_degrees_le_card_of_isIndepSet
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V)
    (hsafe : CommonNeighborIndependent G C)
    (hind : G.IsIndepSet (C : Set V)) :
    C.card + ∑ x ∈ C, G.degree x ≤ Fintype.card V := by
  classical
  let X := {x : V // x ∈ C}
  let N : X → Type _ := fun x => {v : V // v ∈ G.neighborFinset x.1}
  let f : X ⊕ (Σ x : X, N x) → V := fun p =>
    Sum.elim Subtype.val (fun q => q.2.1) p
  rw [SimpleGraph.isIndepSet_iff] at hind
  have hnoAdj : ∀ x ∈ C, ∀ y ∈ C, ¬ G.Adj x y := by
    intro x hx y hy hxy
    by_cases hne : x = y
    · subst y
      exact G.loopless.irrefl x hxy
    · exact hind hx hy hne hxy
  have hf : Function.Injective f := by
    rintro (x | ⟨x, v⟩) (y | ⟨y, w⟩) heq
    · exact congrArg Sum.inl (Subtype.ext heq)
    · exfalso
      change x.1 = w.1 at heq
      exact hnoAdj y.1 y.2 x.1 x.2
        (by simpa [heq] using (G.mem_neighborFinset y.1 w.1).mp w.2)
    · exfalso
      change v.1 = y.1 at heq
      exact hnoAdj x.1 x.2 y.1 y.2
        (by simpa [heq] using (G.mem_neighborFinset x.1 v.1).mp v.2)
    · have hvw : v.1 = w.1 := heq
      have hxy : x.1 = y.1 := by
        by_contra hxy
        have hz : v.1 ∈ G.neighborFinset x.1 ∩
            G.neighborFinset y.1 := by
          exact Finset.mem_inter.mpr ⟨v.2, hvw ▸ w.2⟩
        have hempty := hsafe x.2 y.2 hxy
        rw [Finset.card_eq_zero] at hempty
        exact Finset.notMem_empty v.1 (hempty ▸ hz)
      have hxySub : x = y := Subtype.ext hxy
      cases hxySub
      have hv : v = w := Subtype.ext hvw
      cases hv
      rfl
  have hcard := Fintype.card_le_of_injective f hf
  change Fintype.card (X ⊕ (Σ x : X, N x)) ≤ Fintype.card V at hcard
  rw [Fintype.card_sum, Fintype.card_sigma] at hcard
  have hCX : Fintype.card X = C.card := by simp [X]
  have hsum : (∑ x : X, Fintype.card (N x)) =
      ∑ x ∈ C, G.degree x := by
    rw [Finset.sum_subtype C (fun _ => Iff.rfl)]
    apply Finset.sum_congr rfl
    intro x hx
    dsimp [N]
    rw [Fintype.card_coe, ← SimpleGraph.card_neighborFinset_eq_degree]
  rwa [hCX, hsum] at hcard

/-- An independent defect clique of size `d-1` can occur in the regular
positive-excess band only at its top endpoint `e=d-4`. -/
theorem excess_eq_sub_four_of_independent_large_secondOrderDefectClique
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 4 ≤ d)
    (he : e ≤ d - 4)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (hreg : ∀ x, G.degree x = d)
    (C : Finset V) (hCcard : C.card = d - 1)
    (hclique : (secondOrderDefectGraph G).IsClique (C : Set V))
    (hind : G.IsIndepSet (C : Set V)) :
    e = d - 4 := by
  have hsafe := commonNeighborIndependent_of_secondOrderDefect_isClique
    G hfree C hclique
  have hcount :=
    hsafe.card_add_sum_degrees_le_card_of_isIndepSet G C hind
  have hsum : (∑ x ∈ C, G.degree x) = C.card * d := by
    simp_rw [hreg]
    simp
  rw [hsum, hCcard, hcard] at hcount
  have hmul : (d - 1) * d = d * (d - 1) := Nat.mul_comm _ _
  rw [hmul] at hcount
  omega

/-- At that forced top endpoint the independent defect clique and its
pairwise-disjoint open neighborhoods exhaust the entire cardinal budget. -/
theorem independent_large_secondOrderDefectClique_count_eq_card
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 4 ≤ d)
    (he : e ≤ d - 4)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (hreg : ∀ x, G.degree x = d)
    (C : Finset V) (hCcard : C.card = d - 1)
    (hclique : (secondOrderDefectGraph G).IsClique (C : Set V))
    (hind : G.IsIndepSet (C : Set V)) :
    C.card + ∑ x ∈ C, G.degree x = Fintype.card V := by
  have heq :=
    excess_eq_sub_four_of_independent_large_secondOrderDefectClique
      G hfree hd he hcard hreg C hCcard hclique hind
  have hsum : (∑ x ∈ C, G.degree x) = C.card * d := by
    simp_rw [hreg]
    simp
  rw [hsum, hCcard, hcard, heq]
  have hmul : (d - 1) * d = d * (d - 1) := Nat.mul_comm _ _
  rw [hmul]
  omega

/-- **Defect-clique plateau rigidity.**  In a graph with no degree-`d`
witness one order higher, every second-order-defect clique of size at least
`d-1` is entangled with every vertex: the vertex lies in the clique, is
adjacent to it, or has a neighbor adjacent to it. -/
theorem secondOrderDefectClique_entangled_of_no_witness
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    {n d : ℕ} (hcard : Fintype.card V = n + 1) (hd : 1 ≤ d)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G)
    (hnext : ¬ C4FreeMinDegreeWitness (n + 2) d)
    (C : Finset V) (hCcard : d - 1 ≤ C.card)
    (hclique : (secondOrderDefectGraph G).IsClique (C : Set V))
    (u : V) :
    u ∈ C ∨ (∃ c ∈ C, G.Adj u c) ∨
      (∃ a ∈ C, ∃ b : V, G.Adj b u ∧ G.Adj a b) := by
  apply defectClique_entangled_of_no_witness
    G hcard hd hmin hfree hnext C hCcard
  intro a ha b hb hab
  have hsafe := commonNeighborIndependent_of_secondOrderDefect_isClique
    G hfree C hclique
  exact hsafe ha hb hab

end

end Erdos85
