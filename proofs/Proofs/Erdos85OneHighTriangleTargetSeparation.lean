import Proofs.Erdos85OneHighRepeatedPairTargets

/-!
# Target separation for triangular exchanged-miss support

The same far-branch target cannot serve two distinct endpoints in one source
branch: together with the source root it would have two common neighbors.
This elementary injection packages the three instances needed when three
exchanged-label edges have triangle support.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Distinct source-branch vertices that hit one far branch must hit distinct
targets there.  The internal matching edges that produced the vertices are
irrelevant once the two oriented cross incidences are known. -/
theorem ne_crossTargets_of_distinct_sourceVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    {s u : {z : V // z ∈ G.neighborSet v}}
    {x₁ x₂ a₁ a₂ : V}
    (hx₁ : x₁ ∈ secondLayerBranch G v s)
    (hx₂ : x₂ ∈ secondLayerBranch G v s)
    (hxne : x₁ ≠ x₂)
    (ha₁ : a₁ ∈ secondLayerBranch G v u)
    (ha₂ : a₂ ∈ secondLayerBranch G v u)
    (hxa₁ : G.Adj x₁ a₁) (hxa₂ : G.Adj x₂ a₂) :
    a₁ ≠ a₂ := by
  intro heq
  subst a₂
  have hsa : s.1 ≠ a₁ := by
    intro h
    subst a₁
    exact (Finset.mem_sdiff.mp ha₂).2 (by
      simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
      exact Or.inr s.2)
  have hsX₁ : G.Adj x₁ s.1 :=
    ((G.mem_neighborFinset s.1 x₁).mp
      (Finset.mem_sdiff.mp hx₁).1).symm
  have hsX₂ : G.Adj x₂ s.1 :=
    ((G.mem_neighborFinset s.1 x₂).mp
      (Finset.mem_sdiff.mp hx₂).1).symm
  exact hfree (containsC4_of_two_common hsa hxne
    hsX₁ hxa₁ hsX₂ hxa₂)

/-- Endpoint-oriented triangle package.  The three exchanged edges use far
pairs `(u,w)`, `(w,r)`, and `(r,u)`.  If the two source endpoints assigned to
each shared label are distinct, then the corresponding selected targets are
distinct as well.  Label decoders may choose these orientations upstream. -/
theorem triangle_crossTargets_pairwise_separated
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    {s u w r : {z : V // z ∈ G.neighborSet v}}
    {x₁ y₁ x₂ y₂ x₃ y₃ : V}
    (hx₁ : x₁ ∈ secondLayerBranch G v s)
    (hy₁ : y₁ ∈ secondLayerBranch G v s)
    (hx₂ : x₂ ∈ secondLayerBranch G v s)
    (hy₂ : y₂ ∈ secondLayerBranch G v s)
    (hx₃ : x₃ ∈ secondLayerBranch G v s)
    (hy₃ : y₃ ∈ secondLayerBranch G v s)
    (qUW : OneHighExchangedCrossWitness G v u w x₁ y₁)
    (qWR : OneHighExchangedCrossWitness G v w r x₂ y₂)
    (qRU : OneHighExchangedCrossWitness G v r u x₃ y₃)
    (huSources : y₁ ≠ x₃)
    (hwSources : x₁ ≠ y₂)
    (hrSources : x₂ ≠ y₃) :
    qUW.uTarget ≠ qRU.wTarget ∧
      qUW.wTarget ≠ qWR.uTarget ∧
      qWR.wTarget ≠ qRU.uTarget := by
  refine ⟨?_, ?_, ?_⟩
  · exact ne_crossTargets_of_distinct_sourceVertices
      G hfree hy₁ hx₃ huSources qUW.uTarget_mem qRU.wTarget_mem
      qUW.y_adj_uTarget qRU.x_adj_wTarget
  · exact ne_crossTargets_of_distinct_sourceVertices
      G hfree hx₁ hy₂ hwSources qUW.wTarget_mem qWR.uTarget_mem
      qUW.x_adj_wTarget qWR.y_adj_uTarget
  · exact ne_crossTargets_of_distinct_sourceVertices
      G hfree hx₂ hy₃ hrSources qWR.wTarget_mem qRU.uTarget_mem
      qWR.x_adj_wTarget qRU.y_adj_uTarget

end

end Erdos85
