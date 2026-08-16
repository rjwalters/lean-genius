import Proofs.Erdos85OneHighTriangleTargetSeparation

/-!
# Target separation for four-cycle exchanged-miss support

This is the endpoint-oriented graph package paired with the abstract
all-distinct four-key classification.  Each label of the support cycle occurs
on two exchanged edges, and its two selected far-branch targets are distinct.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- For oriented exchanged pairs `(u,w)`, `(w,r)`, `(r,t)`, `(t,u)`, distinct
source endpoints at each shared label force four corresponding target
separations. -/
theorem cycle4_crossTargets_pairwise_separated
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    {s u w r t : {z : V // z ∈ G.neighborSet v}}
    {x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ : V}
    (hx₁ : x₁ ∈ secondLayerBranch G v s)
    (hy₁ : y₁ ∈ secondLayerBranch G v s)
    (hx₂ : x₂ ∈ secondLayerBranch G v s)
    (hy₂ : y₂ ∈ secondLayerBranch G v s)
    (hx₃ : x₃ ∈ secondLayerBranch G v s)
    (hy₃ : y₃ ∈ secondLayerBranch G v s)
    (hx₄ : x₄ ∈ secondLayerBranch G v s)
    (hy₄ : y₄ ∈ secondLayerBranch G v s)
    (qUW : OneHighExchangedCrossWitness G v u w x₁ y₁)
    (qWR : OneHighExchangedCrossWitness G v w r x₂ y₂)
    (qRT : OneHighExchangedCrossWitness G v r t x₃ y₃)
    (qTU : OneHighExchangedCrossWitness G v t u x₄ y₄)
    (huSources : y₁ ≠ x₄)
    (hwSources : x₁ ≠ y₂)
    (hrSources : x₂ ≠ y₃)
    (htSources : x₃ ≠ y₄) :
    qUW.uTarget ≠ qTU.wTarget ∧
      qUW.wTarget ≠ qWR.uTarget ∧
      qWR.wTarget ≠ qRT.uTarget ∧
      qRT.wTarget ≠ qTU.uTarget := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ne_crossTargets_of_distinct_sourceVertices
      G hfree hy₁ hx₄ huSources qUW.uTarget_mem qTU.wTarget_mem
      qUW.y_adj_uTarget qTU.x_adj_wTarget
  · exact ne_crossTargets_of_distinct_sourceVertices
      G hfree hx₁ hy₂ hwSources qUW.wTarget_mem qWR.uTarget_mem
      qUW.x_adj_wTarget qWR.y_adj_uTarget
  · exact ne_crossTargets_of_distinct_sourceVertices
      G hfree hx₂ hy₃ hrSources qWR.wTarget_mem qRT.uTarget_mem
      qWR.x_adj_wTarget qRT.y_adj_uTarget
  · exact ne_crossTargets_of_distinct_sourceVertices
      G hfree hx₃ hy₄ htSources qRT.wTarget_mem qTU.uTarget_mem
      qRT.x_adj_wTarget qTU.y_adj_uTarget

end

end Erdos85
