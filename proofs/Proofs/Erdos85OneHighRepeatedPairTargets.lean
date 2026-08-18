import Proofs.Erdos85OneHighSameMissParity

/-!
# Cross-target separation for repeated one-high miss pairs

Two disjoint internal edges in one source branch cannot reuse a cross-target
in either of two far branches: reuse would give that target and the source
root two distinct common neighbors.  Together with the existing rectangle
obstruction, this yields four separated targets and two forced nonedges.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

structure OneHighExchangedCrossWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (u w : {z : V // z ∈ G.neighborSet v}) (x y : V) where
  uTarget : V
  uTarget_mem : uTarget ∈ secondLayerBranch G v u
  wTarget : V
  wTarget_mem : wTarget ∈ secondLayerBranch G v w
  y_adj_uTarget : G.Adj y uTarget
  x_adj_wTarget : G.Adj x wTarget
  targets_not_adj : ¬ G.Adj uTarget wTarget

/-- Two disjoint internal edges exchanging the same ordered far-branch pair
produce distinct targets on both sides, in addition to the two local forced
nonedges. -/
theorem exists_separated_crossTargets_of_two_internalEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    {s u w : {z : V // z ∈ G.neighborSet v}}
    (hsu : s ≠ u) (hsw : s ≠ w)
    {x₁ y₁ x₂ y₂ : V}
    (hx₁ : x₁ ∈ secondLayerBranch G v s)
    (hy₁ : y₁ ∈ secondLayerBranch G v s)
    (hx₂ : x₂ ∈ secondLayerBranch G v s)
    (hy₂ : y₂ ∈ secondLayerBranch G v s)
    (hxy₁ : G.Adj x₁ y₁) (hxy₂ : G.Adj x₂ y₂)
    (hxne : x₁ ≠ x₂) (hyne : y₁ ≠ y₂)
    (hy₁SeesU : (G.neighborFinset y₁ ∩
      secondLayerBranch G v u).card ≠ 0)
    (hx₁SeesW : (G.neighborFinset x₁ ∩
      secondLayerBranch G v w).card ≠ 0)
    (hy₂SeesU : (G.neighborFinset y₂ ∩
      secondLayerBranch G v u).card ≠ 0)
    (hx₂SeesW : (G.neighborFinset x₂ ∩
      secondLayerBranch G v w).card ≠ 0) :
    ∃ q₁ : OneHighExchangedCrossWitness G v u w x₁ y₁,
      ∃ q₂ : OneHighExchangedCrossWitness G v u w x₂ y₂,
        q₁.uTarget ≠ q₂.uTarget ∧
        q₁.wTarget ≠ q₂.wTarget := by
  obtain ⟨a₁, ha₁, b₁, hb₁, hy₁a₁, hx₁b₁, hab₁⟩ :=
    exists_nonadjacent_cross_witnesses_of_different_misses
      G hfree hsu hsw hx₁ hy₁ hxy₁ hy₁SeesU hx₁SeesW
  obtain ⟨a₂, ha₂, b₂, hb₂, hy₂a₂, hx₂b₂, hab₂⟩ :=
    exists_nonadjacent_cross_witnesses_of_different_misses
      G hfree hsu hsw hx₂ hy₂ hxy₂ hy₂SeesU hx₂SeesW
  let q₁ : OneHighExchangedCrossWitness G v u w x₁ y₁ :=
    ⟨a₁, ha₁, b₁, hb₁, hy₁a₁, hx₁b₁, hab₁⟩
  let q₂ : OneHighExchangedCrossWitness G v u w x₂ y₂ :=
    ⟨a₂, ha₂, b₂, hb₂, hy₂a₂, hx₂b₂, hab₂⟩
  refine ⟨q₁, q₂, ?_, ?_⟩
  · dsimp [q₁, q₂]
    intro heq
    subst a₂
    have hsa : s.1 ≠ a₁ := by
      intro h
      subst a₁
      exact (Finset.mem_sdiff.mp ha₂).2 (by
        simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
        exact Or.inr s.2)
    have hsY₁ : G.Adj y₁ s.1 :=
      ((G.mem_neighborFinset s.1 y₁).mp
        (Finset.mem_sdiff.mp hy₁).1).symm
    have hsY₂ : G.Adj y₂ s.1 :=
      ((G.mem_neighborFinset s.1 y₂).mp
        (Finset.mem_sdiff.mp hy₂).1).symm
    exact hfree (containsC4_of_two_common hsa hyne
      hsY₁ hy₁a₁ hsY₂ hy₂a₂)
  · dsimp [q₁, q₂]
    intro heq
    subst b₂
    have hsb : s.1 ≠ b₁ := by
      intro h
      subst b₁
      exact (Finset.mem_sdiff.mp hb₂).2 (by
        simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
        exact Or.inr s.2)
    have hsX₁ : G.Adj x₁ s.1 :=
      ((G.mem_neighborFinset s.1 x₁).mp
        (Finset.mem_sdiff.mp hx₁).1).symm
    have hsX₂ : G.Adj x₂ s.1 :=
      ((G.mem_neighborFinset s.1 x₂).mp
        (Finset.mem_sdiff.mp hx₂).1).symm
    exact hfree (containsC4_of_two_common hsb hxne
      hsX₁ hx₁b₁ hsX₂ hx₂b₂)

end

end Erdos85
