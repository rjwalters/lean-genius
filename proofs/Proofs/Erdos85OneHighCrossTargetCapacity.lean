import Proofs.Erdos85OneHighTriangleTargetSeparation

/-!
# Capacity of cross-target selections

The pairwise target-separation obstruction scales to arbitrary finite source
sets: choosing one neighbor in a fixed far branch defines an injection.  This
is the counting interface needed for global exchanged-label cycles.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- A cross-target choice from one source branch into one far branch is
injective on any finite source set. -/
theorem card_le_secondLayerBranch_of_crossTargetChoice
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    {s u : {z : V // z ∈ G.neighborSet v}}
    (sources : Finset V) (target : V → V)
    (hsource : ∀ x ∈ sources, x ∈ secondLayerBranch G v s)
    (htarget : ∀ x ∈ sources, target x ∈ secondLayerBranch G v u)
    (hadj : ∀ x ∈ sources, G.Adj x (target x)) :
    sources.card ≤ (secondLayerBranch G v u).card := by
  apply Finset.card_le_card_of_injOn target
  · intro x hx
    exact htarget x hx
  · intro x hx y hy hxy
    by_contra hne
    exact (ne_crossTargets_of_distinct_sourceVertices
      G hfree (hsource x hx) (hsource y hy) hne
        (htarget x hx) (htarget y hy) (hadj x hx) (hadj y hy)) hxy

/-- In the order-49 one-high geometry every far branch has five vertices, so
at most five distinct source vertices can select targets in it. -/
theorem card_le_five_of_crossTargetChoice
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    {s u : {z : V // z ∈ G.neighborSet v}}
    (sources : Finset V) (target : V → V)
    (hsource : ∀ x ∈ sources, x ∈ secondLayerBranch G v s)
    (htarget : ∀ x ∈ sources, target x ∈ secondLayerBranch G v u)
    (hadj : ∀ x ∈ sources, G.Adj x (target x))
    (hcard : (secondLayerBranch G v u).card = 5) :
    sources.card ≤ 5 := by
  rw [← hcard]
  exact card_le_secondLayerBranch_of_crossTargetChoice
    G hfree sources target hsource htarget hadj

end

end Erdos85
