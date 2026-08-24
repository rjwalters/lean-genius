import Proofs.Erdos85ThreeSeparatorPositiveSpikeSixCycle

/-! # Neighborhood exhaustion in the positive-spike three-separator profile -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Inclusion-exclusion turns a full two-set load into neighborhood exhaustion. -/
theorem neighborFinset_subset_union_of_load_overlap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V) (K R : Finset V) (q t : ℕ)
    (hdeg : G.degree w = q)
    (hload : (G.neighborFinset w ∩ K).card +
      (G.neighborFinset w ∩ R).card = q + t)
    (hoverlap : (G.neighborFinset w ∩ (K ∩ R)).card = t) :
    G.neighborFinset w ⊆ K ∪ R := by
  let A := G.neighborFinset w ∩ K
  let B := G.neighborFinset w ∩ R
  have hinter : A ∩ B = G.neighborFinset w ∩ (K ∩ R) := by
    ext z
    simp [A, B, and_left_comm]
  have hunion : A ∪ B = G.neighborFinset w ∩ (K ∪ R) := by
    ext z
    simp [A, B, and_or_left]
  have hcard := Finset.card_union_add_card_inter A B
  rw [hinter, hoverlap, hload] at hcard
  have hUnionCard : (G.neighborFinset w ∩ (K ∪ R)).card = q := by
    rw [← hunion]
    omega
  have hInterEq : G.neighborFinset w ∩ (K ∪ R) = G.neighborFinset w := by
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.inter_subset_left
    · rw [hUnionCard, G.card_neighborFinset_eq_degree, hdeg]
  intro z hz
  have : z ∈ G.neighborFinset w ∩ (K ∪ R) := hInterEq.symm ▸ hz
  exact (Finset.mem_inter.mp this).2

/-- B7's overlap degree two and pole load exhaust every pole neighborhood by
`K ∪ R`, the containment labelled (B8) in the structural analysis. -/
theorem positiveSpike_threeSeparator_pole_neighborFinset_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℕ}
    (hreg : ∀ v, G.degree v = q)
    (W K R : Finset V) (c : V)
    (hWcard : W.card = 3) (hKRcard : (K ∩ R).card = 3)
    (hcK : c ∈ K) (hcR : c ∉ R)
    (hprofile : ∀ v,
      ((G.neighborFinset v ∩ W).card : ℤ) =
        (if v ∈ K then 1 else 0) + (if v ∈ R then 1 else 0) -
          (if v = c then 1 else 0))
    (hpoleLoad : ∀ w ∈ W,
      (G.neighborFinset w ∩ K).card +
        (G.neighborFinset w ∩ R).card = q + 2) :
    ∀ w ∈ W, G.neighborFinset w ⊆ K ∪ R := by
  have htwo := (positiveSpike_threeSeparator_overlap_is_two_regular
    G hreg W K R c hWcard hKRcard hcK hcR hprofile hpoleLoad).2
  intro w hw
  exact neighborFinset_subset_union_of_load_overlap G w K R q 2
    (hreg w) (hpoleLoad w hw) (htwo w hw)

#print axioms neighborFinset_subset_union_of_load_overlap
#print axioms positiveSpike_threeSeparator_pole_neighborFinset_subset

end

end Erdos85
