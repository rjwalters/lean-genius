import Proofs.Erdos85ThreeHighRRelabeling

namespace Erdos85
attribute [local irreducible] threeHighCrossDomain

/-- Choose the ordered representative of a single R-column swap orbit.
Every other column remains unchanged, allowing disjoint swaps to be composed. -/
theorem threeHighRSwap_ordered_witness
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (a b : Fin 8) (score : (Fin 15 → Bool) → Nat)
    (hnear : ∀ j, (Equiv.swap a b j).val < 6 ↔ j.val < 6)
    (hR : ∀ i j, R (Equiv.swap a b i) (Equiv.swap a b j) = R i j)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (hExt : encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true)
    (hJoint : ThreeHighJointWitness (threeHighEmptyAdj U R cross)) :
    ∃ cross' : ThreeHighCross, cross' ∈ threeHighCrossDomain U R ∧
      encodedExternalBlockCap (threeHighEmptyAdj U R cross') threeHighCanonicalRow = true ∧
      ThreeHighJointWitness (threeHighEmptyAdj U R cross') ∧
      score (fun i => cross' i a) ≤ score (fun i => cross' i b) ∧
      (∀ i j, j ≠ a → j ≠ b → cross' i j = cross i j) := by
  by_cases h : score (fun i => cross i a) ≤ score (fun i => cross i b)
  · exact ⟨cross,hc,hExt,hJoint,h,fun _ _ _ _ => rfl⟩
  · have ht := threeHighRAutomorphism_joint_transport U R (Equiv.swap a b) hnear hR cross hc hExt hJoint
    refine ⟨(fun i j => cross i (Equiv.swap a b j)),ht.1,ht.2.1,ht.2.2,?_,?_⟩
    · simpa only [Equiv.swap_apply_left,Equiv.swap_apply_right] using Nat.le_of_lt (Nat.lt_of_not_ge h)
    · intro i j hja hjb
      simp only [Equiv.swap_apply_of_ne_of_ne hja hjb]

/-- Simultaneously order any list of disjoint R swap automorphisms. -/
theorem threeHighRDisjointSwaps_ordered_witness
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (pairs : List (Fin 8 × Fin 8)) (score : (Fin 15 → Bool) → Nat)
    (hdis : pairs.Pairwise (fun p q => p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2))
    (hnear : ∀ p ∈ pairs, ∀ j, (Equiv.swap p.1 p.2 j).val < 6 ↔ j.val < 6)
    (hR : ∀ p ∈ pairs, ∀ i j, R (Equiv.swap p.1 p.2 i) (Equiv.swap p.1 p.2 j) = R i j)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (hExt : encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true)
    (hJoint : ThreeHighJointWitness (threeHighEmptyAdj U R cross)) :
    ∃ cross' : ThreeHighCross, cross' ∈ threeHighCrossDomain U R ∧
      encodedExternalBlockCap (threeHighEmptyAdj U R cross') threeHighCanonicalRow = true ∧
      ThreeHighJointWitness (threeHighEmptyAdj U R cross') ∧
      (∀ p ∈ pairs, score (fun i => cross' i p.1) ≤ score (fun i => cross' i p.2)) ∧
      (∀ i j, (∀ p ∈ pairs, j ≠ p.1 ∧ j ≠ p.2) → cross' i j = cross i j) := by
  induction pairs generalizing cross with
  | nil => exact ⟨cross,hc,hExt,hJoint,by simp,fun _ _ _ => rfl⟩
  | cons p ps ih =>
    obtain ⟨hd,ht⟩ := List.pairwise_cons.mp hdis
    obtain ⟨c1,hc1,he1,hj1,ho1,hu1⟩ := threeHighRSwap_ordered_witness U R p.1 p.2 score
      (hnear p (List.mem_cons_self)) (hR p (List.mem_cons_self)) cross hc hExt hJoint
    obtain ⟨c2,hc2,he2,hj2,ho2,hu2⟩ := ih ht
      (fun q hq => hnear q (List.mem_cons_of_mem p hq))
      (fun q hq => hR q (List.mem_cons_of_mem p hq)) c1 hc1 he1 hj1
    refine ⟨c2,hc2,he2,hj2,?_,?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with hq | hq
      · subst q
        have ha : (fun i => c2 i p.1) = (fun i => c1 i p.1) := by
          funext i
          exact hu2 i p.1 (fun q hq => ⟨(hd q hq).1,(hd q hq).2.1⟩)
        have hb : (fun i => c2 i p.2) = (fun i => c1 i p.2) := by
          funext i
          exact hu2 i p.2 (fun q hq => ⟨(hd q hq).2.2.1,(hd q hq).2.2.2⟩)
        simpa only [ha,hb] using ho1
      · exact ho2 q hq
    · intro i j hj
      rw [hu2 i j (fun q hq => hj q (List.mem_cons_of_mem p hq))]
      exact hu1 i j (hj p List.mem_cons_self).1 (hj p List.mem_cons_self).2

end Erdos85
#print axioms Erdos85.threeHighRSwap_ordered_witness
#print axioms Erdos85.threeHighRDisjointSwaps_ordered_witness
