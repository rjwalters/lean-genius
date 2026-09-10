import Proofs.Erdos85ThreeBlockCandidateDomains

namespace Erdos85
open SimpleGraph

private def maskGraph (bits : BitVec 10) : SimpleGraph (Fin 5) where
  Adj i j := oneHighBranchBitAdj bits i j = true
  symm := ⟨by
    intro i j h
    simpa only [oneHighBranchBitAdj, oneHighBranchEdgeIndex, eq_comm, min_comm, max_comm] using h⟩
  loopless := ⟨by intro i; simp [oneHighBranchBitAdj]⟩

private instance (bits : BitVec 10) : DecidableRel (maskGraph bits).Adj :=
  inferInstanceAs (DecidableRel (fun i j => oneHighBranchBitAdj bits i j = true))

/-- Every common relabeling keeps an internal row in the fifteen-mask domain. -/
theorem threeBlockMask_relabel (m : ThreeBlockMask) (σ : Equiv.Perm (Fin 5)) :
    ∃ m' : ThreeBlockMask, ∀ i j,
      oneHighBranchBitAdj m'.val i j = oneHighBranchBitAdj m.val (σ.symm i) (σ.symm j) := by
  classical
  let R := SimpleGraph.comap σ.symm (maskGraph m.val)
  let bits := oneHighBranchGraphEdges R
  have hbits (i j) : oneHighBranchBitAdj bits i j =
      oneHighBranchBitAdj m.val (σ.symm i) (σ.symm j) := by
    rw [oneHighBranchBitAdj_graphEdges_kernel]
    change decide (oneHighBranchBitAdj m.val (σ.symm i) (σ.symm j) = true) = _
    simp
  have hdegree (i) : (Finset.univ.filter fun j => oneHighBranchBitAdj bits i j).card =
      (Finset.univ.filter fun j => oneHighBranchBitAdj m.val (σ.symm i) j).card := by
    apply Finset.card_bij (fun j _ => σ.symm j)
    · intro j hj
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, hbits] using hj
    · intro j hj k hk heq
      exact σ.symm.injective heq
    · intro j hj
      refine ⟨σ j,?_,σ.symm_apply_apply j⟩
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, hbits, Equiv.symm_apply_apply] using hj
  obtain ⟨hd,hm⟩ := (finFiveTwoEdgeMatchingMasks_mem_iff m.val).mp m.property
  have hmem : bits ∈ finFiveTwoEdgeMatchingMasks := by
    apply (finFiveTwoEdgeMatchingMasks_mem_iff bits).mpr
    refine ⟨fun i => (hdegree i).trans_le (hd _), ?_⟩
    refine Eq.trans ?_ hm
    apply Finset.card_bij (fun i _ => σ.symm i)
    · intro i hi
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, hdegree] using hi
    · intro i hi j hj heq
      exact σ.symm.injective heq
    · intro i hi
      refine ⟨σ i,?_,σ.symm_apply_apply i⟩
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, hdegree, Equiv.symm_apply_apply] using hi
  exact ⟨⟨bits,hmem⟩,hbits⟩

def threeBlockCanonicalMask : ThreeBlockMask := ⟨129, by decide⟩

theorem threeBlockCanonicalMask_adj (i j : Fin 5) :
    oneHighBranchBitAdj threeBlockCanonicalMask.val i j = oneHighCanonicalBranchAdj true i j := by
  decide +revert

/-- A common five-label permutation may fix the first internal row to mask129. -/
theorem threeBlockMask_to_canonical (m : ThreeBlockMask) :
    ∃ σ : Equiv.Perm (Fin 5), ∀ i j,
      oneHighBranchBitAdj m.val i j = oneHighBranchBitAdj threeBlockCanonicalMask.val (σ i) (σ j) := by
  obtain ⟨hd,hm⟩ := (finFiveTwoEdgeMatchingMasks_mem_iff m.val).mp m.property
  obtain ⟨σ,hσ⟩ := finFive_matchingBits_canonical_kernel m.val true hd (by simpa using hm)
  exact ⟨σ,fun i j => (hσ i j).trans (threeBlockCanonicalMask_adj _ _).symm⟩

end Erdos85
#print axioms Erdos85.threeBlockMask_relabel
#print axioms Erdos85.threeBlockMask_to_canonical
