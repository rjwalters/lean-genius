import Proofs.Erdos85DisjointFiberInvolutionGluing

/-!
# Owner-adapted pairing of a broken-T fiber

This is the finite pairing normal form in `(73rnz_cjibba)`.  A broken-T
fiber is even and contains at most two special leaves.  With one leaf, every
free pairing necessarily launches it to a nonleaf.  With two leaves, pair
the leaf fiber and the residual nonleaf fiber separately.
-/

namespace Erdos85

noncomputable section

/-- **Owner-adapted broken-fiber pairing (`73rnz_cjibba`).** -/
theorem exists_ownerAdapted_mate_of_even_with_atMostTwo_leaves
    {V : Type*} [Fintype V] [DecidableEq V]
    (S leaves : Finset V) (hleaves : leaves ⊆ S)
    (heven : Even S.card) (hleTwo : leaves.card ≤ 2) :
    ∃ mate : V → V,
      (∀ v ∈ S, mate v ∈ S) ∧
      (∀ v ∈ S, mate (mate v) = v) ∧
      (∀ v ∈ S, mate v ≠ v) ∧
      (leaves.card = 1 →
        ∀ l ∈ leaves, mate l ∈ S \ leaves) ∧
      (leaves.card = 2 →
        ∀ l ∈ leaves, mate l ∈ leaves) := by
  have hcases : leaves.card = 0 ∨ leaves.card = 1 ∨ leaves.card = 2 := by
    omega
  rcases hcases with hzero | hone | htwo
  · obtain ⟨mate, hclosed, hinvol, hfree, _⟩ :=
      exists_mate_of_even_finset S heven
    refine ⟨mate, hclosed, hinvol, hfree, ?_, ?_⟩
    · intro h
      omega
    · intro h
      omega
  · obtain ⟨mate, hclosed, hinvol, hfree, _⟩ :=
      exists_mate_of_even_finset S heven
    refine ⟨mate, hclosed, hinvol, hfree, ?_, ?_⟩
    · intro _hcard l hl
      apply Finset.mem_sdiff.mpr
      refine ⟨hclosed l (hleaves hl), ?_⟩
      intro hmateLeaf
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hone
      have hlx : l = x := by simpa [hx] using hl
      have hmlx : mate l = x := by simpa [hx] using hmateLeaf
      exact hfree l (hleaves hl) (by simpa [hlx] using hmlx)
    · intro h
      omega
  · have hevenLeaves : Even leaves.card := ⟨1, by omega⟩
    let residual := S \ leaves
    have hcardLe : leaves.card ≤ S.card := Finset.card_le_card hleaves
    have hcardSplit : leaves.card + residual.card = S.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hleaves]
      omega
    obtain ⟨k, hk⟩ := heven
    have hevenResidual : Even residual.card := by
      refine ⟨k - 1, ?_⟩
      omega
    have hdisjoint : Disjoint leaves residual := by
      apply Finset.disjoint_left.mpr
      intro v hvL hvR
      exact (Finset.mem_sdiff.mp hvR).2 hvL
    obtain ⟨leafMate, hleafClosed, hleafInvol, hleafFree, _⟩ :=
      exists_mate_of_even_finset leaves hevenLeaves
    obtain ⟨mate, hOnLeaves, hclosedLeaves, hclosedResidual,
      hinvolUnion, hfreeUnion⟩ :=
      exists_gluedMate_of_involution_of_even_disjoint
        leaves residual hdisjoint leafMate
        hleafClosed hleafInvol hleafFree hevenResidual
    have hunion : leaves ∪ residual = S := by
      ext v
      simp only [residual, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (hv | hv)
        · exact hleaves hv
        · exact hv.1
      · intro hvS
        by_cases hvL : v ∈ leaves
        · exact Or.inl hvL
        · exact Or.inr ⟨hvS, hvL⟩
    refine ⟨mate, ?_, ?_, ?_, ?_, ?_⟩
    · intro v hvS
      rw [← hunion] at hvS ⊢
      rcases Finset.mem_union.mp hvS with hvL | hvR
      · exact Finset.mem_union.mpr (Or.inl (hclosedLeaves v hvL))
      · exact Finset.mem_union.mpr (Or.inr (hclosedResidual v hvR))
    · intro v hvS
      exact hinvolUnion v (by rwa [hunion])
    · intro v hvS
      exact hfreeUnion v (by rwa [hunion])
    · intro h
      omega
    · intro _hcard l hl
      exact hclosedLeaves l hl

end

end Erdos85

#print axioms Erdos85.exists_ownerAdapted_mate_of_even_with_atMostTwo_leaves
