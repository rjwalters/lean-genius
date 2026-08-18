import Proofs.Erdos85RestrictedOwnerBipartiteShadow

/-! # Matching normal form for two disjoint bipartite two-factors

Two disjoint degree-two relations on the same finite bipartite shores are
simultaneously the unions of two perfect matchings.  Moreover, every matching
edge in one factor avoids both displayed matching edges in the other factor.
This is the permutation-coordinate interface used by the all-triangle
`mu = 3` terminal.
-/

namespace Erdos85

noncomputable section

/-- Simultaneous four-matching normal form for two disjoint bipartite
two-factors.  The last line records all four pointwise cross-factor
inequalities. -/
theorem disjoint_twoRegular_relations_exists_fourMatching_normalForm
    {S T : Type*} [Fintype S] [Fintype T]
    [DecidableEq S] [DecidableEq T]
    (H K : S → T → Prop) [DecidableRel H] [DecidableRel K]
    (hHS : ∀ s, (Finset.univ.filter (H s)).card = 2)
    (hHT : ∀ t, (Finset.univ.filter (fun s => H s t)).card = 2)
    (hKS : ∀ s, (Finset.univ.filter (K s)).card = 2)
    (hKT : ∀ t, (Finset.univ.filter (fun s => K s t)).card = 2)
    (hdisj : ∀ s t, H s t → ¬ K s t) :
    ∃ fH gH fK gK : S ≃ T,
      (∀ s t, H s t ↔ t = fH s ∨ t = gH s) ∧
      (∀ s t, K s t ↔ t = fK s ∨ t = gK s) ∧
      (∀ s, fK s ≠ fH s ∧ fK s ≠ gH s ∧
        gK s ≠ fH s ∧ gK s ≠ gH s) := by
  obtain ⟨fH, pH⟩ :=
    twoRegularBipartite_exists_afterMatching H hHS hHT
  obtain ⟨fK, pK⟩ :=
    twoRegularBipartite_exists_afterMatching K hKS hKT
  let gH : S ≃ T := pH.residualEquiv
  let gK : S ≃ T := pK.residualEquiv
  refine ⟨fH, gH, fK, gK, ?_, ?_, ?_⟩
  · intro s t
    simpa [gH] using pH.rel_iff_matching_or_residual s t
  · intro s t
    simpa [gK] using pK.rel_iff_matching_or_residual s t
  · intro s
    have hHf : H s (fH s) := pH.matching_mem s
    have hHg : H s (gH s) := by
      simpa [gH] using (pH.residualEquiv_mem s).1
    have hKf : K s (fK s) := pK.matching_mem s
    have hKg : K s (gK s) := by
      simpa [gK] using (pK.residualEquiv_mem s).1
    constructor
    · intro heq
      exact hdisj s (fH s) hHf (heq ▸ hKf)
    constructor
    · intro heq
      exact hdisj s (gH s) hHg (heq ▸ hKf)
    constructor
    · intro heq
      exact hdisj s (fH s) hHf (heq ▸ hKg)
    · intro heq
      exact hdisj s (gH s) hHg (heq ▸ hKg)

/-- Normalize the first matching of `H` to the identity on the left shore.
The other three matching permutations then avoid the two `H` coordinates
pointwise. -/
theorem disjoint_twoRegular_relations_exists_leftPermutation_normalForm
    {S T : Type*} [Fintype S] [Fintype T]
    [DecidableEq S] [DecidableEq T]
    (H K : S → T → Prop) [DecidableRel H] [DecidableRel K]
    (hHS : ∀ s, (Finset.univ.filter (H s)).card = 2)
    (hHT : ∀ t, (Finset.univ.filter (fun s => H s t)).card = 2)
    (hKS : ∀ s, (Finset.univ.filter (K s)).card = 2)
    (hKT : ∀ t, (Finset.univ.filter (fun s => K s t)).card = 2)
    (hdisj : ∀ s t, H s t → ¬ K s t) :
    ∃ f : S ≃ T, ∃ σ α β : S ≃ S,
      (∀ s t, H s t ↔ f.symm t = s ∨ f.symm t = σ s) ∧
      (∀ s t, K s t ↔ f.symm t = α s ∨ f.symm t = β s) ∧
      (∀ s, α s ≠ s ∧ α s ≠ σ s ∧
        β s ≠ s ∧ β s ≠ σ s) := by
  obtain ⟨fH, gH, fK, gK, hH, hK, hcross⟩ :=
    disjoint_twoRegular_relations_exists_fourMatching_normalForm
      H K hHS hHT hKS hKT hdisj
  let σ : S ≃ S := gH.trans fH.symm
  let α : S ≃ S := fK.trans fH.symm
  let β : S ≃ S := gK.trans fH.symm
  refine ⟨fH, σ, α, β, ?_, ?_, ?_⟩
  · intro s t
    rw [hH]
    simp only [σ, Equiv.trans_apply]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl (fH.symm_apply_apply s)
      · exact Or.inr rfl
    · rintro (ht | ht)
      · left
        exact fH.symm.injective (ht.trans (fH.symm_apply_apply s).symm)
      · right
        exact fH.symm.injective ht
  · intro s t
    rw [hK]
    simp only [α, β, Equiv.trans_apply]
    constructor
    · rintro (rfl | rfl) <;> simp
    · rintro (ht | ht)
      · left; exact fH.symm.injective ht
      · right; exact fH.symm.injective ht
  · intro s
    rcases hcross s with ⟨hfi, hfg, hgi, hgg⟩
    simp only [σ, α, β, Equiv.trans_apply]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact fun h => hfi (fH.symm.injective (h.trans (fH.symm_apply_apply s).symm))
    · exact fun h => hfg (fH.symm.injective h)
    · exact fun h => hgi (fH.symm.injective (h.trans (fH.symm_apply_apply s).symm))
    · exact fun h => hgg (fH.symm.injective h)

end

end Erdos85
