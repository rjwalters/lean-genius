import Proofs.Erdos85PairedBlockRigidity

/-!
# Canonical labeling of the one-high mate involution

The family CNFs number the eight branches so that mate pairs are
`0↔1, 2↔3, 4↔5, 6↔7`.  This file supplies the finite conjugacy theorem which
turns the graph's intrinsic fixed-point-free involution into that convention.
-/

namespace Erdos85

noncomputable section

/-- The standard four-pair involution used by the family encoders. -/
def oneHighStandardMate : Equiv.Perm (Fin 8) :=
  Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5 * Equiv.swap 6 7

theorem oneHighStandardMate_involutive :
    Function.Involutive oneHighStandardMate := by
  intro i
  native_decide +revert

theorem oneHighStandardMate_ne (i : Fin 8) : oneHighStandardMate i ≠ i := by
  native_decide +revert

/-- Every fixed-point-free involution of eight points is conjugate to the
standard four-pair involution.  This is a closed finite classification over
the `8!` permutations, checked by native evaluation. -/
theorem finEight_fixedPointFreeInvolution_conjugate_standard
    (p : Equiv.Perm (Fin 8))
    (hinv : ∀ i, p (p i) = i)
    (hfix : ∀ i, p i ≠ i) :
    ∃ σ : Equiv.Perm (Fin 8),
      ∀ i, σ (p i) = oneHighStandardMate (σ i) := by
  native_decide +revert

/-- Abstract eight-point form used for the graph neighborhood subtype. -/
theorem exists_equiv_finEight_intertwining_involution
    {P : Type*} [Fintype P] [DecidableEq P]
    (hcard : Fintype.card P = 8)
    (mate : P → P) (hinv : Function.Involutive mate)
    (hfix : ∀ x, mate x ≠ x) :
    ∃ e : P ≃ Fin 8, ∀ x, e (mate x) = oneHighStandardMate (e x) := by
  let e₀ : P ≃ Fin 8 := Fintype.equivFinOfCardEq hcard
  let p : Equiv.Perm (Fin 8) :=
    Equiv.ofBijective (fun i => e₀ (mate (e₀.symm i))) ⟨
      fun i j hij => by
        apply e₀.symm.injective
        apply hinv.injective
        simpa [e₀] using hij,
      fun j => ⟨e₀ (mate (e₀.symm j)), by
        simpa only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
          using congrArg e₀ (hinv (e₀.symm j))⟩⟩
  have hpInv : Function.Involutive p := by
    intro i
    change e₀ (mate (e₀.symm (e₀ (mate (e₀.symm i))))) = i
    simpa only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
      using congrArg e₀ (hinv (e₀.symm i))
  have hpFix : ∀ i, p i ≠ i := by
    intro i hi
    apply hfix (e₀.symm i)
    apply e₀.injective
    simpa [p] using hi
  obtain ⟨σ, hσ⟩ :=
    finEight_fixedPointFreeInvolution_conjugate_standard p hpInv hpFix
  refine ⟨e₀.trans σ, ?_⟩
  intro x
  simpa [p] using hσ (e₀ x)

/-- Graph-facing specialization: any mate involution on the eight neighbors
of the high root admits the exact branch numbering used by `family_gen.py`. -/
theorem exists_oneHigh_branchLabeling_intertwining_mate
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v : V}
    (hv : G.degree v = 8)
    (mate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hmateInv : Function.Involutive mate)
    (hmateAdj : ∀ s, G.Adj s.1 (mate s).1) :
    ∃ e : {z : V // z ∈ G.neighborSet v} ≃ Fin 8,
      ∀ s, e (mate s) = oneHighStandardMate (e s) := by
  let P := {z : V // z ∈ G.neighborSet v}
  have hPcard : Fintype.card P = 8 := by
    rw [Fintype.card_subtype]
    have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet v) =
        G.neighborFinset v := by ext z; simp
    rw [heq, G.card_neighborFinset_eq_degree, hv]
  apply exists_equiv_finEight_intertwining_involution hPcard mate hmateInv
  intro s hfix
  exact G.loopless.irrefl s.1 (congrArg Subtype.val hfix ▸ hmateAdj s)

end

end Erdos85
