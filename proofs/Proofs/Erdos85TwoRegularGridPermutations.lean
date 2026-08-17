import Proofs.Erdos85TwoBiregularDecomposition

/-! # Two-regular grid subsets split into two permutation graphs -/

namespace Erdos85

noncomputable section

/-- A finite grid predicate with exactly two true cells in each row and each
column is the disjoint union of two equivalence graphs. -/
theorem exists_two_disjoint_equiv_of_two_regular_grid
    {ι α V : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq α]
    (φ : V ≃ ι × α) (p : V → Prop) [DecidablePred p]
    (hrow : ∀ x : ι,
      ((Finset.univ : Finset α).filter fun y => p (φ.symm (x, y))).card = 2)
    (hcol : ∀ y : α,
      ((Finset.univ : Finset ι).filter fun x => p (φ.symm (x, y))).card = 2) :
    ∃ τ₀ τ₁ : ι ≃ α,
      (∀ x, p (φ.symm (x, τ₀ x))) ∧
      (∀ x, p (φ.symm (x, τ₁ x))) ∧
      ∀ x, τ₀ x ≠ τ₁ x := by
  let t : ι → Finset α := fun x =>
    Finset.univ.filter fun y => p (φ.symm (x, y))
  have ht : HallsTheoremOQ01OQ03.IsBiregular t 2 := by
    constructor
    · exact hrow
    · intro y
      simpa [t] using hcol y
  obtain ⟨τ₀, τ₁, hτ₀, hτ₁, hdisj⟩ :=
    exists_two_disjoint_equiv_of_two_biregular t ht
  refine ⟨τ₀, τ₁, ?_, ?_, hdisj⟩
  · intro x
    exact (Finset.mem_filter.mp (hτ₀ x)).2
  · intro x
    exact (Finset.mem_filter.mp (hτ₁ x)).2

end

end Erdos85
