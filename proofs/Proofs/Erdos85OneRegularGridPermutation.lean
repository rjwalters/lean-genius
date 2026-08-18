import Mathlib

/-! # One-regular grid subsets are permutation graphs -/

namespace Erdos85

noncomputable section

/-- A finite grid predicate with exactly one true cell in each row and each
column is the graph of an equivalence between the row and column types. -/
theorem exists_equiv_of_one_regular_grid
    {ι α V : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq α]
    (φ : V ≃ ι × α) (p : V → Prop) [DecidablePred p]
    (hrow : ∀ x : ι,
      ((Finset.univ : Finset α).filter fun y => p (φ.symm (x, y))).card = 1)
    (hcol : ∀ y : α,
      ((Finset.univ : Finset ι).filter fun x => p (φ.symm (x, y))).card = 1) :
    ∃ σ : ι ≃ α, ∀ x, p (φ.symm (x, σ x)) := by
  let t : ι → Finset α := fun x =>
    Finset.univ.filter fun y => p (φ.symm (x, y))
  let yOf (x : ι) : α :=
    Classical.choose (Finset.card_eq_one.mp (hrow x))
  have hyOf_mem (x : ι) : yOf x ∈ t x := by
    have hs := Classical.choose_spec (Finset.card_eq_one.mp (hrow x))
    change yOf x ∈ (Finset.univ.filter fun y => p (φ.symm (x, y)))
    rw [hs]
    simp [yOf]
  have hinj : Function.Injective yOf := by
    intro x₁ x₂ hxy
    let C : Finset ι := Finset.univ.filter fun x => p (φ.symm (x, yOf x₁))
    have hx₁C : x₁ ∈ C := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp (hyOf_mem x₁)).2⟩
    have hx₂C : x₂ ∈ C := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa [hxy] using (Finset.mem_filter.mp (hyOf_mem x₂)).2
    have hCcard : C.card = 1 := hcol (yOf x₁)
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hCcard
    rw [hx] at hx₁C hx₂C
    have hx₁ : x₁ = x := by simpa using hx₁C
    have hx₂ : x₂ = x := by simpa using hx₂C
    exact hx₁.trans hx₂.symm
  have hsurj : Function.Surjective yOf := by
    intro y
    let C : Finset ι := Finset.univ.filter fun x => p (φ.symm (x, y))
    have hCcard : C.card = 1 := hcol y
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hCcard
    have hxC : x ∈ C := by rw [hx]; simp
    have hyRow : y ∈ t x := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hxC).2⟩
    have hyOfRow : yOf x ∈ t x := hyOf_mem x
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp (hrow x)
    change y ∈ (Finset.univ.filter fun a => p (φ.symm (x, a))) at hyRow
    change yOf x ∈ (Finset.univ.filter fun a => p (φ.symm (x, a))) at hyOfRow
    rw [hz] at hyRow hyOfRow
    have hy : y = z := by simpa using hyRow
    have hyOf : yOf x = z := by simpa using hyOfRow
    exact ⟨x, hyOf.trans hy.symm⟩
  let σ : ι ≃ α := Equiv.ofBijective yOf ⟨hinj, hsurj⟩
  refine ⟨σ, ?_⟩
  intro x
  exact (Finset.mem_filter.mp (hyOf_mem x)).2

end

end Erdos85
