import Proofs.Erdos85AdjoinSquareConjugation

/-!
# Translation of the adjoined square through a rational shift

For a rational constant `c` and `μ = c - θ²`, the subfields `ℚ(μ)` and
`ℚ(θ²)` coincide, so membership `θ ∈ ℚ(θ²)` transports to an explicit
square root of `c - μ` inside `ℚ(μ)`.  This is the final translation
step of the orbit theorem: the defect eigenvalue `μ = (d-1) - θ²`
attached to an adjacency eigenvalue `θ` from an asymmetric irreducible
factor satisfies `d - 1 - μ` square in `ℚ(μ)`.
-/

namespace Erdos85

noncomputable section

open IntermediateField

variable {L : Type*} [Field L] [CharZero L]

/-- Adjoining `c - θ²` and adjoining `θ²` give the same subfield. -/
theorem adjoin_rat_sub_sq_eq (c : ℚ) (θ : L) :
    IntermediateField.adjoin ℚ {(c : L) - θ ^ 2} =
      IntermediateField.adjoin ℚ {θ ^ 2} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have hsq : θ ^ 2 ∈ IntermediateField.adjoin ℚ {θ ^ 2} :=
      IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)
    have hc : (c : L) ∈ IntermediateField.adjoin ℚ {θ ^ 2} := by
      have := IntermediateField.algebraMap_mem
        (IntermediateField.adjoin ℚ {θ ^ 2}) c
      simpa using this
    exact sub_mem hc hsq
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have hgen : (c : L) - θ ^ 2 ∈
        IntermediateField.adjoin ℚ {(c : L) - θ ^ 2} :=
      IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)
    have hc : (c : L) ∈ IntermediateField.adjoin ℚ {(c : L) - θ ^ 2} := by
      have := IntermediateField.algebraMap_mem
        (IntermediateField.adjoin ℚ {(c : L) - θ ^ 2}) c
      simpa using this
    have : (c : L) - ((c : L) - θ ^ 2) ∈
        IntermediateField.adjoin ℚ {(c : L) - θ ^ 2} :=
      sub_mem hc hgen
    simpa using this

/-- **The square transport.**  If `θ ∈ ℚ(θ²)` and `μ = c - θ²`, then
`c - μ` has an explicit square root inside `ℚ(μ)`. -/
theorem exists_sq_root_mem_adjoin_of_mem_adjoin_sq
    (c : ℚ) (θ μ : L) (hμ : μ = (c : L) - θ ^ 2)
    (hθ : θ ∈ IntermediateField.adjoin ℚ {θ ^ 2}) :
    ∃ t ∈ IntermediateField.adjoin ℚ {μ}, t * t = (c : L) - μ := by
  refine ⟨θ, ?_, ?_⟩
  · rw [hμ, adjoin_rat_sub_sq_eq c θ]
    exact hθ
  · rw [hμ]
    ring

/-- Subtype form: `c - μ` is a square in the subfield `ℚ(μ)`. -/
theorem isSquare_sub_mem_adjoin_of_mem_adjoin_sq
    (c : ℚ) (θ μ : L) (hμ : μ = (c : L) - θ ^ 2)
    (hθ : θ ∈ IntermediateField.adjoin ℚ {θ ^ 2})
    (hmem : (c : L) - μ ∈ IntermediateField.adjoin ℚ {μ}) :
    IsSquare (⟨(c : L) - μ, hmem⟩ :
      IntermediateField.adjoin ℚ {μ}) := by
  obtain ⟨t, htmem, htsq⟩ :=
    exists_sq_root_mem_adjoin_of_mem_adjoin_sq c θ μ hμ hθ
  exact ⟨⟨t, htmem⟩, Subtype.ext (by simpa using htsq.symm)⟩

/-- **End-to-end form.**  A root `θ` of a monic irreducible rational
polynomial moved by the signed reflection satisfies: `c - μ` is a
square in `ℚ(μ)` for `μ = c - θ²`. -/
theorem exists_sq_root_of_asymmetric_factor
    (c : ℚ) (f : Polynomial ℚ) (hf : Irreducible f)
    (hmonic : f.Monic)
    (hne : Polynomial.signedReflection f ≠ f)
    (θ : L) (hroot : Polynomial.aeval θ f = 0)
    (μ : L) (hμ : μ = (c : L) - θ ^ 2) :
    ∃ t ∈ IntermediateField.adjoin ℚ {μ}, t * t = (c : L) - μ :=
  exists_sq_root_mem_adjoin_of_mem_adjoin_sq c θ μ hμ
    (mem_adjoin_sq_of_aeval_eq_zero_of_signedReflection_ne
      f hf hmonic hne θ hroot)

end

end Erdos85
