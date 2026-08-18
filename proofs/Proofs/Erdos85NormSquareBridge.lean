import Proofs.Erdos85AdjoinSquareTranslate
import Mathlib.RingTheory.Norm.Defs

/-!
# The norm-square bridge

The rational-certificate layer of the orbit program.  The global orbit
theorem outputs an element `t ∈ ℚ(μ)` with `t·t = c - μ`.  Since the
field norm `Algebra.norm ℚ : ℚ(μ) →* ℚ` is multiplicative, a square in
`ℚ(μ)` has a square norm in `ℚ`.  Contrapositively: if the rational
norm of `c - μ` (as an element of the subfield `ℚ(μ)`) is *not* a
rational square — a fact checkable by a finite computation with the
minimal polynomial of `μ` — then no such square root `t` can exist.
-/

open IntermediateField

namespace Erdos85

noncomputable section

/-- Squares have square norms: the field norm is a monoid homomorphism,
so `x = t·t` forces `norm x = (norm t)·(norm t)`. -/
theorem norm_isSquare_of_isSquare
    {K : Type*} [Field K] [Algebra ℚ K] {x : K}
    (hx : IsSquare x) : IsSquare (Algebra.norm ℚ x) := by
  obtain ⟨t, rfl⟩ := hx
  exact ⟨Algebra.norm ℚ t, map_mul (Algebra.norm ℚ) t t⟩

variable {L : Type*} [Field L] [CharZero L]

/-- A rational translate `c - μ` of the generator lies in `ℚ(μ)`. -/
theorem rat_sub_mem_adjoin (c : ℚ) (μ : L) :
    (c : L) - μ ∈ IntermediateField.adjoin ℚ {μ} := by
  have hμ : μ ∈ IntermediateField.adjoin ℚ {μ} :=
    IntermediateField.subset_adjoin ℚ {μ} rfl
  have hc : (c : L) ∈ IntermediateField.adjoin ℚ {μ} :=
    SubfieldClass.ratCast_mem _ c
  exact sub_mem hc hμ

/-- **The contrapositive certificate.**  If the rational norm of
`c - μ` in the number field `ℚ(μ)` is not a rational square, then
`c - μ` has no square root inside `ℚ(μ)` — refuting the output shape
of the global orbit theorem by a finite rational computation. -/
theorem not_exists_sq_root_of_norm_not_isSquare
    (μ : L) (c : ℚ) (hint : IsIntegral ℚ μ)
    (hnorm : ¬ IsSquare (Algebra.norm ℚ
      (⟨(c : L) - μ, rat_sub_mem_adjoin c μ⟩ :
        IntermediateField.adjoin ℚ {μ}))) :
    ¬ ∃ t ∈ IntermediateField.adjoin ℚ {μ}, t * t = (c : L) - μ := by
  -- `ℚ(μ)` is finite-dimensional over `ℚ` since `μ` is integral, so the
  -- norm is the genuine (nontrivial) field norm; multiplicativity alone
  -- drives the proof.
  have _fd : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {μ}) :=
    IntermediateField.adjoin.finiteDimensional hint
  rintro ⟨t, htmem, htsq⟩
  apply hnorm
  apply norm_isSquare_of_isSquare
  exact ⟨⟨t, htmem⟩, Subtype.ext (by simpa using htsq.symm)⟩

end

end Erdos85
