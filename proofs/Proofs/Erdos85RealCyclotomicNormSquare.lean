import Proofs.Erdos85AdjoinNormMinpoly
import Mathlib.RingTheory.Norm.Transitivity

/-!
# The index-two tower norm square

This file isolates the norm calculation used by the real cyclotomic bridge.
Once the full cyclotomic field has degree two over its maximal real subfield,
the norm of an element from the real subfield is the square of its real-field
norm.  Combining this with the translated-generator norm identity turns that
square into a minimal-polynomial evaluation squared.
-/

namespace Erdos85

noncomputable section

/-- Norm transitivity across an index-two field tower: an element imported
from the middle field has bottom norm equal to the square of its middle-field
norm. -/
theorem norm_algebraMap_eq_norm_sq_of_finrank_two
    {E K : Type*} [Field E] [Field K]
    [Algebra ℚ E] [Algebra ℚ K] [Algebra E K]
    [IsScalarTower ℚ E K] [FiniteDimensional ℚ E]
    [FiniteDimensional E K]
    (hfinrank : Module.finrank E K = 2) (x : E) :
    Algebra.norm ℚ (algebraMap E K x) =
      Algebra.norm ℚ x * Algebra.norm ℚ x := by
  rw [← Algebra.norm_norm (R := ℚ) (S := E) (A := K),
    Algebra.norm_algebraMap, hfinrank, pow_two, map_mul]

/-- **Real-cyclotomic tower consumer.**  Let `E = ℚ(μ)` and let `K/E`
be an index-two extension (eventually `K = ℚ(z)`, `μ=z+z⁻¹`).  Then the
full-field norm of `c-μ` is exactly `minpoly(μ)(c)²`.

The only cyclotomic-specific input deliberately left explicit is the
index-two statement `finrank E K = 2`; proving it from primitivity of `z`
is the separate real-subfield theorem. -/
theorem norm_rat_sub_eq_minpoly_eval_sq_of_finrank_two
    {L K : Type*} [Field L] [CharZero L] [Field K]
    [Algebra ℚ K]
    (μ : L) (c : ℚ) (hμ : IsIntegral ℚ μ)
    [Algebra (IntermediateField.adjoin ℚ {μ}) K]
    [IsScalarTower ℚ (IntermediateField.adjoin ℚ {μ}) K]
    [FiniteDimensional (IntermediateField.adjoin ℚ {μ}) K]
    (hfinrank : Module.finrank (IntermediateField.adjoin ℚ {μ}) K = 2) :
    Algebra.norm ℚ
        (algebraMap (IntermediateField.adjoin ℚ {μ}) K
          (⟨(c : L) - μ, rat_sub_mem_adjoin c μ⟩ :
            IntermediateField.adjoin ℚ {μ})) =
      (minpoly ℚ μ).eval c * (minpoly ℚ μ).eval c := by
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {μ}) :=
    IntermediateField.adjoin.finiteDimensional hμ
  rw [norm_algebraMap_eq_norm_sq_of_finrank_two hfinrank]
  rw [norm_rat_sub_generator_eq_minpoly_eval μ c hμ]

end

end Erdos85
