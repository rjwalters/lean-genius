import Mathlib

/-!
# The Primitive Element Theorem: deg(minpoly K α) = [L:K]

## Open Question: cayley-hamilton-minpoly-oq-05-oq-02-oq-03

From `CayleyHamiltonMinpolyOQ05OQ02.lean`, which established:
- `simple_extension_dim`: finrank K K⟮x⟯ = deg(minpoly K x)
- Divisibility: deg(minpoly K x) | [L:K]
- Generator condition: finrank (K⟮x⟯) L = 1 iff deg(minpoly K x) = [L:K]

OQ-03 asks: **Can we formalize the primitive element theorem: every finite
separable extension has an element with deg(minpoly K x) = [L:K]?**

## Answer: YES

Mathlib's `Field.exists_primitive_element` provides: for a finite separable
extension K ⊂ L with K infinite, ∃ α ∈ L with K(α) = L (as intermediate fields).
Combined with `IntermediateField.adjoin.finrank`, this yields deg(minpoly K α) = [L:K].

The key identity chain:
  deg(minpoly K α)
    = finrank K K⟮α⟯       [by `IntermediateField.adjoin.finrank`]
    = finrank K ↥(⊤ : IntermediateField K L)   [since K⟮α⟯ = ⊤]
    = finrank K L           [by `IntermediateField.topEquiv`]

## Status: 0 sorries, 0 axioms
-/

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

namespace PrimitiveElementOQ03

open Polynomial IntermediateField Module FiniteDimensional

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

-- ============================================================
-- PART I: finrank of the Top Intermediate Field
-- ============================================================

/-- The top intermediate field K⟮L⟯ = L has the same K-rank as L itself.

    `IntermediateField.topEquiv` is the canonical K-algebra isomorphism
    between `↥(⊤ : IntermediateField K L)` and `L`, and `LinearEquiv.finrank_eq`
    converts this to a statement about finrank. -/
theorem finrank_top_eq (K L : Type*) [Field K] [Field L] [Algebra K L] :
    finrank K ↥(⊤ : IntermediateField K L) = finrank K L :=
  LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv

-- ============================================================
-- PART II: Primitive Element → Maximal Minpoly Degree
-- ============================================================

/-- **Bridge Lemma**: If α ∈ L generates L over K (i.e., K(α) = ⊤ as intermediate fields),
    then deg(minpoly K α) = finrank K L = [L:K].

    Proof chain:
    - `adjoin.finrank hα_int`: finrank K K⟮α⟯ = deg(minpoly K α)
    - Rewrite K⟮α⟯ to ⊤ using hgen
    - `finrank_top_eq`: finrank K ↥⊤ = finrank K L
    - Conclude: deg(minpoly K α) = finrank K L -/
theorem minpoly_deg_of_generator [FiniteDimensional K L] (α : L)
    (hgen : K⟮α⟯ = ⊤) :
    (minpoly K α).natDegree = finrank K L := by
  have hα_int : IsIntegral K α := IsIntegral.of_finite K α
  have h : finrank K ↥K⟮α⟯ = (minpoly K α).natDegree :=
    IntermediateField.adjoin.finrank hα_int
  rw [hgen, finrank_top_eq] at h
  omega

-- ============================================================
-- PART III: The Primitive Element Theorem (from Mathlib)
-- ============================================================

/-- **Primitive Element Theorem** (Artin–Galois): For a finite separable extension
    K ⊂ L over an infinite field K, there exists α ∈ L such that K(α) = L.

    This is `Field.exists_primitive_element` from Mathlib's
    `Mathlib.FieldTheory.PrimitiveElement`. Mathlib's proof uses:
    - For each pair of intermediate fields E ≠ L, there are finitely many
      c ∈ K such that K(β + c·γ) ≠ E for generators β, γ of L/K.
    - Since K is infinite, some c avoids all bad values.
    - By induction, an element generating all of L is found.

    Historical note: the theorem was known to Lagrange and Galois (for
    characteristic-0 finite extensions). The modern proof via separability
    is due to Artin (1944). -/
theorem primitive_element_exists [FiniteDimensional K L] [IsSeparable K L]
    [Infinite K] :
    ∃ α : L, K⟮α⟯ = ⊤ :=
  Field.exists_primitive_element K L

-- ============================================================
-- PART IV: Main Theorem (OQ-03 Answer)
-- ============================================================

/-- **Main Theorem**: In a finite separable extension K ⊂ L over an infinite field,
    there exists α ∈ L with deg(minpoly K α) = [L:K].

    This answers OQ-03: **YES**, the primitive element theorem is formalizable.
    The proof combines Mathlib's `Field.exists_primitive_element` with the
    fundamental identity deg(minpoly K α) = finrank K K⟮α⟯. -/
theorem primitive_element_minpoly [FiniteDimensional K L] [IsSeparable K L]
    [Infinite K] :
    ∃ α : L, (minpoly K α).natDegree = finrank K L := by
  obtain ⟨α, hα⟩ := primitive_element_exists (K := K) (L := L)
  exact ⟨α, minpoly_deg_of_generator α hα⟩

-- ============================================================
-- PART V: Degree Bounds and Characterization
-- ============================================================

/-- The degree of the minimal polynomial is always at most [L:K].

    This is a special case of the divisibility relation: deg | [L:K] implies deg ≤ [L:K].
    Proof: finrank K K⟮α⟯ ≤ finrank K L by monotonicity of finrank. -/
theorem minpoly_deg_le_finrank [FiniteDimensional K L] (α : L)
    (hα_int : IsIntegral K α) :
    (minpoly K α).natDegree ≤ finrank K L := by
  rw [← IntermediateField.adjoin.finrank hα_int]
  exact Submodule.finrank_le _

/-- Every element of L with finrank K K⟮α⟯ < finrank K L is not a generator.

    Contrapositive of `minpoly_deg_of_generator`. -/
theorem not_generator_of_deg_lt [FiniteDimensional K L] (α : L)
    (hlt : (minpoly K α).natDegree < finrank K L) :
    K⟮α⟯ ≠ ⊤ := by
  intro hgen
  have := minpoly_deg_of_generator α hgen
  omega

/-- A primitive element has strictly larger minpoly degree than any non-generator.

    This shows primitive elements are precisely the "degree-maximizing" elements. -/
theorem primitive_has_max_minpoly_deg [FiniteDimensional K L] [IsSeparable K L]
    [Infinite K] (β : L) (hβ_int : IsIntegral K β) (hβ_not_gen : K⟮β⟯ ≠ ⊤) :
    (minpoly K β).natDegree < finrank K L := by
  have hle := minpoly_deg_le_finrank β hβ_int
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    apply hβ_not_gen
    exact (generator_iff_minpoly_maxdeg β).mpr h.symm
where
  generator_iff_minpoly_maxdeg (α : L) :
      K⟮α⟯ = ⊤ ↔ (minpoly K α).natDegree = finrank K L := by
    constructor
    · exact minpoly_deg_of_generator α
    · intro hdeg
      -- From natDegree = finrank K L, deduce K⟮α⟯ = ⊤
      -- finrank K K⟮α⟯ = finrank K L (via adjoin.finrank)
      -- So K⟮α⟯.toSubmodule has same rank as L, giving K⟮α⟯ = ⊤
      have hα_int : IsIntegral K α := IsIntegral.of_finite K α
      have hfr : finrank K ↥K⟮α⟯ = finrank K L := by
        rw [IntermediateField.adjoin.finrank hα_int]; exact hdeg
      exact IntermediateField.eq_top_of_finrank_eq hfr

-- ============================================================
-- PART VI: The Iff Characterization
-- ============================================================

/-- **Biconditional**: α generates L over K if and only if deg(minpoly K α) = [L:K].

    Forward: `minpoly_deg_of_generator`.
    Backward: if deg = [L:K], then finrank K K⟮α⟯ = finrank K L, so K⟮α⟯ = ⊤.
    The backward direction uses `IntermediateField.eq_top_of_finrank_eq`. -/
theorem generator_iff_minpoly_maxdeg [FiniteDimensional K L] (α : L) :
    K⟮α⟯ = ⊤ ↔ (minpoly K α).natDegree = finrank K L := by
  constructor
  · exact minpoly_deg_of_generator α
  · intro hdeg
    have hα_int : IsIntegral K α := IsIntegral.of_finite K α
    have hfr : finrank K ↥K⟮α⟯ = finrank K L := by
      rw [IntermediateField.adjoin.finrank hα_int]; exact hdeg
    exact IntermediateField.eq_top_of_finrank_eq hfr

-- ============================================================
-- PART VII: Applications and Corollaries
-- ============================================================

/-- **Product formula for primitive element degree**: If α is a primitive element
    of the extension K ⊂ L (K(α) = L), then for any β ∈ L:
      [L:K] = deg(minpoly K α) = deg(minpoly K β) · [L:K(β)]

    This is the tower law: [L:K] = [K(β):K] · [L:K(β)] = deg(minpoly K β) · [L:K(β)]. -/
theorem tower_formula_via_primitive [FiniteDimensional K L] (α β : L)
    (hgen : K⟮α⟯ = ⊤) :
    (minpoly K α).natDegree = (minpoly K β).natDegree * finrank (↥K⟮β⟯) L := by
  have hα_int : IsIntegral K α := IsIntegral.of_finite K α
  have hβ_int : IsIntegral K β := IsIntegral.of_finite K β
  rw [minpoly_deg_of_generator α hgen]
  rw [← IntermediateField.adjoin.finrank hβ_int]
  exact finrank_mul_finrank K (↥K⟮β⟯) L

/-- **Corollary**: The degree of the minimal polynomial of a primitive element
    divides the degree of the minimal polynomial of any other element only in
    the degenerate way (since the primitive element has maximum degree). -/
theorem primitive_elem_deg_dvd_finrank [FiniteDimensional K L] [IsSeparable K L]
    [Infinite K] :
    ∃ α : L, ∀ β : L, IsIntegral K β →
      (minpoly K β).natDegree ∣ (minpoly K α).natDegree := by
  obtain ⟨α, hα_deg⟩ := primitive_element_minpoly (K := K) (L := L)
  refine ⟨α, fun β hβ_int => ?_⟩
  rw [hα_deg]
  -- deg(minpoly K β) | finrank K L, proved via tower law
  exact ⟨finrank (↥K⟮β⟯) L, by
    rw [← IntermediateField.adjoin.finrank hβ_int]
    exact (finrank_mul_finrank K (↥K⟮β⟯) L).symm⟩

-- ============================================================
-- Summary
-- ============================================================

/-
## What's Proved (10 theorems, 0 sorries, 0 axioms)

1. `finrank_top_eq` — finrank K ↥⊤ = finrank K L (via topEquiv)
2. `minpoly_deg_of_generator` — K(α)=⊤ ⟹ deg(minpoly K α) = [L:K]
3. `primitive_element_exists` — ∃ α, K(α) = ⊤ (Mathlib's primitive element thm)
4. `primitive_element_minpoly` — ∃ α, deg(minpoly K α) = [L:K]  (**main theorem**)
5. `minpoly_deg_le_finrank` — deg(minpoly K α) ≤ [L:K] always
6. `not_generator_of_deg_lt` — deg < [L:K] ⟹ not a generator
7. `primitive_has_max_minpoly_deg` — primitive elements have maximal deg
8. `generator_iff_minpoly_maxdeg` — K(α)=⊤ ↔ deg(minpoly K α) = [L:K]
9. `tower_formula_via_primitive` — [L:K] = deg(minpoly β) · [L:K(β)]
10. `primitive_elem_deg_dvd_finrank` — deg(minpoly β) | deg(primitive element)

## Answer to OQ-03

**YES**: The primitive element theorem is formalizable in Lean 4 using Mathlib.
- `Field.exists_primitive_element`: ∃ α, K(α) = L (Mathlib)
- `IntermediateField.adjoin.finrank`: deg(minpoly K α) = finrank K K(α) (Mathlib)
- `IntermediateField.topEquiv.toLinearEquiv`: finrank K ↥⊤ = finrank K L (Mathlib)
- Combining: deg(minpoly K α) = [L:K]

The result requires: [FiniteDimensional K L], [IsSeparable K L], [Infinite K].
For finite fields, a separate argument via Frobenius is needed.
-/

end PrimitiveElementOQ03
