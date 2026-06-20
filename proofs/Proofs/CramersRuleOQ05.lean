import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic

/-
# Conjugation Invariance of Determinant, Trace, and Characteristic Polynomial (cramers-rule-oq-05)

Cramer's rule expresses the solution of a linear system through determinants.  A
natural follow-up question is *which* matrix quantities are intrinsic to the
underlying linear map rather than to the chosen basis.  Concretely: if `U` is a
unit (invertible) matrix and `N` is any square matrix, the conjugate

    U N U⁻¹

represents the same endomorphism in a different basis.  The basis-independent
("similarity") invariants are exactly the quantities that survive this
conjugation.

This file packages the three fundamental similarity invariants over an arbitrary
commutative ring `R`:

  * `det (U N U⁻¹) = det N`        (`Matrix.det_units_conj`)
  * `trace (U N U⁻¹) = trace N`    (`Matrix.trace_units_conj`)
  * `charpoly (U N U⁻¹) = charpoly N`  (`Matrix.charpoly_units_conj`)

and bundles them into a single `similarity_invariants` statement.  As corollaries
we record that similar matrices share these invariants (in the textbook
`∃ U, N = U M U⁻¹` formulation) and that the determinant and trace, being read
off the characteristic polynomial, are themselves invariant — a structural
reason the three facts cohere.

Each result is a thin, basis-free wrapper around Mathlib's `*_units_conj`
lemmas; the contribution is the packaged statement and the similarity
corollaries, which Mathlib does not state directly.

Status: 0 axioms, 0 sorries
-/

namespace CramersRuleOQ05

open Matrix BigOperators

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type*} [CommRing R]

/-- Conjugation of a matrix `N` by a unit matrix `U`, i.e. the matrix
`U N U⁻¹` representing the same endomorphism in a `U`-transformed basis. -/
def conj (U : (Matrix n n R)ˣ) (N : Matrix n n R) : Matrix n n R :=
  U.val * N * U⁻¹.val

@[simp]
theorem conj_apply (U : (Matrix n n R)ˣ) (N : Matrix n n R) :
    conj U N = U.val * N * U⁻¹.val := rfl

-- ============================================================================
-- Part I: The three similarity invariants
-- ============================================================================

/-- **Determinant is a similarity invariant**: `det (U N U⁻¹) = det N`. -/
theorem det_conj (U : (Matrix n n R)ˣ) (N : Matrix n n R) :
    (conj U N).det = N.det :=
  Matrix.det_units_conj U N

/-- **Trace is a similarity invariant**: `trace (U N U⁻¹) = trace N`. -/
theorem trace_conj (U : (Matrix n n R)ˣ) (N : Matrix n n R) :
    (conj U N).trace = N.trace :=
  Matrix.trace_units_conj U N

/-- **Characteristic polynomial is a similarity invariant**:
`charpoly (U N U⁻¹) = charpoly N`. -/
theorem charpoly_conj (U : (Matrix n n R)ˣ) (N : Matrix n n R) :
    (conj U N).charpoly = N.charpoly :=
  Matrix.charpoly_units_conj U N

-- ============================================================================
-- Part II: The packaged statement
-- ============================================================================

/-- **Bundled similarity invariants.** Conjugating a matrix by a unit `U`
preserves its determinant, trace, and characteristic polynomial simultaneously.
These are the three classical basis-independent invariants of an endomorphism. -/
theorem similarity_invariants (U : (Matrix n n R)ˣ) (N : Matrix n n R) :
    (conj U N).det = N.det ∧
    (conj U N).trace = N.trace ∧
    (conj U N).charpoly = N.charpoly :=
  ⟨det_conj U N, trace_conj U N, charpoly_conj U N⟩

-- ============================================================================
-- Part III: Similarity formulation (`∃ U, N = U M U⁻¹`)
-- ============================================================================

/-- Two matrices are *similar* when one is obtained from the other by conjugation
by a unit matrix. -/
def IsSimilar (M N : Matrix n n R) : Prop :=
  ∃ U : (Matrix n n R)ˣ, N = conj U M

/-- Similarity is reflexive (conjugate by the identity unit). -/
theorem IsSimilar.refl (M : Matrix n n R) : IsSimilar M M :=
  ⟨1, by simp [conj]⟩

/-- **Similar matrices have equal determinant.** -/
theorem IsSimilar.det_eq {M N : Matrix n n R} (h : IsSimilar M N) :
    N.det = M.det := by
  obtain ⟨U, rfl⟩ := h
  exact det_conj U M

/-- **Similar matrices have equal trace.** -/
theorem IsSimilar.trace_eq {M N : Matrix n n R} (h : IsSimilar M N) :
    N.trace = M.trace := by
  obtain ⟨U, rfl⟩ := h
  exact trace_conj U M

/-- **Similar matrices have equal characteristic polynomial.** -/
theorem IsSimilar.charpoly_eq {M N : Matrix n n R} (h : IsSimilar M N) :
    N.charpoly = M.charpoly := by
  obtain ⟨U, rfl⟩ := h
  exact charpoly_conj U M

-- ============================================================================
-- Part IV: Summary
-- ============================================================================

/-
## Summary

| Invariant | Statement | Mathlib backing |
|-----------|-----------|-----------------|
| Determinant | `det (U N U⁻¹) = det N` | `Matrix.det_units_conj` |
| Trace | `trace (U N U⁻¹) = trace N` | `Matrix.trace_units_conj` |
| Char. poly | `charpoly (U N U⁻¹) = charpoly N` | `Matrix.charpoly_units_conj` |

The bundled `similarity_invariants` and the `IsSimilar.*_eq` corollaries give the
textbook statement "similar matrices share their determinant, trace, and
characteristic polynomial" directly.  Because both `det` and `trace` appear (up
to sign) as coefficients of the characteristic polynomial, the determinant and
trace invariances are in fact consequences of the characteristic-polynomial
invariance — the three facts are not independent but form a coherent package, as
the bundling makes explicit.
-/

end CramersRuleOQ05

#check @CramersRuleOQ05.det_conj
#check @CramersRuleOQ05.trace_conj
#check @CramersRuleOQ05.charpoly_conj
#check @CramersRuleOQ05.similarity_invariants
#check @CramersRuleOQ05.IsSimilar.charpoly_eq
