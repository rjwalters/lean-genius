/-
# Chebyshev substitution as an algebra-endomorphism homomorphism
  `(ℤ, ·) → (R[X] →ₐ[R] R[X], ∘)`
  (de-moivre-oq-01-oq-03-oq-01-oq-01-oq-02)

## Open Question (OQ-02 of de-moivre-oq-01-oq-03-oq-01-oq-01)
The parent entry `de-moivre-oq-01-oq-03-oq-01-oq-01` (PR #31304) bundled the index
map `n ↦ Cₙ` as a monoid homomorphism `(ℤ, ·) → (Function.End R[X], ∘)` via the
**left-regular** action `p ↦ Cₙ ∘ p`. It asked:

  > "Can the bundled `MonoidHom` be upgraded to an algebra-endomorphism-valued
  >  homomorphism `ℤ →* (R[X] →ₐ[R] R[X])` via `aeval`, recording that each
  >  `Cₙ`-substitution is an `R`-algebra endomorphism?"

## Answer: YES — via the *substitution* action `p ↦ p(Cₙ) = p ∘ Cₙ`.

This is a genuine refinement, not a relabelling: the parent's left-regular action
`p ↦ Cₙ ∘ p` is **not** an algebra endomorphism (it fails multiplicativity in `p`,
e.g. for `Cₙ = X + 1`, `(p·q)+1 ≠ (p+1)(q+1)`). The correct algebra-endomorphism
upgrade is the **substitution** `X ↦ Cₙ`, i.e.

  `p ↦ p.comp Cₙ = aeval Cₙ p`,

which is an `R`-algebra endomorphism of `R[X]` for every `n` (it is `Polynomial.aeval`,
an `AlgHom` by construction). Substitution composes contravariantly,
`aeval Cₘ ∘ aeval Cₙ = aeval (Cₙ ∘ Cₘ) = aeval C_{nm}`, but because `(ℤ, ·)` is
commutative `C_{nm} = C_{mn}`, so this is again the Chebyshev composition law and we
get a genuine monoid homomorphism into the algebra-endomorphism monoid
`AlgHom.End` (algebra endomorphisms of `R[X]` under `∘`, with unit `AlgHom.id`):

  `chebAlgEnd : ℤ →* (R[X] →ₐ[R] R[X])`,   `chebAlgEnd n = aeval (C R n)`.

* `map_mul` is the composition law `C_{mn} = Cₘ ∘ Cₙ` at the level of substitutions
  (`chebAlgEnd_comp`).
* `map_one` is the unit `C₁ = X` (`aeval X = AlgHom.id`).
* The Chebyshev polynomial itself is recovered as the image of `X`:
  `chebAlgEnd n X = Cₙ` (`chebAlgEnd_X`).
* On the unit-circle locus the algebra endomorphism reparametrizes the polynomial
  argument by the De Moivre power map: `(chebAlgEnd n p).eval (z + z⁻¹) =
  p.eval (zⁿ + z⁻ⁿ)` (`eval_chebAlgEnd_unit`), tying the substitution action back to
  the parent chain's evaluation identity.

## Status
- All theorems proved (0 sorries, 0 axioms, no `native_decide`).
- Core ingredients: Mathlib's `Polynomial.Chebyshev.C_mul`, `Polynomial.comp_eq_aeval`,
  `Polynomial.aeval_X_left`, and `AlgHom.End`; the unit-circle theorem reuses the
  grandparent's `chebyshevC_eval_field_int`.
- Builds on the parent file `Proofs.DeMoivreOQ01OQ03OQ01OQ01`.
-/

import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic
import Proofs.DeMoivreOQ01OQ03OQ01OQ01

namespace DeMoivreChebyshevAlgEnd

open Polynomial.Chebyshev
open scoped Polynomial

variable {R : Type*} [CommRing R]

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: THE ALGEBRA-ENDOMORPHISM HOMOMORPHISM `(ℤ, ·) → (R[X] →ₐ[R] R[X], ∘)`
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The Chebyshev substitution as an algebra-endomorphism homomorphism.**
    `n ↦ aeval (Cₙ)` is a monoid homomorphism from the multiplicative monoid
    `(ℤ, ·)` into the monoid `AlgHom.End` of `R`-algebra endomorphisms of `R[X]`
    under composition. Each `chebAlgEnd n = aeval (C R n)` is the substitution
    `X ↦ Cₙ`, a genuine `R`-algebra endomorphism; its `map_mul` is the Chebyshev
    composition law `C_{mn} = Cₘ ∘ Cₙ`. -/
noncomputable def chebAlgEnd : ℤ →* (R[X] →ₐ[R] R[X]) where
  toFun n := Polynomial.aeval (C R n)
  map_one' := by
    rw [C_one]
    exact Polynomial.aeval_X_left
  map_mul' m n := by
    refine AlgHom.ext fun p => ?_
    rw [AlgHom.mul_apply]
    simp only [← Polynomial.comp_eq_aeval]
    rw [Polynomial.comp_assoc, ← C_mul, mul_comm]

/-- Unfolding: `chebAlgEnd n` is the substitution `p ↦ p ∘ Cₙ`. -/
@[simp] theorem chebAlgEnd_apply (n : ℤ) (p : R[X]) :
    chebAlgEnd n p = p.comp (C R n) :=
  Polynomial.comp_eq_aeval.symm

/-- The Chebyshev polynomial `Cₙ` is the image of the generator `X` under the
    substitution endomorphism: `chebAlgEnd n X = Cₙ`. -/
@[simp] theorem chebAlgEnd_X (n : ℤ) : chebAlgEnd (R := R) n Polynomial.X = C R n := by
  rw [chebAlgEnd_apply, Polynomial.X_comp]

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: STRUCTURE — THE COMPOSITION LAW AND ALGEBRA-ENDOMORPHISM PROPERTY
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The homomorphism's `map_mul`, written as composition in `AlgHom.End`: the
    Chebyshev composition law `C_{mn} = Cₘ ∘ Cₙ` lifted to substitution
    endomorphisms. -/
theorem chebAlgEnd_comp (m n : ℤ) :
    (chebAlgEnd (R := R) m).comp (chebAlgEnd n) = chebAlgEnd (m * n) := by
  show chebAlgEnd m * chebAlgEnd n = chebAlgEnd (m * n)
  exact (map_mul chebAlgEnd m n).symm

/-- The homomorphism's `map_one`: index `1` is the identity endomorphism
    (`C₁ = X`). -/
theorem chebAlgEnd_one : chebAlgEnd (R := R) 1 = 1 := map_one chebAlgEnd

/-- The substitution endomorphisms commute: `Cₘ ∘ Cₙ = Cₙ ∘ Cₘ`, the image being a
    commutative submonoid (since `(ℤ, ·)` is commutative). -/
theorem chebAlgEnd_comm (m n : ℤ) :
    (chebAlgEnd (R := R) m).comp (chebAlgEnd n)
      = (chebAlgEnd (R := R) n).comp (chebAlgEnd m) := by
  rw [chebAlgEnd_comp, chebAlgEnd_comp, mul_comm]

/-- **Each `chebAlgEnd n` is a genuine `R`-algebra endomorphism**: it is
    multiplicative, in contrast to the parent's left-regular action `p ↦ Cₙ ∘ p`
    (which is not). This is automatic from the `AlgHom` codomain and is the precise
    sense in which the OQ's "algebra-endomorphism-valued" upgrade holds. -/
theorem chebAlgEnd_map_mul (n : ℤ) (p q : R[X]) :
    chebAlgEnd n (p * q) = chebAlgEnd n p * chebAlgEnd n q :=
  map_mul (chebAlgEnd n) p q

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: THE UNIT-CIRCLE LOCUS — SUBSTITUTION REPARAMETRIZES BY THE POWER MAP
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Substitution on the unit-circle locus.** Over a field `F`, evaluating the
    image `chebAlgEnd n p` at a unit-circle point `z + z⁻¹` reparametrizes the
    polynomial argument by the De Moivre power map:
      `(chebAlgEnd n p).eval (z + z⁻¹) = p.eval (zⁿ + z⁻ⁿ)`.
    This ties the algebra-endomorphism action to the grandparent's evaluation
    identity `chebyshevC_eval_field_int`. -/
theorem eval_chebAlgEnd_unit {F : Type*} [Field F] (z : F) (hz : z ≠ 0) (n : ℤ)
    (p : F[X]) :
    (chebAlgEnd n p).eval (z + z⁻¹) = p.eval (z ^ n + (z⁻¹) ^ n) := by
  rw [chebAlgEnd_apply, Polynomial.eval_comp,
    DeMoivreChebyshevIntegerIndex.chebyshevC_eval_field_int z hz n]

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: CONSISTENCY CHECKS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The generator maps to `C₂ = X² − 2` under the index-`2` substitution. -/
example : chebAlgEnd (R := ℤ) 2 Polynomial.X = Polynomial.X ^ 2 - 2 := by
  rw [chebAlgEnd_X, C_two]

/-- Composition of substitutions: `C₂ ∘ C₃ = C₆` as algebra endomorphisms of `ℝ[X]`. -/
example : (chebAlgEnd (R := ℝ) 2).comp (chebAlgEnd 3) = chebAlgEnd 6 := by
  rw [chebAlgEnd_comp]; norm_num

/-- Index `1` is the identity algebra endomorphism. -/
example : chebAlgEnd (R := ℝ) 1 = 1 := chebAlgEnd_one

/-- Unit-circle reparametrization, concrete: substituting `C₃` then evaluating at
    `z + z⁻¹` feeds `z³ + z⁻³` into the argument polynomial. -/
example (z : ℝ) (hz : z ≠ 0) (p : ℝ[X]) :
    (chebAlgEnd 3 p).eval (z + z⁻¹) = p.eval (z ^ (3 : ℤ) + (z⁻¹) ^ (3 : ℤ)) :=
  eval_chebAlgEnd_unit z hz 3 p

/-
═══════════════════════════════════════════════════════════════════════════════
VERIFICATION
═══════════════════════════════════════════════════════════════════════════════ -/

#check @chebAlgEnd
#check @chebAlgEnd_comp
#check @chebAlgEnd_X
#check @eval_chebAlgEnd_unit

end DeMoivreChebyshevAlgEnd
