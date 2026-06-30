/-
# The Chebyshev index map `n ↦ Cₙ` is a monoid homomorphism `(ℤ, ·) → (End, ∘)`
  (de-moivre-oq-01-oq-03-oq-01-oq-01)

## Open Question (OQ-01 of de-moivre-oq-01-oq-03-oq-01)
The parent `de-moivre-oq-01-oq-03-oq-01` proved the integer-index
De Moivre–Chebyshev identity over the "unit-circle locus" `z · w = 1`:
  `(C R n).eval (z + z⁻¹) = zⁿ + z⁻ⁿ`        for every `n : ℤ`.
Pointwise this says the index map `n ↦ Cₙ` *acts* like the power map `z ↦ zⁿ`.
OQ-01 asks for the **structural** upgrade: does this assemble into the full
semigroup / group law `C_{mn} = Cₘ ∘ Cₙ`, exhibiting `n ↦ Cₙ` as a genuine
**monoid homomorphism** `(ℤ, ·) → (End, ∘)`?

## Answer: YES.

The composition law itself is `Polynomial.Chebyshev.C_mul`:
  `C R (m * n) = (C R m).comp (C R n)`        (for all `m n : ℤ`),
with unit `C R 1 = X` (`Polynomial.Chebyshev.C_one`), the identity for `∘`.
These are exactly the two monoid-homomorphism axioms once the target is the
**endomorphism monoid** `Function.End R[X]` (the polynomials under composition,
with `mul = (· ∘ ·)` and `one = id`).  We package them:

  `chebyshevCEnd : ℤ →* Function.End R[X]`,  `chebyshevCEnd n = (C R n).comp ·`.

Then `map_mul` *is* the composition law `C_{mn} = Cₘ ∘ Cₙ` and `map_one` *is*
`C₁ = X`.  Because `(ℤ, ·)` is commutative the image is a commutative submonoid:
the Chebyshev polynomials commute under composition, `Cₘ ∘ Cₙ = Cₙ ∘ Cₘ`.

## The unit-circle locus made structural
The homomorphism is conjugate to the integer power map on `z · z⁻¹ = 1`.  Nesting
two Chebyshev evaluations is the same as a single evaluation at the product index:

  `chebyshevC_nest_eval_field_int` :
    `(C F m).eval ((C F n).eval (z + z⁻¹)) = z^{mn} + z^{-mn}`,

i.e. `Cₘ(Cₙ(z + z⁻¹)) = z^{mn} + z^{-mn} = C_{mn}(z + z⁻¹)`.  So under the
conjugating substitution `z ↦ z + z⁻¹`, the composition monoid `(End, ∘)` of
Chebyshev polynomials is carried to the power monoid `(ℤ, ·)` acting by `z ↦ zⁿ`
— the precise sense in which `n ↦ Cₙ` is "the power map restricted to the
unit-circle locus".

## Status
- `0` sorries, `0` axioms, no `native_decide`.
- New content: the bundled `MonoidHom` and the nesting/conjugacy theorem.
  The composition law `C_mul` and unit `C_one` are cited from Mathlib; the
  unit-circle identity is the parent's `chebyshevC_eval_field_int`.
-/

import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic
import Proofs.DeMoivreOQ01OQ03OQ01

namespace DeMoivreChebyshevMonoidHom

open Polynomial.Chebyshev
open DeMoivreChebyshevIntegerIndex

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: THE MONOID HOMOMORPHISM `(ℤ, ·) → (End R[X], ∘)`
═══════════════════════════════════════════════════════════════════════════════ -/

variable (R : Type*) [CommRing R]

/-- **The Chebyshev index map as a monoid homomorphism.**
    `n ↦ (Cₙ ∘ ·)` is a monoid homomorphism from the multiplicative monoid
    `(ℤ, ·)` to the endomorphism monoid `Function.End R[X]` (polynomials under
    composition).  Its two structure axioms are precisely the Chebyshev
    composition law `C R (m * n) = (C R m).comp (C R n)` (`map_mul`) and the unit
    `C R 1 = X` (`map_one`). -/
noncomputable def chebyshevCEnd : ℤ →* Function.End (Polynomial R) where
  toFun n := fun p => (C R n).comp p
  map_one' := by
    funext p
    show (C R 1).comp p = p
    rw [C_one, Polynomial.X_comp]
  map_mul' m n := by
    funext p
    show (C R (m * n)).comp p = (C R m).comp ((C R n).comp p)
    rw [C_mul, Polynomial.comp_assoc]

@[simp] theorem chebyshevCEnd_apply (n : ℤ) (p : Polynomial R) :
    chebyshevCEnd R n p = (C R n).comp p := rfl

/-- The homomorphism's `map_mul` *is* the Chebyshev composition law
    `C_{mn} = Cₘ ∘ Cₙ`, recovered as a function identity on `R[X]`. -/
theorem chebyshevCEnd_mul (m n : ℤ) :
    chebyshevCEnd R (m * n) = chebyshevCEnd R m * chebyshevCEnd R n :=
  (chebyshevCEnd R).map_mul m n

/-- The homomorphism's `map_one` *is* the unit law `C₁ = X`: the identity
    endomorphism of `R[X]`. -/
theorem chebyshevCEnd_one : chebyshevCEnd R 1 = 1 :=
  (chebyshevCEnd R).map_one

/-- **The Chebyshev polynomials commute under composition.**  Because `(ℤ, ·)` is
    commutative and `chebyshevCEnd` is a homomorphism, the image is a commutative
    submonoid: `Cₘ ∘ Cₙ = Cₙ ∘ Cₘ` for all integer indices. -/
theorem chebyshevC_comp_comm (m n : ℤ) :
    (C R m).comp (C R n) = (C R n).comp (C R m) := by
  rw [← C_mul, ← C_mul, mul_comm]

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: THE UNIT-CIRCLE LOCUS — CONJUGACY TO THE POWER MONOID
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Nesting = single evaluation at the product index (field form).**
    On the unit-circle locus `z · z⁻¹ = 1`, composing two Chebyshev evaluations
    equals one evaluation at the product index:
      `(C F m).eval ((C F n).eval (z + z⁻¹)) = z^{mn} + z^{-mn}`.
    This is the structural content of the monoid homomorphism transported through
    the conjugating substitution `z ↦ z + z⁻¹`: the composition monoid `(End, ∘)`
    is carried to the integer power map `z ↦ zⁿ`. -/
theorem chebyshevC_nest_eval_field_int {F : Type*} [Field F] (z : F) (hz : z ≠ 0)
    (m n : ℤ) :
    (C F m).eval ((C F n).eval (z + z⁻¹)) = z ^ (m * n) + (z⁻¹) ^ (m * n) := by
  rw [← Polynomial.eval_comp, ← C_mul, chebyshevC_eval_field_int z hz (m * n)]

/-- **Finite-field nesting law.** Over `ZMod p` (prime `p`), nesting Chebyshev
    evaluations on the unit circle collapses to the product index. -/
theorem chebyshevC_nest_eval_zmod_int (p : ℕ) [Fact p.Prime] (z : ZMod p)
    (hz : z ≠ 0) (m n : ℤ) :
    (C (ZMod p) m).eval ((C (ZMod p) n).eval (z + z⁻¹))
      = z ^ (m * n) + (z⁻¹) ^ (m * n) :=
  chebyshevC_nest_eval_field_int z hz m n

/-- **p-adic nesting law.** Over `ℚ_[p]`, nesting Chebyshev evaluations on the
    unit circle collapses to the product index. -/
theorem chebyshevC_nest_eval_padic_int (p : ℕ) [Fact p.Prime] (z : ℚ_[p])
    (hz : z ≠ 0) (m n : ℤ) :
    (C ℚ_[p] m).eval ((C ℚ_[p] n).eval (z + z⁻¹))
      = z ^ (m * n) + (z⁻¹) ^ (m * n) :=
  chebyshevC_nest_eval_field_int z hz m n

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: CONSISTENCY CHECKS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Over `ℝ`: nesting `C₂` after `C₃` at `z + z⁻¹` equals the index-`6` value
    `z⁶ + z⁻⁶`, the `m = 2, n = 3` instance. -/
example (z : ℝ) (hz : z ≠ 0) :
    (C ℝ 2).eval ((C ℝ 3).eval (z + z⁻¹)) = z ^ (6 : ℤ) + (z⁻¹) ^ (6 : ℤ) := by
  have h := chebyshevC_nest_eval_field_int z hz 2 3
  norm_num at h ⊢
  exact h

/-- The homomorphism sends the zero index to the constant endomorphism `p ↦ 2`
    (since `C R 0 = 2`), consistent with `0` not being a unit of `(ℤ, ·)`. -/
example : chebyshevCEnd ℝ 0 = fun _ => (2 : Polynomial ℝ) := by
  funext p
  show (C ℝ 0).comp p = 2
  rw [C_zero]
  simp

#check @chebyshevCEnd
#check @chebyshevCEnd_mul
#check @chebyshevC_nest_eval_field_int

end DeMoivreChebyshevMonoidHom
