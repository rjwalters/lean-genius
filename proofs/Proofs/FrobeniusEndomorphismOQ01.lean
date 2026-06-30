/-
  The Frobenius endomorphism in prime characteristic.

  Over a commutative ring `R` of prime characteristic `p`, the map

      frobenius : R → R,   x ↦ x ^ p

  is a RING HOMOMORPHISM.  The only non-obvious part is additivity — the
  "freshman's dream"

      (x + y) ^ p = x ^ p + y ^ p,

  which holds because every binomial coefficient `C(p, k)` for `0 < k < p` is
  divisible by `p`.

  Two characteristic facts pin down the Frobenius on the basic fields:

    * over `ZMod p` the Frobenius is the IDENTITY, `x ^ p = x` for all `x` —
      this is exactly **Fermat's little theorem** (every element is a fixed
      point);
    * over a finite field `K` with `|K| = q` the `q`-power map is the identity,
      `x ^ q = x`, and so are all its iterates `x ^ (q ^ n) = x`.

  Mathlib scatters these across `Algebra/CharP` and `FieldTheory/Finite`; this
  file packages the Frobenius ring-hom together with the prime-field
  fixed-point / finite-field identity characterizations, and checks the small
  cases `ZMod 5`, `ZMod 3` by `decide`.  Fully verified: 0 sorries, 0 axioms,
  no `native_decide`.
-/
import Mathlib

namespace FrobeniusEndomorphismOQ01

/-! ### The Frobenius ring homomorphism -/

section AbstractFrobenius

variable {R : Type*} [CommRing R] (p : ℕ) [ExpChar R p]

/-- The Frobenius map is `x ↦ x ^ p` (definitionally). -/
theorem frobenius_apply (x : R) : frobenius R p x = x ^ p := rfl

/-- **Freshman's dream.** In prime characteristic `p`, raising to the `p`-th
power is additive: `(x + y) ^ p = x ^ p + y ^ p`. This is the content that makes
the Frobenius a ring homomorphism. -/
theorem freshmans_dream (x y : R) : (x + y) ^ p = x ^ p + y ^ p :=
  add_pow_expChar x y p

omit [ExpChar R p] in
/-- The Frobenius respects multiplication (automatic from commutativity). -/
theorem frobenius_mul (x y : R) : (x * y) ^ p = x ^ p * y ^ p :=
  mul_pow x y p

end AbstractFrobenius

/-! ### Frobenius over `ZMod p`: Fermat's little theorem -/

section PrimeField

variable (p : ℕ) [Fact p.Prime]

/-- Over `ZMod p` the Frobenius endomorphism is the **identity** ring
homomorphism. -/
theorem frobenius_zmod_eq_id : frobenius (ZMod p) p = RingHom.id (ZMod p) :=
  ZMod.frobenius_zmod p

/-- **Fermat's little theorem**, as the statement that every element of `ZMod p`
is a fixed point of the Frobenius: `a ^ p = a`. -/
theorem fermat_little (a : ZMod p) : a ^ p = a :=
  ZMod.pow_card a

end PrimeField

/-! ### Frobenius over a finite field -/

section FiniteField

variable {K : Type*} [Field K] [Fintype K]

/-- Over a finite field `K` with `q = |K|`, the `q`-power map is the identity:
`a ^ q = a`. (The Frobenius iterated `n` times, where `q = pⁿ`.) -/
theorem finite_field_pow_card (a : K) : a ^ Fintype.card K = a :=
  FiniteField.pow_card a

/-- Every iterate of the `q`-power map is also the identity: `a ^ (qⁿ) = a`. -/
theorem finite_field_iterate (n : ℕ) (a : K) : a ^ Fintype.card K ^ n = a :=
  FiniteField.pow_card_pow n a

end FiniteField

/-! ### Concrete checks (decide, no native_decide) -/

/-- Fermat's little theorem for `p = 5`: every residue mod 5 is fixed by the
Frobenius `x ↦ x⁵`. -/
theorem frobenius_fixes_zmod_five : ∀ a : ZMod 5, a ^ 5 = a := by decide

/-- The freshman's dream verified in `ZMod 3`: `(x + y)³ = x³ + y³` for all
`x, y`. -/
theorem freshmans_dream_zmod_three : ∀ x y : ZMod 3, (x + y) ^ 3 = x ^ 3 + y ^ 3 := by decide

end FrobeniusEndomorphismOQ01
