/-
# Chebyshev semigroup law over 𝔽_p: C_{mn} = C_m ∘ C_n  (de-moivre-oq-01-oq-03-oq-02)

## Open question (OQ-02 of de-moivre-oq-01-oq-03)
The parent (`de-moivre-oq-01-oq-03`) established the Chebyshev–De Moivre recurrence over an
arbitrary commutative ring (finite fields, ℂ, ℚ_p). This follow-up packages that algebra as
the **semigroup / nesting law**

      C_{mn}(x) = C_m(C_n(x)),

specialized over a finite field `𝔽_p = ZMod p`, and states it as a **monoid homomorphism**
`(ℤ, ·) →* (End 𝔽_p, ∘)`. The resulting commuting family `C_a ∘ C_b = C_b ∘ C_a` is the
algebraic trapdoor behind Chebyshev / Lucas-sequence public-key exchange.

## What is Mathlib's, and what is new here
The *polynomial* composition identity is already in Mathlib:

      `Polynomial.Chebyshev.C_mul : C R (m * n) = (C R m).comp (C R n)`.

This file does **not** reprove it. Its content is the packaging the open question asks for:

* `chebyshevC_evalComp`      — the **evaluation-map** form `C_{mn}(x) = C_m(C_n(x))`, a one-line
  corollary of `C_mul` via `eval_comp`, over an arbitrary commutative ring.
* `chebyshevC_evalComp_comm` — the **commuting family** `C_m(C_n x) = C_n(C_m x)`.
* `chebyshevC_evalComp_pow`  — the **power-map conjugacy**: on the "unit circle" `z·w = 1`
  the semigroup law is the shadow of `(zⁿ)ᵐ = z^{mn}`, reusing the parent's identity
  `C_n(z+w) = zⁿ + wⁿ`. This is the genuine structural insight — via `z ↦ z + z⁻¹`, the
  Chebyshev map family `n ↦ C_n` is conjugate to the power monoid `n ↦ (· ^ n)`.
* `chebyshevEnd`, `chebyshevHom` — the bundled **monoid homomorphism**
  `(ℤ, ·) →* Function.End (ZMod p)`, `n ↦ (x ↦ C_n x)`, whose `map_mul` is the semigroup law.
* `chebyshevEnd_eval_pow` — the conjugacy specialized to the finite field `𝔽_p`.

## Status: 0 sorries, 0 axioms. Builds on `Proofs.DeMoivreOQ01OQ03` and Mathlib's
`Polynomial.Chebyshev` (the polynomial composition law `C_mul`).
-/
import Mathlib
import Proofs.DeMoivreOQ01OQ03

namespace DeMoivreChebyshevSemigroup

open Polynomial.Chebyshev

variable {R : Type*} [CommRing R]

/-- **Evaluation-map composition law.** For any commutative ring `R`,
`C_{mn}(x) = C_m(C_n(x))`. This is the evaluation form of Mathlib's polynomial identity
`Polynomial.Chebyshev.C_mul` (`C R (m * n) = (C R m).comp (C R n)`), obtained by `eval_comp`. -/
theorem chebyshevC_evalComp (m n : ℤ) (x : R) :
    (C R (m * n)).eval x = (C R m).eval ((C R n).eval x) := by
  rw [C_mul, Polynomial.eval_comp]

/-- **Commuting family.** `C_m(C_n(x)) = C_n(C_m(x))` — the commutativity that powers
Chebyshev / Lucas key exchange (`C_a ∘ C_b = C_b ∘ C_a`). -/
theorem chebyshevC_evalComp_comm (m n : ℤ) (x : R) :
    (C R m).eval ((C R n).eval x) = (C R n).eval ((C R m).eval x) := by
  rw [← chebyshevC_evalComp, ← chebyshevC_evalComp, mul_comm]

/-- **Power-map conjugacy.** On the "unit circle" `z · w = 1`, the nesting law is the shadow
of `(zⁿ)ᵐ = z^{mn}`: both `C_{mn}(z+w)` and `C_m(C_n(z+w))` equal `(zⁿ)ᵐ + (wⁿ)ᵐ`, because
`zⁿ · wⁿ = (z·w)ⁿ = 1` keeps the pair on the unit circle. Hence, via the parametrization
`z ↦ z + w` (with `w = z⁻¹`), the Chebyshev family `n ↦ C_n` is conjugate to the power monoid
`n ↦ (· ^ n)`. Reuses the parent identity
`DeMoivreChebyshevFiniteField.chebyshevC_eval_add`. -/
theorem chebyshevC_evalComp_pow (m n : ℕ) (z w : R) (hzw : z * w = 1) :
    (C R ((m : ℤ) * n)).eval (z + w) = (z ^ n) ^ m + (w ^ n) ^ m := by
  rw [show ((m : ℤ) * n) = ((m * n : ℕ) : ℤ) by push_cast; ring,
    DeMoivreChebyshevFiniteField.chebyshevC_eval_add z w hzw (m * n)]
  ring

/-! ## Packaging over `ZMod p`

The monoid-homomorphism structure and the commuting family need only that `ZMod p` is a
commutative ring, so they are stated for an arbitrary modulus `p` (for prime `p`, `ZMod p`
is the finite field `𝔽_p`, the cryptographically relevant case). The power-map conjugacy in
the final section genuinely uses the field structure of `𝔽_p`. -/

section AnyModulus

variable (p : ℕ)

/-- The Chebyshev evaluation endomorphism `x ↦ C_n(x)` on `ZMod p`, viewed as an element of
the composition monoid `Function.End (ZMod p)`. -/
noncomputable def chebyshevEnd (n : ℤ) : Function.End (ZMod p) := fun x => (C (ZMod p) n).eval x

/-- **Monoid homomorphism** `(ℤ, ·) →* (End (ZMod p), ∘)`, `n ↦ (x ↦ C_n x)`. Its `map_one`
is `C_1 = X = id`; its `map_mul` is the semigroup law `C_{mn} = C_m ∘ C_n` (the evaluation
form of Mathlib's `C_mul`). For prime `p` the codomain is `End 𝔽_p`, and the image is the
commutative submonoid behind Chebyshev / Lucas key exchange. -/
noncomputable def chebyshevHom : ℤ →* Function.End (ZMod p) where
  toFun := chebyshevEnd p
  map_one' := by
    funext x
    show (C (ZMod p) (1 : ℤ)).eval x = x
    rw [C_one, Polynomial.eval_X]
  map_mul' m n := by
    funext x
    exact chebyshevC_evalComp m n x

@[simp] theorem chebyshevHom_apply (n : ℤ) (x : ZMod p) :
    chebyshevHom p n x = (C (ZMod p) n).eval x := rfl

/-- **Commuting family over `ZMod p`.** `C_m ∘ C_n = C_n ∘ C_m` as endomorphisms (the
trapdoor identity behind Chebyshev key exchange). -/
theorem chebyshevEnd_comm (m n : ℤ) :
    chebyshevEnd p m * chebyshevEnd p n = chebyshevEnd p n * chebyshevEnd p m := by
  funext x
  exact chebyshevC_evalComp_comm m n x

end AnyModulus

section FiniteField

variable (p : ℕ) [Fact p.Prime]

/-- **Power-map conjugacy over `𝔽_p`.** For `z ≠ 0` in the finite field `𝔽_p = ZMod p`, the
nested Chebyshev endomorphism on the "unit-circle" point `z + z⁻¹` realizes the `(m·n)`-th
power map: it equals `(zⁿ)ᵐ + (z⁻ⁿ)ᵐ = z^{mn} + z^{-mn}`. This is the genuine finite-field
content — `mul_inv_cancel₀` uses the field structure of `𝔽_p` — exhibiting `n ↦ C_n` as the
shadow of the power monoid `n ↦ (· ^ n)` under `z ↦ z + z⁻¹`. -/
theorem chebyshevEnd_eval_pow (m n : ℕ) (z : ZMod p) (hz : z ≠ 0) :
    chebyshevEnd p ((m : ℤ) * n) (z + z⁻¹) = (z ^ n) ^ m + (z⁻¹ ^ n) ^ m :=
  chebyshevC_evalComp_pow m n z z⁻¹ (mul_inv_cancel₀ hz)

end FiniteField

end DeMoivreChebyshevSemigroup
