/-
  The cyclotomic field `ℚ(ζ_p)` has degree `p − 1`, and `Φ_p` is the minimal
  polynomial of a primitive `p`-th root of unity.

  This file answers the second open question of `eisenstein-criterion-oq-01-oq-03-oq-02`:

    > Use `cyclotomic_prime_irreducible_rat` to compute `[ℚ(ζ_p) : ℚ] = p − 1`
    > explicitly, identifying `Φ_p` as the minimal polynomial of a primitive
    > `p`-th root of unity.

  **Why this is the payoff of irreducibility.**  Irreducibility of `Φ_p` over `ℚ`
  is not an end in itself: its whole point is that it pins down the *degree* of the
  cyclotomic field.  For a primitive `p`-th root of unity `ζ`, the minimal
  polynomial `minpoly ℚ ζ` is, a priori, merely *some* monic divisor of `Φ_p`.
  Once `Φ_p` is known to be irreducible, that divisor can only be `Φ_p` itself, so

      minpoly ℚ ζ = Φ_p,     [ℚ(ζ) : ℚ] = deg Φ_p = φ(p) = p − 1.

  **What is reused.**  The single nontrivial input is the irreducibility of `Φ_p`
  over `ℚ`, which the parent entry `eisenstein-criterion-oq-01-oq-03-oq-02` re-derived
  *elementarily* from Eisenstein's criterion at `Φ_p(X + 1)`
  (`EisensteinCriterionOQ01OQ03OQ02.cyclotomic_prime_irreducible_rat`), rather than by
  invoking Mathlib's `Polynomial.cyclotomic.irreducible_rat`.  We feed it into Mathlib's
  `IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible` to identify the minimal
  polynomial, read off its degree via `natDegree_cyclotomic` and `Nat.totient_prime`,
  and convert to the field degree via `IntermediateField.adjoin.finrank`.  A concrete
  capstone instantiates this in `ℂ` at `ζ_p = exp(2πi/p)`.

  Fully verified: 0 sorries, 0 axioms, no `native_decide`.
-/
import Mathlib
import Proofs.EisensteinCriterionOQ01OQ03OQ02

open Polynomial
open scoped IntermediateField

namespace EisensteinCriterionOQ01OQ03OQ02OQ02

variable (p : ℕ) [hp : Fact p.Prime]
variable {L : Type*} [Field L] [CharZero L] {ζ : L}

/-- **`Φ_p` is the minimal polynomial of a primitive `p`-th root of unity over `ℚ`.**

For any primitive `p`-th root of unity `ζ` in a characteristic-zero field, the minimal
polynomial of `ζ` over `ℚ` is exactly the `p`-th cyclotomic polynomial.  The only input
beyond Mathlib's `minpoly_eq_cyclotomic_of_irreducible` is the parent entry's
*elementary* (Eisenstein-route) irreducibility of `Φ_p`. -/
theorem minpoly_eq_cyclotomic (hζ : IsPrimitiveRoot ζ p) :
    minpoly ℚ ζ = cyclotomic p ℚ := by
  haveI : NeZero ((p : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.2 hp.out.pos.ne'⟩
  exact (hζ.minpoly_eq_cyclotomic_of_irreducible
    (EisensteinCriterionOQ01OQ03OQ02.cyclotomic_prime_irreducible_rat p)).symm

/-- The minimal polynomial of a primitive `p`-th root of unity has degree `p − 1`. -/
theorem minpoly_natDegree (hζ : IsPrimitiveRoot ζ p) :
    (minpoly ℚ ζ).natDegree = p - 1 := by
  rw [minpoly_eq_cyclotomic p hζ, natDegree_cyclotomic, Nat.totient_prime hp.out]

/-- **`[ℚ(ζ_p) : ℚ] = p − 1`.**

The degree of `ℚ` adjoined a primitive `p`-th root of unity equals `p − 1`, obtained
from `[ℚ(ζ) : ℚ] = deg (minpoly ℚ ζ)` and the previous degree computation. -/
theorem finrank_adjoin (hζ : IsPrimitiveRoot ζ p) :
    Module.finrank ℚ ℚ⟮ζ⟯ = p - 1 := by
  rw [IntermediateField.adjoin.finrank ((hζ.isIntegral hp.out.pos).tower_top (A := ℚ)),
    minpoly_natDegree p hζ]

/-- **Concrete capstone in `ℂ`.**  There is a primitive complex `p`-th root of unity
`ζ_p` (namely `exp(2πi/p)`) for which `[ℚ(ζ_p) : ℚ] = p − 1`. -/
theorem exists_complex_primitiveRoot_finrank :
    ∃ ζ : ℂ, IsPrimitiveRoot ζ p ∧ Module.finrank ℚ ℚ⟮ζ⟯ = p - 1 :=
  ⟨_, Complex.isPrimitiveRoot_exp p hp.out.pos.ne',
    finrank_adjoin p (Complex.isPrimitiveRoot_exp p hp.out.pos.ne')⟩

end EisensteinCriterionOQ01OQ03OQ02OQ02
