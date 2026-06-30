import Mathlib
import Proofs.InverseGaloisA5
import Proofs.DedekindFrobeniusBridge

/-!
# Instantiating the Dedekind–Frobenius bridge for the A₅ quintic

The parent file `InverseGaloisA5` realizes `A₅` as a Galois group over `ℚ` using the
quintic `q = X⁵ − 5X⁴ + 10X³ − 10X² + 25X − 5`, but its final assumption is the
`axiom`

```
axiom three_dvd_gal_card : 3 ∣ Fintype.card q.Gal     -- InverseGaloisA5.lean:309
```

"By Dedekind's theorem at `p = 7`, `q mod 7 = (X−5)(X−6)·(irreducible cubic)`, so `Gal`
contains a Frobenius element with cycle type `(1,1,3)` and hence `3 ∣ |Gal|`."

The genuine Mathlib gap — *the order of the arithmetic Frobenius at an unramified prime
equals the inertia degree* — was closed abstractly in
`Proofs.DedekindFrobeniusBridge.orderOf_arithFrobAt_eq_inertiaDegIn`
(`R`–`S`–`G` general, `0` axioms, `0` sorries).

This file **instantiates that abstract bridge in the concrete A₅ setting**:
`R = ℤ`, `S = 𝓞 q.SplittingField`, `G = q.Gal`. The payoff is `three_dvd_gal_card_of_bridge`:
once one exhibits an *unramified* prime `Q` of `𝓞 q.SplittingField` over a rational prime
whose inertia degree is divisible by `3`, the axiom `three_dvd_gal_card` follows — with the
arithmetic Frobenius `arithFrobAt ℤ q.Gal Q` as the explicit order-divisible-by-3 witness.

This reduces the vague "Dedekind's theorem is missing" assumption to the single, sharp,
*standard* number-theoretic fact

```
3 ∣ Ideal.inertiaDegIn (Q.under ℤ) (𝓞 q.SplittingField)
```

at an unramified `Q` over `7`. It does **not** by itself remove the axiom (that fact is
still assumed here), but it verifies that the proven bridge plugs into the A₅ tower — all
the `NumberField` / `IsGaloisGroup` / `IsDedekindDomain` instances line up — and pins down
exactly what remains. See the module docstring's "Residual gap" note below for the
Kummer–Dedekind + inertia-tower route that would discharge the remaining hypothesis.

## Residual gap (next step)

`3 ∣ inertiaDegIn (7) (𝓞 q.SplittingField)` is provable from:
* `Mathlib`'s `inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply`
  (`NumberField/Ideal/KummerDedekind.lean`): applied to a root `α` of `q` inside the
  splitting field, the prime of `𝓞 ℚ(α)` matching the irreducible cubic factor of
  `q mod 7` has inertia degree `3` (using `7 ∤ disc q = 32000²`, so `7 ∤` the conductor);
* `Ideal.inertiaDeg_algebra_tower` (residue-field `finrank` multiplicativity, no Galois
  needed on the non-normal middle field `ℚ(α)`): a prime `Q` of `𝓞 q.SplittingField`
  over that cubic prime has `3 ∣ inertiaDeg(Q | 7)`;
* `Ideal.inertiaDegIn_eq_inertiaDeg` (Galois): all primes of the *splitting field* over
  `7` share this inertia degree, so `3 ∣ inertiaDegIn (7) (𝓞 q.SplittingField)`.
-/

open Polynomial Ideal
open scoped NumberField

namespace InverseGaloisA5DedekindInstantiation

open InverseGaloisA5

/-- The splitting field of `q` is a number field (finite extension of `ℚ`, characteristic 0). -/
instance : NumberField q.SplittingField := ⟨⟩

/-- `q.SplittingField / ℚ` is a Galois extension: it is the splitting field of `q`, hence
normal (`InverseGaloisA5` registers the `Normal` instance) and — being in characteristic
zero — separable (`Algebra.IsSeparable`, also registered in the parent). `IsGalois` is the
conjunction of those two, so the anonymous constructor assembles it from the ambient
instances. This is what unlocks `IsGaloisGroup.of_isGalois` below. -/
instance : IsGalois ℚ q.SplittingField := ⟨⟩

/-- `q.Gal` is a Galois group for `q.SplittingField / ℚ`.

`Polynomial.Gal q` is *definitionally* `q.SplittingField ≃ₐ[ℚ] q.SplittingField`, so
Mathlib's `IsGaloisGroup.of_isGalois` (which is stated for the notation `Gal(L/K)`) applies
once we identify the two `MulSemiringAction`s — they agree on the nose
(`Polynomial.Gal.applyMulSemiringAction` is the `AlgEquiv` application). -/
instance : IsGaloisGroup q.Gal ℚ q.SplittingField :=
  inferInstanceAs (IsGaloisGroup (q.SplittingField ≃ₐ[ℚ] q.SplittingField) ℚ q.SplittingField)

/-- **Bridge instantiation for the A₅ quintic.**

Given an *unramified* prime `Q` of `𝓞 q.SplittingField` (`ramificationIdxIn = 1`) over a
nonzero rational prime whose inertia degree is divisible by `3`, the arithmetic Frobenius
`arithFrobAt ℤ q.Gal Q` is an element of `q.Gal` whose order is divisible by `3`; hence
`3 ∣ |q.Gal|`. This is the instantiated form of `three_dvd_gal_card`, with the abstract
Dedekind–Frobenius bridge supplying `orderOf (arithFrobAt …) = inertiaDegIn …`. -/
theorem three_dvd_gal_card_of_bridge
    (Q : Ideal (𝓞 q.SplittingField)) [Q.IsMaximal] [Finite (𝓞 q.SplittingField ⧸ Q)]
    [(Q.under ℤ).IsMaximal]
    [Algebra.IsSeparable (ℤ ⧸ Q.under ℤ) (𝓞 q.SplittingField ⧸ Q)]
    (hp : Q.under ℤ ≠ ⊥)
    (hunram : Ideal.ramificationIdxIn (Q.under ℤ) (𝓞 q.SplittingField) = 1)
    (h3 : 3 ∣ Ideal.inertiaDegIn (Q.under ℤ) (𝓞 q.SplittingField)) :
    3 ∣ Fintype.card q.Gal := by
  -- The bridge: the arithmetic Frobenius at `Q` has order equal to the inertia degree.
  have hbridge :
      orderOf (arithFrobAt ℤ q.Gal Q)
        = Ideal.inertiaDegIn (Q.under ℤ) (𝓞 q.SplittingField) :=
    DedekindFrobeniusBridge.orderOf_arithFrobAt_eq_inertiaDegIn
      (R := ℤ) (G := q.Gal) Q hp hunram
  -- Hence `3 ∣ orderOf (arithFrobAt …)`, and `orderOf` divides the group order.
  rw [← hbridge] at h3
  exact h3.trans orderOf_dvd_card

end InverseGaloisA5DedekindInstantiation
