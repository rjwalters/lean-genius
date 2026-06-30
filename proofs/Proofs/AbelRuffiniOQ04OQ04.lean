import Mathlib
import Proofs.InverseGaloisF20

/-
# Specific Solvable Quintics via Galois Group Computation (OQ-04-OQ-04)

The Abel–Ruffini theorem says the *general* quintic is not solvable by radicals,
because its Galois group is `S₅`, which is not solvable. The complementary,
constructive question is: **exhibit specific quintics that ARE solvable, and
certify solvability by computing their Galois group.**

This file assembles a small menu of concrete solvable quintics over `ℚ`, each
with its Galois group shown to be solvable (and, for the headline example, its
exact order computed).

## The menu

| Quintic                | Reducible? | `Gal` order | Group structure        |
|------------------------|------------|-------------|------------------------|
| `X⁵ - 2`               | no         | `20`        | `F₂₀ = C₅ ⋊ C₄`        |
| `X⁵ - 1`               | yes        | `4`         | `(ℤ/5)ˣ ≅ C₄` (abelian)|
| `(X² - 2)(X³ - 2)`     | yes        | —           | product, solvable      |

## Relation to existing gallery work

`Proofs.InverseGaloisF20` proves `|Gal(X⁵-2/ℚ)| = 20` but only *remarks* (in its
header) that the group is solvable — it never states the fact. The headline
result here closes that gap: `x5_sub_2_solvable_quintic` certifies both
`IsSolvable` and `card = 20` in one statement, giving a *complete* Galois
computation of a specific solvable quintic.

The solvability facts themselves are direct applications of Mathlib's
`Polynomial.gal_X_pow_sub_C_isSolvable`, `gal_X_pow_sub_one_isSolvable`, and
`gal_mul_isSolvable`. The contribution of this entry is the concrete assembly:
naming the examples, pinning their degrees, and tying solvability to the
order computation. No axioms or sorries beyond Mathlib's foundational
`Classical.choice`.
-/

namespace AbelRuffiniOQ04OQ04

open Polynomial

-- ============================================================================
-- Headline example: X⁵ - 2, an irreducible solvable quintic with |Gal| = 20
-- ============================================================================

/-- The Galois group of `X⁵ - 2` over `ℚ` is solvable.

This is the solvability half of the Galois computation; it is a direct instance
of Mathlib's `gal_X_pow_sub_C_isSolvable` (radical extensions `X^n - C a` always
have solvable Galois group). It complements `InverseGaloisF20.x5_sub_2_gal_card`,
which computes the order. -/
theorem x5_sub_2_gal_solvable :
    IsSolvable ((X : ℚ[X]) ^ 5 - C 2).Gal :=
  gal_X_pow_sub_C_isSolvable 5 2

/-- **A specific solvable quintic, fully computed.**

`X⁵ - 2` is an irreducible quintic over `ℚ` whose Galois group is *solvable* and
has *exactly 20 elements* — the Frobenius group `F₂₀ = C₅ ⋊ C₄`. This is the
constructive counterpart to Abel–Ruffini: a quintic that genuinely is solvable
by radicals (its roots are `⁵√2 · ζ₅ᵏ`), certified by its Galois group.

Solvability is `gal_X_pow_sub_C_isSolvable`; the order is
`InverseGaloisF20.x5_sub_2_gal_card`. -/
theorem x5_sub_2_solvable_quintic :
    IsSolvable ((X : ℚ[X]) ^ 5 - C 2).Gal ∧
      Fintype.card ((X : ℚ[X]) ^ 5 - C 2).Gal = 20 :=
  ⟨x5_sub_2_gal_solvable, InverseGaloisF20.x5_sub_2_gal_card⟩

/-- `X⁵ - 2` is irreducible over `ℚ` (recorded from `InverseGaloisF20`), so the
above genuinely concerns a quintic that does not split into lower-degree pieces. -/
theorem x5_sub_2_irreducible :
    Irreducible ((X : ℚ[X]) ^ 5 - C 2) :=
  InverseGaloisF20.x_fifth_sub_2_irreducible

-- ============================================================================
-- Cyclotomic example: X⁵ - 1, a (reducible) abelian solvable quintic
-- ============================================================================

/-- The Galois group of `X⁵ - 1` over `ℚ` is solvable.

`X⁵ - 1 = (X - 1)·Φ₅`, and its splitting field is `ℚ(ζ₅)` with Galois group
`(ℤ/5)ˣ ≅ C₄`, which is cyclic (hence abelian, hence solvable). Direct instance
of `gal_X_pow_sub_one_isSolvable`. -/
theorem x5_sub_1_gal_solvable :
    IsSolvable ((X : ℚ[X]) ^ 5 - 1).Gal :=
  gal_X_pow_sub_one_isSolvable 5

-- ============================================================================
-- Reducible product example: (X² - 2)(X³ - 2), a solvable quintic from pieces
-- ============================================================================

/-- The degree-5 polynomial `(X² - 2)(X³ - 2)` really is a quintic. -/
theorem product_quintic_natDegree :
    (((X : ℚ[X]) ^ 2 - C 2) * (X ^ 3 - C 2)).natDegree = 5 := by
  have h2 : ((X : ℚ[X]) ^ 2 - C 2) ≠ 0 := X_pow_sub_C_ne_zero (by norm_num) 2
  have h3 : ((X : ℚ[X]) ^ 3 - C 2) ≠ 0 := X_pow_sub_C_ne_zero (by norm_num) 2
  rw [natDegree_mul h2 h3, natDegree_X_pow_sub_C, natDegree_X_pow_sub_C]

/-- The Galois group of the reducible quintic `(X² - 2)(X³ - 2)` over `ℚ` is
solvable.

Each factor is a radical extension `X^n - C 2` with solvable Galois group, and
solvability is preserved under products of polynomials (`gal_mul_isSolvable`).
This exhibits a solvable quintic that is neither irreducible nor a single
radical — its splitting field `ℚ(√2, ³√2, ζ₃)` has Galois group an extension of
`S₃` by `C₂`. -/
theorem product_quintic_gal_solvable :
    IsSolvable (((X : ℚ[X]) ^ 2 - C 2) * (X ^ 3 - C 2)).Gal :=
  gal_mul_isSolvable (gal_X_pow_sub_C_isSolvable 2 2) (gal_X_pow_sub_C_isSolvable 3 2)

-- ============================================================================
-- Summary: the menu as one statement
-- ============================================================================

/-- **Menu of specific solvable quintics over `ℚ`.**

Three concrete quintics — one irreducible radical (`X⁵-2`), one cyclotomic
(`X⁵-1`), one reducible product (`(X²-2)(X³-2)`) — each certified to have a
solvable Galois group. Constructive companion to Abel–Ruffini's `S₅`
non-solvability. -/
theorem solvable_quintics_menu :
    IsSolvable ((X : ℚ[X]) ^ 5 - C 2).Gal ∧
      IsSolvable ((X : ℚ[X]) ^ 5 - 1).Gal ∧
      IsSolvable (((X : ℚ[X]) ^ 2 - C 2) * (X ^ 3 - C 2)).Gal :=
  ⟨x5_sub_2_gal_solvable, x5_sub_1_gal_solvable, product_quintic_gal_solvable⟩

end AbelRuffiniOQ04OQ04
