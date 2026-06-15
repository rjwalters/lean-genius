import Mathlib
import Proofs.WilsonsTheoremOQ02ExtOQ01

/-!
# Gauss–Wilson for rings of integers `O_K` (ORIENT)

Open question (`wilsons-theorem-oq-02-ext-oq-02`):

> Does the Gauss–Wilson theorem extend to rings of integers in algebraic
> number fields: is there a characterization of when `∏_{u ∈ O_K^×} u = -1`
> analogous to the `ZMod` case?

## The two readings

**Literal reading (`∏` over `O_K^×` itself).** By Dirichlet's unit theorem the
group `O_K^×` is finite *only* when its rank `r₁ + r₂ - 1 = 0`, i.e. when
`K = ℚ` or `K` is imaginary quadratic. In those cases `O_K^× = μ_K`, the group
of roots of unity in `K`, which is **cyclic of even order** (because `-1 ∈ μ_K`
always). A finite cyclic group of even order has a unique involution, so by
Miller's theorem its element-product is that involution, namely `-1`. Hence the
literal product is `-1` *exactly when it is defined*, and the `ZMod` dichotomy
(`-1` vs `+1`) **degenerates**: there is no `+1` case. For every other `K` the
product is an infinite product and is undefined.

**Genuine analogue (`∏` over `(O_K ⧸ I)ˣ`).** The faithful analogue of
`ZMod n = ℤ ⧸ (n)` is the residue ring `O_K ⧸ I` for a nonzero ideal `I`. This
is a *finite commutative ring*, so its unit group is a finite abelian group and
**Miller's theorem applies verbatim**. This file records that reduction.

## Main content

`gaussWilson_finite_ring` instantiates the merged Miller dichotomy
(`WilsonsTheoremOQ02ExtOQ01.miller_prod`) at `G = Rˣ` for *any* finite
commutative ring `R`. Specialising `R := ZMod n` recovers the gallery's
`gaussWilson_abstract_ext`; specialising `R := O_K ⧸ I` answers the open
question:

> `∏_{u ∈ (O_K ⧸ I)ˣ} u = -1`  ⟺  `(O_K ⧸ I)ˣ` has a *unique* involution and
> that involution is `-1`.

By CRT (`O_K ⧸ I ≅ ∏ O_K ⧸ 𝔭ᵢ^{eᵢ}`) the number of involutions is
`2^(number of local factors with nontrivial 2-torsion)`, so `∏ = -1` forces
`(O_K ⧸ I)ˣ` to be **cyclic of even order** — the direct `O_K` analogue of the
classical `n ∈ {1, 2, 4, pᵏ, 2pᵏ}` "primitive root" condition.

### A new phenomenon absent over `ℤ`

Over `ℤ`, a unique involution is *always* `-1`. Over `O_K` this can fail at
primes above `2`: in `ℤ[i] ⧸ (2)` the unique involution is `i` (since
`-1 ≡ 1`), and the product is `i`, not `-1`. Thus the refinement "and that
involution is `-1`" is genuinely necessary; it is automatic only for `I`
coprime to `2`. (See `proofs/scripts/verify_gauss_wilson_OK.py` for exact
finite-arithmetic confirmation across `ℤ[i]`, `ℤ[ω]`, `ℤ[√-2]` and residue
fields `F_q`.)

## Status

ORIENT. `gaussWilson_finite_ring` is a clean specialization of the merged
`miller_prod` and carries no `sorry`. The `-1` characterization corollary is
stated for documentation; closing it in Lean requires the units-coercion
`Units.coeHom` bookkeeping and the local unit-group structure
`(O_K ⧸ 𝔭ᵉ)ˣ`, neither of which is needed for the reduction itself.

**Not registered in `Proofs.lean`** while the Docker/Aristotle build backends
are unavailable; build-pending.
-/

namespace WilsonsTheoremOQ02ExtOQ02

open Finset
open WilsonsTheoremOQ02ExtOQ01 (miller_prod prod_eq_unique_involution)

variable (R : Type*) [CommRing R] [Fintype R] [DecidableEq R]

/-- **Gauss–Wilson for the units of an arbitrary finite commutative ring.**
The product of all units of a finite commutative ring `R` is `1`, unless `Rˣ`
has a unique element of order `2`, in which case the product is that element.

This is `WilsonsTheoremOQ02ExtOQ01.miller_prod` specialised to the finite
abelian group `G := Rˣ`. Taking `R := ZMod n` recovers the gallery's
`gaussWilson_abstract_ext`; taking `R := 𝒪_K ⧸ I` (a finite commutative ring
for any nonzero ideal `I` of a ring of integers) answers the `O_K` extension
question. -/
theorem gaussWilson_finite_ring :
    (∏ u : Rˣ, u = 1) ∨
    (∃ t : Rˣ, t ≠ 1 ∧ t ^ 2 = 1 ∧ (∀ s : Rˣ, s ^ 2 = 1 → s = 1 ∨ s = t)
        ∧ ∏ u : Rˣ, u = t) :=
  miller_prod (G := Rˣ)

/-- **Characterization of the `-1` case** (the `O_K` analogue of Gauss–Wilson).
The product of all units, viewed inside `R`, is `-1` exactly when `Rˣ` has a
unique involution and that involution is `-1`.

Stated for documentation of the open-question answer; the proof reduces
`gaussWilson_finite_ring` along `Units.coeHom R` and is left build-pending. -/
theorem prod_units_coe_eq_neg_one_iff :
    (∏ u : Rˣ, (u : R)) = -1 ↔
      ((-1 : R) ≠ 1 ∧
        ∀ s : Rˣ, s ^ 2 = 1 → (s : R) = 1 ∨ (s : R) = -1) := by
  sorry

end WilsonsTheoremOQ02ExtOQ02
