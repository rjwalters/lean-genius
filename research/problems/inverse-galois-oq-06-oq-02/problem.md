# Problem: mod-7 Irreducible Factorization of q (the Dedekind input)

**Slug**: inverse-galois-oq-06-oq-02
**Created**: 2026-06-27
**Status**: Active
**Source**: inverse-galois-oq-06 <!-- gallery-gap -->

## Problem Statement

The A₅-realizability entry (`InverseGaloisA5.lean`) is fully proved **except** for
one axiom:

```lean
axiom three_dvd_gal_card : 3 ∣ Fintype.card q.Gal
```

where `q = X⁵ - 5X⁴ + 10X³ - 10X² + 25X - 5`. The intended elimination route is
**Dedekind's theorem at p = 7**: `q mod 7` factors into irreducibles of degrees
`(1,1,3)`, so `Gal(q)` contains a 3-cycle, hence `3 ∣ |Gal(q)|`.

Dedekind's theorem itself is a Mathlib gap (sibling Frobenius track
`inverse-galois-a5-oq-01` / `inverse-galois-oq-06-oq-01`). This sub-problem
isolates and **fully verifies the algebraic *input*** to that theorem at p = 7,
which the sibling track had only partially established (factorization shape +
no-roots, but not irreducibility or squarefreeness).

### Goal (this slug)

A verified, 0-axiom statement that, mod 7, `q` factors as

  `(X - 5)(X - 6) · (X³ + 6X² + 4X + 1)`

into **distinct irreducibles** of degrees `(1, 1, 3)` with **squarefree product**
(so 7 is unramified). This is exactly the hypothesis Dedekind's theorem consumes.

## Scope / Honesty

This does **NOT** close `three_dvd_gal_card`. It supplies the verified algebraic
half of the mod-7 route. The remaining "(1,1,3) factor type ⟹ Frobenius 3-cycle
⟹ 3 ∣ |Gal|" implication is the sibling track and stays axiomatized.

## First Steps (done)

1. `cubicMod7` (from `InverseGaloisOQ06OQ01`) has no roots in 𝔽₇ — upgrade to
   irreducibility via `irreducible_of_degree_le_three_of_not_isRoot`.
2. Linear factors irreducible (`irreducible_X_sub_C`) and pairwise non-associated.
3. Pairwise coprime (`isCoprime_X_sub_C_of_isUnit_sub`, `dvd_iff_isRoot`) ⟹
   squarefree via `squarefree_mul_iff`.
