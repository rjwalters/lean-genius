# Problem: Iterated CRT for Multiple Coprime Moduli over Commutative Rings

**Slug**: bezout-identity-oq-03-oq-04-oq-01-oq-01
**Status**: Completed
**Source**: bezout-identity-oq-03-oq-04-oq-01 (open question #1)

## Problem Statement

Can the folding approach for multiple coprime moduli (iterated CRT) be
generalized to commutative rings? The key lemma named in the parent open
question: if `IsCoprime m₁ m₂` and `IsCoprime (m₁*m₂) m₃`, then
`IsCoprime m₁ (m₂*m₃)` — available in Mathlib as `IsCoprime.mul_right`.

## Answer

YES. Over an arbitrary `CommRing R`, a list of `(residue, modulus)` pairs with
pairwise-coprime moduli always has a simultaneous solution
(`crtRing_list_exists`), unique modulo the product of all moduli
(`crtRing_list_unique`). The construction folds the two-modulus `crtRing`; the
crux is `isCoprime_list_prod` (an element coprime to each factor is coprime to
the product), the iterated form of `IsCoprime.mul_right` the question flagged.

## Result

- Lean file: `Proofs/BezoutIdentityOQ03OQ04OQ01OQ01.lean`
- Gallery: `src/data/proofs/bezout-identity-oq-03-oq-04-oq-01-oq-01/`
- Status: VERIFIED, 0 axioms, 0 sorries, 8 theorems / 1 definition / 196 lines.
