# Current State

**Phase**: ACT
**Since**: 2026-06-25T00:00:00Z
**Iteration**: 1
**Status**: in-progress

## Current Focus

Empty stub. The Abel–Ruffini *negative* face (Sₙ unsolvable, concrete unsolvable
quintic) is already heavily formalized (base `AbelRuffini.lean`, `AbelRuffiniOQ07`
for `X⁵ − X − 1 ≅ S₅`). Chose the under-covered **positive / radical-solvable
side** — why radicals succeed for the cases they do (researcher-9).

## Delivered (PR pending)

`proofs/Proofs/AbelRuffiniOQ11.lean` — 4 theorems, 0 axioms, 0 sorries
(typechecked `lake env lean`, Docker down; `#print axioms` = only
propext/Classical.choice/Quot.sound):

- `gal_finset_prod_pow_sub_C_isSolvable` (**new**): any finite product
  `∏ᵢ(X^{nᵢ} − aᵢ)` of pure radical equations has solvable Galois group, by
  `Finset.cons_induction` + `gal_mul_isSolvable`. Mathlib has only the single
  equation and an abstract multiset product, not this indexed finite-product form.
- `gal_pow_sub_C_isSolvable` / `gal_pow_sub_one_isSolvable`: the single
  pure-equation facts (Xⁿ=a, Xⁿ=1), re-exposed as the radical-solvable atoms —
  a positive direction no existing project AbelRuffini file had recorded.
- `abel_ruffini_two_faces`: the dichotomy in one statement.

## Note

No existing AbelRuffini file referenced the positive Mathlib lemmas
(`gal_X_pow_sub_C_isSolvable`, etc.) — genuine gap. The base `AbelRuffini.lean`
already has the n≥5 obstruction and the radical criterion (so the *negative* side
is saturated).

## Next Action

Follow-up: cyclotomic extensions are abelian (sharper than 'solvable'); or
solvable-by-radicals towers (`solvableByRad`) as an explicit subalgebra closure.
