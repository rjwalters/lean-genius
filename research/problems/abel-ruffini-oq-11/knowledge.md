# Knowledge: abel-ruffini-oq-11

## Summary

The radical-solvable (positive) side of Abel–Ruffini: equations built from pure
root extractions always have solvable Galois groups.

## What is formalized (researcher-9, 2026-06-25)

`proofs/Proofs/AbelRuffiniOQ11.lean`, namespace `AbelRuffiniOQ11`, 0 ax / 0 sorry:

| Theorem | Statement |
|---|---|
| `gal_pow_sub_C_isSolvable` | `IsSolvable (Xⁿ − C a).Gal` |
| `gal_pow_sub_one_isSolvable` | `IsSolvable (Xⁿ − 1).Gal` |
| `gal_finset_prod_pow_sub_C_isSolvable` | `IsSolvable (∏ᵢ∈s (X^{nᵢ} − C aᵢ)).Gal` |
| `abel_ruffini_two_faces` | dichotomy: pure eqns solvable ∧ Sₘ (m≥5) not |

## Key Mathlib facts

- `gal_X_pow_sub_C_isSolvable (n) (a) : IsSolvable (X^n - C a).Gal`
- `gal_X_pow_sub_one_isSolvable (n) : IsSolvable (X^n - 1).Gal`
- `gal_mul_isSolvable : IsSolvable p.Gal → IsSolvable q.Gal → IsSolvable (p*q).Gal`
- `gal_prod_isSolvable {s : Multiset F[X]} : (∀ p ∈ s, IsSolvable (Gal p)) → IsSolvable s.prod.Gal`
- `Equiv.Perm.not_solvable (X) (5 ≤ #X) : ¬IsSolvable (Equiv.Perm X)`

## The new content

`gal_finset_prod_pow_sub_C_isSolvable`: Mathlib only gives the single equation
and the abstract multiset product. The indexed finite-product form
`∏_{i∈s}(X^{nᵢ} − aᵢ)` is the directly usable "closure" statement. Proof:
`Finset.cons_induction` — `empty` ⇒ `∏ = 1`, `simpa using gal_one_isSolvable`;
`cons` ⇒ `Finset.prod_cons` + `gal_mul_isSolvable (gal_X_pow_sub_C_isSolvable …) ih`.
No multiset bridge needed (cons_induction avoids the Finset→Multiset plumbing).

## Coverage gap confirmed

`grep` over `Proofs/AbelRuffini*.lean` shows NO file referenced the positive
lemmas. The base `AbelRuffini.lean` has `symmetric_group_not_solvable`,
`s5/s6_not_solvable`, `s0/s1_solvable`, `galois_bridge`, `exists_quintic`,
`not_solvable_by_rad_of_not_solvable_gal` — all negative/criterion side.

## Approaches Tried

- Finset→Multiset bridge for the product: avoided in favor of `cons_induction`,
  which is cleaner and needs no `Finset.prod_eq_multiset_prod`.
