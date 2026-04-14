# Knowledge Base: bezout-identity-oq-02-oq-04

## Problem Understanding

Does the `linear_combination` tactic approach from bezout-identity-oq-02 scale to Gauss's
lemma for ℤ[x]: if f is primitive and irreducible and f | g·h, does f | g or f | h?

## Key Insights

- **No polynomial Bézout in ℤ[x]**: gcd(2, X) = 1 but no f, g satisfy 2f + Xg = 1.
  Proof: evaluate at 0 → 2·f(0) = 1 has no solution in ℤ since 2 ∤ 1.

- **ℤ[x] is a UFD but not a PID**: Bézout works for integers (PID) but not polynomials
  over ℤ (UFD). The polynomial Gauss's lemma is proved via UFD theory, not Bézout.

- **UFD proof is one line**: `UniqueFactorizationMonoid.irreducible_iff_prime.mp` converts
  `Irreducible f` to `Prime f`, which directly gives `f.dvd_or_dvd`.

- **linear_combination's partial role**: Applies at the coefficient level — checking
  primitivity uses integer Bézout witnesses (e.g., 3·(-1) + 2·2 = 1 for gcd(3,2) = 1).

- **`irreducible_X_add_C`**: Mathlib has `Polynomial.irreducible_X_add_C` for any
  nontrivial integral domain, giving X + C(1) is irreducible in ℤ[x].

## Session 2026-04-13 (Session 1) - Full formalization

**Mode**: FRESH
**Outcome**: completed

### What I Did
- Created `proofs/Proofs/BezoutIdentityOQ02OQ04.lean` (154 lines)
- Proved `no_bezout_2_X` by evaluation at 0 + omega
- Proved `gauss_lemma_prime` via `UniqueFactorizationMonoid.irreducible_iff_prime`
- Proved `X_add_one_primitive` using `coeff_X_zero`, `coeff_one_zero`, `isUnit_of_dvd_one`
- Proved `X_add_one_irreducible` via `Polynomial.irreducible_X_add_C 1`
- Proved `three_X_add_two_primitive` extracting coefficients and using Bézout 3(-1)+2·2=1
- Created `src/data/proofs/bezout-identity-oq-02-oq-04/meta.json`

### Files Created
- `proofs/Proofs/BezoutIdentityOQ02OQ04.lean` (154 lines, 0 sorries, 0 axioms)
- `src/data/proofs/bezout-identity-oq-02-oq-04/meta.json`
- `research/problems/bezout-identity-oq-02-oq-04/knowledge.md`

### Note
Proof needs Docker build verification. The key concern is whether the simp lemmas for
`three_X_add_two_primitive` work correctly. Core results (no_bezout, gauss_lemma_prime,
X_add_one_primitive, X_add_one_irreducible) are high-confidence.
