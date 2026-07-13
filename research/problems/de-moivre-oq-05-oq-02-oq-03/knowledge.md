# de-moivre-oq-05-oq-02-oq-03

**Status**: COMPLETED (PR #32451, VERIFIED 0-axiom)

## Problem
Formalize ∑_{ord ζ = n} ζ = μ(n) over a general field containing a primitive
n-th root of unity (parent de-moivre-oq-05-oq-02 did the ℂ case).

## Result (delivered, strengthened)
Proved over ANY commutative integral domain R with IsPrimitiveRoot ζ n:
  ∑ z ∈ primitiveRoots n R, z = (μ n : R)
plus a field specialization. `proofs/Proofs/DeMoivreOQ05OQ02OQ03.lean`
(4 thm, 0 def, 155 L, 0 sorry; axioms = propext/Classical.choice/Quot.sound only).

## Session 1 (2026-07-01, FRESH) — completed
### Key findings / recipe
- The parent's ℂ proof is purely algebraic; only two ℂ-specific ingredients needed
  replacing: existence of the generator (→ hypothesis) and DecidableEq (→ classical
  + [DecidableEq R] on the image helpers).
- All Mathlib ingredients generalize to [CommRing R][IsDomain R]:
  `IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots`, `.disjoint`,
  `.geom_sum_eq_zero`, `.eq_pow_of_pow_eq_one`, `.injOn_pow`, `.pow`, `.one`;
  Möbius inversion `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq` is over any ring.
- DECOUPLING INSIGHT: the divisor partition ∑_{d∣k} f(d)=g(k) holds over the ambient
  domain with NO primitive root assumed (it just groups present roots by order).
  Root existence is only needed for the local evaluation g(d)=[d=1], and the required
  primitive d-th root is manufactured as ζ^{n/d} via `IsPrimitiveRoot.pow hn hprod.symm`.
- FREE MATH: hypothesis IsPrimitiveRoot ζ n forces char R ∤ n (Frobenius injectivity),
  so (μ n : R) is well-defined without any characteristic assumption.

### Gotchas
- `.image` in a lemma STATEMENT needs [DecidableEq R] at the type level; `classical`
  inside the body is too late. Add [DecidableEq R] to the helper lemmas; the main
  theorem supplies it via `classical`.
- `IsPrimitiveRoot.pow` expects `n = a*b`; antidiagonal gives `a*b = n` → use `hprod.symm`.

### Build
`cd main/proofs && env -u LAKE lake env lean <abs path>` (docker broken; main has mathlib cache).
