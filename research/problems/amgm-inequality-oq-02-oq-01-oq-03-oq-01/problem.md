# Problem: Newton–Girard $k=4$ closed form $p_4 = e_1^4 - 4 e_1^2 e_2 + 2 e_2^2 + 4 e_1 e_3 - 4 e_4$

**Slug**: amgm-inequality-oq-02-oq-01-oq-03-oq-01
**Created**: 2026-06-20
**Status**: SOLVED
**Source**: follow-up open question of gallery proof amgm-inequality-oq-02-oq-01-oq-03 (k=3 closed form)

## Problem Statement

### Formal Statement

For a finite indexed family $x_1,\dots,x_m$ with power sums $p_k = \sum_i x_i^k$ and
elementary symmetric polynomials $e_k$, prove the $k=4$ Newton–Girard closed form
$$
p_4 = e_1^4 - 4\,e_1^2 e_2 + 2\,e_2^2 + 4\,e_1 e_3 - 4\,e_4,
$$
both as the universal MvPolynomial statement and as a concrete identity over a `Finset`
of values in an arbitrary commutative ring (characteristic 2 included).

### Why This Matters

This is the explicit next rung after the k=3 closed form
`amgm-inequality-oq-02-oq-01-oq-03`. It is the first case whose reduced expression is
genuinely quartic in the elementary symmetric polynomials (the cross term $2 e_2^2$),
and it is a direct test of whether the k=3 `aeval` bridge is degree-general — it is,
so the concrete form costs only two one-line bridge instantiations.

## Resolution

Proved 2026-06-20 in `proofs/Proofs/AmgmInequalityOQ02OQ01OQ03OQ01.lean`
(Docker-verified GREEN, Lean v4.26.0; 6 theorems, 2 defs, 0 sorries, 0 axioms):

1. `psum_four_recurrence` — extract $p_4 = e_1 p_3 - e_2 p_2 + e_3 p_1 - 4 e_4$ from
   `MvPolynomial.psum_eq_mul_esymm_sub_sum` at $n=4$.
2. `psum_four_closed` — substitute the proven $p_3, p_2, p_1$ closed forms and `ring`.
3. `newton_girard_four_finset` — transport `psum_four_closed` across the (degree-general)
   k=3 `aeval` bridge at degree 4; holds over any `CommRing`.
4. `fourth_power_sum_four` — the explicit 4-variable instance.

Independently certified in `lean/verify_newton_girard_k4.py` (symbolic residual 0,
$n=2..6$).
