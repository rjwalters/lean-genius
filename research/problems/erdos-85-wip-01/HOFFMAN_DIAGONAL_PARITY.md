# An extra factor of two in the Hoffman divisibility condition

2026-09-08, codex-sol-1. Prose proof and exact executable controls, not Lean.
No novelty claim. This excludes the q16 ledger recorded in
`Q16_HOFFMAN_DIAGONAL_PARITY_REJECTION.md`; it does not establish A-REG.

## General statement

Let A be a symmetric integer n-by-n matrix with zero diagonal, constant
**even** row sum q, and a one-dimensional q-eigenspace spanned by the
all-ones vector. Let h in Z[X] vanish on every other eigenvalue. If n is
**even**, then

    2n divides h(q).

For graph applications connectedness ensures the required principal
multiplicity. C4-freeness and nonnegative matrix entries are unnecessary.
The polynomial need not be minimal, monic, or have any particular parity.
For binary square order q=2^k, n=q², this strengthens the usual necessary
valuation v2(h(q))>=2k to v2(h(q))>=2k+1 when h(q) is nonzero.

## Proof

Every positive diagonal power of A is even. For odd exponent 2r+1,
writing w=A^r e_v gives

    (A^(2r+1))_vv = w^T A w = 2 sum_(i<j) A_ij w_i w_j.

For exponent 2r with r>=1, symmetry and integer-square parity give

    (A^(2r))_vv = sum_w (A^r)_vw²
                 = sum_w (A^r)_vw (mod 2)
                 = q^r (mod 2) = 0.

Consequently diag h(A) is congruent to h(0) modulo two, entrywise.
The spectral theorem and the assumed principal eigenspace give the exact
Hoffman identity

    h(A) = (h(q)/n) J.

Since h(A) has integer entries, c=h(q)/n is an integer. Because n and q
are even, h(0)=h(q)=nc=0 modulo two. Comparing diagonal entries therefore
gives c=0 modulo two. Hence 2n divides h(q).

Both evenness hypotheses matter: K4 has q=3,n=4 and h=X+1, with c=1;
K5 has q=4,n=5 and h=X+1, again with c=1.

## The q16 ledger is excluded

The proposed adjacency spectrum is

    16; -4 (multiplicity 4); -2 (multiplicity 2); +4;
    +/-sqrt(2) (multiplicity 3 each);
    +/-sqrt(14) (multiplicity 99 each);
    +/-sqrt(22) (multiplicity 22 each).

It has simple principal root 16 and order 256. A nonprincipal annihilator is

    h(X)=(X+4)(X+2)(X-4)(X²-2)(X²-14)(X²-22).

Its value is

    h(16)=62,136,771,840=256 * 242,721,765.

The quotient is odd, violating the theorem. Thus this spectrum cannot
belong to any symmetric integer zero-diagonal 16-regular matrix, even
without the C4-free condition. Passing the full cycle-integrality test,
low moments, spectral windows, and ordinary n-divisibility does not evade
this diagonal obstruction. The independently constructed defect-only
local spectral weights likewise cannot extend to such an adjacency matrix.

## Checks and scope

`verify_hoffman_diagonal_parity.py` checks the polynomial arithmetic exactly
and evaluates the Hoffman identity as an actual matrix identity on the
known q4 C4-free control and C6. It checks positive-power diagonal parity
through degree 12 on those controls and K5. K4 and K5 illustrate why the
theorem's degree/order hypotheses must not be removed.

For the actual q4 graph a nonprincipal annihilator is

    X(X+2)(X²-2)(X⁴-8X²+14),

and h(4)/16=2982 is even. This does not exclude that genuine graph.

The argument adds one necessary factor of two; it is not an upper bound
on v2(h(q)), a classification of possible annihilators, or a uniform
exclusion of square-order candidates. Spectra with larger valuation may
survive. No A-REG or Erdős-85 completion is asserted.

Independent proof and executable review: Squad #1479 PASS from Claude.
