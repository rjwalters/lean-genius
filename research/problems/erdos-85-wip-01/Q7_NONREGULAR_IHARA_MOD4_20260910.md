# Nonregular q7 Ihara reduction modulo four — 2026-09-10

Owner: codex-sol-3. Paper derivation passed independent review1581 by
codex-sol-2; no Lean
formalization, no spectrum enumeration, no excluded profile or graph witness.
This is an applicability reduction for Phase A. It does not apply the regular
even-degree formula to a mixed-degree graph.

## Statement

Use the exact H5/H7 block hypotheses and residual polynomial psi of
[the setup worksheet](Q7_H5_H7_SQUEEZE_20260910.md). Write k=48-2h and
c(u)=u^k psi(1/u), so c(0)=1. Adjacency characteristic parity gives

    c(u) = (1+u+u²) S(u)² modulo2,

where S is the unique binary-coefficient polynomial of degree at most
(k-2)/2 with constant coefficient1. The actual graph necessarily satisfies

    h=5: c(u) = (1+u+u²) S(u)² modulo4;
    h=7: c(u) = (1+3u+u²) S(u)² modulo4.

More precisely, under the displayed parity and fixed block factorization,
these congruences are equivalent to the reduced Ihara determinant being an
integer-series square. This does not assert nonnegativity of its formal
primitive counts or the existence of a graph for any coefficient data.

## Actual mixed-degree determinant

Bass's general formula uses the diagonal degree matrix, not a scalar degree:
the inverse Ihara zeta function is

    (1-u²)^(m-n) det(I-uA+u²(diag(d)-I)).

See [Rangarajan, Theorem2, PDF page3](https://drops.dagstuhl.de/storage/00lipics/lipics-vol093-fsttcs2017/LIPIcs.FSTTCS.2017.46/LIPIcs.FSTTCS.2017.46.pdf).
Here n=49, m=(343+h)/2, and diag(d)-I has value7 on highs and6 on lows.
The formula applies componentwise if necessary. The Euler factors of the
inverse zeta occur in reversal pairs: an undirected cyclically reduced
nonempty walk cannot equal its reversal up to cyclic rotation. A reflection
of its cyclic oriented-edge sequence would force a fixed reversed edge or
an adjacent inverse pair. Both are forbidden in a loopless nonbacktracking
walk. Thus the inverse zeta is a square in Z[[u]], with root constant1.

Both A and the degree matrix preserve the three summands in the setup.
Each paired high-difference block contributes

    F(u)=(1+7u²)(1+6u²)-7u²=1+6u²+42u⁴.

On the three-dimensional quotient, the degree matrix minus identity acts
as diag(7,6,6), and adjacency acts as

    Q_h=[0 8 h+7; 0 7 h; 1 -1 0].

Therefore its contribution is

    H_h(u)=det(I-uQ_h+u²diag(7,6,6))
          =1-7u+12u²-(42+h)u³+(78+h)u⁴-294u⁵+252u⁶.

On K the contribution is

    R(u)=(1+6u²)^k c(u/(1+6u²)).

Since h-1 is even, F^(h-1) is already an integer unit-series square.
Removing it and the even part of the exponent m-n leaves

    P_h(u)=f_h(u) R(u),
    f_5=(1-u²)H_5,   f_7=H_7.

These removals preserve square status in Z[[u]]. The finite square-series
criterion is the already-reviewed [integer-series mod-four lemma](NONBACKTRACKING_INTEGRALITY_MOD4.md):
a unit polynomial is an integer-series square exactly when it agrees modulo4
with the square of the binary lift of its formal square root modulo2.

## Reduction to the reciprocal residual polynomial

Put q=1+u+u² and write c=qS²+2L with L an integer polynomial. Since k is
even and6=2 modulo4, direct expansion gives

    R = c+2u³c' modulo4.

Indeed (1+6u²)^k=1 modulo4, and the substituted variable is u+2u³ modulo4.
Also c'=q'S² modulo2. Define the binary polynomials

    g_5=1+u+u³+u⁴,   g_7=1+u³.

One checks f_h q=g_h² modulo2, so g_h S is the required binary square-root
lift modulo2 (its integer coefficients may exceed1; changing them by even
integers does not change its square modulo4). The mod-four criterion is
therefore equivalent to

    (f_h modulo2)(L modulo2)=(W_h modulo2)S²,
    W_h=(g_h²-f_h q-2f_h u³q')/2.

The numerator is even coefficientwise. Exact polynomial expansion yields

    f_5 modulo2=(u+1)^4 q,   W_5 modulo2=0;
    f_7 modulo2=(u+1)^2 q,   W_7 modulo2=u(u+1)^2 q.

Cancellation in F2[u] gives L=0 modulo2 for h5 and L=uS² modulo2 for h7.
Substitution into c=qS²+2L proves the stated equivalence.

## Verification scope and next consumer

`verify_q7_nonregular_ihara_mod4.py` checks the quotient determinant and W
identities exactly, then compares the original reduced-polynomial square
test with the claimed residual congruence on deterministic coefficient
controls. It includes controls satisfying the condition and mutations that
fail it. These are polynomial controls, not spectra or actual q7 graphs.

This restriction can be evaluated on a fully specified residual polynomial.
It is not the redundant full-Gram test det(I+tA²), and no claim is made that
it is independent of every existing walk/Sachs congruence. Prior-filter
coverage must be reconciled before a spectrum campaign. No kill follows
from the leading coefficient checks alone.

Independent review1581 checked the primary Bass formula, reversal pairing,
three invariant blocks, prefactor parities, derivative substitution, and
mod-two cancellation, and reran all64 controls in a private directory.
Its scope is the algebraic applicability reduction above.
