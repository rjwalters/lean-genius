# Hoffman diagonal parity rejects a q16 mod-four spectral control

2026-09-08, Sol3. Bounded feasibility probe under A-REG-NONBIP.
Final rejection independently reviewed by Claude (#1480 PASS).
**The full spectral ledger below cannot be realized by a symmetric integer
matrix with zero diagonal and constant row sum 16.** Sol1 found the
annihilator parity obstruction, independently confirmed by Claude; Sol3
supplied the even-power simplification below. The argument needs no
C4-freeness. It rejects this particular ledger, not every A-REG candidate.

## General parity refinement of Hoffman divisibility

Let A be a symmetric integer matrix with zero diagonal, even constant row
sum q, and simple eigenvalue q. Let h in Z[x] annihilate all nonprincipal
eigenvalues. The Hoffman identity is h(A)=cJ, where c=h(q)/n. Integer
entries force c to be an integer. Moreover,

    c = h(0) modulo two, or equivalently
    2n divides h(q)-n*h(0).                              (1)

To prove this, every positive power of A has even diagonal. For odd
powers, (A^(2r+1))_uu=v^T A v with v=A^r e_u, which is even by symmetry
and zero diagonal. For even powers 2r>=2,

    (A^(2r))_uu = sum_v (A^r_uv)^2
                 = sum_v A^r_uv = q^r = 0 modulo two.

Hence diag h(A)=h(0) modulo two. Comparing with cJ proves (1). No
uncontrolled higher local-walk counts enter this mod-two identity.
Evenness of n is not required. If h(0) is even, (1) strengthens the
usual n|h(q) to 2n|h(q).
In binary square order n is also even: n|h(q) and even q then force
h(0) to be even, so the stronger 2n divisibility applies to every such h.
The same necessary condition is recorded in `HOFFMAN_DIAGONAL_PARITY.md`;
this note supplies the explicit q16 ledger and its rejection, not a second
independent obstruction.

## The full ledger

For n=256 and q=16 take the following adjacency eigenvalues:

| Eigenvalue | Multiplicity |
| --- | ---: |
| 16 | 1 |
| -4 | 4 |
| -2 | 2 |
| 4 | 1 |
| each of +sqrt(2), -sqrt(2) | 3 |
| each of +sqrt(14), -sqrt(14) | 99 |
| each of +sqrt(22), -sqrt(22) | 22 |

All 256 roots are nonzero. The principal root is simple, and every other
root has absolute value at most sqrt(30). The reciprocal characteristic
polynomial is the integer polynomial

    P_A(t)=(1-16t)(1+4t)^4(1+2t)^2(1-4t)
           (1-2t^2)^3(1-14t^2)^99(1-22t^2)^22.

The first four traces are

    tr A=0, tr A^2=4096, tr A^3=3888, tr A^4=126976.

Thus they satisfy tr A^2=nq, tr A^4=nq(2q-1), and
0<=tr A^3<=nq (indeed also tr A^3>=2n). The putative triangle count is
648. This is the degree/triangle/C4 moment pattern, not proof of zero
diagonal or C4-freeness of a realizing matrix.

## Complete primitive-cycle integrality and positivity pass

In fact **P_A(t)=1 modulo four**. Every linear factor is 1 modulo four
except (1+2t)^2, which is also 1 modulo four. All three quadratic types
are 1+2t^2 modulo four, with total exponent 124; their product is 1
modulo four as well. The finite criterion in
`NONBACKTRACKING_INTEGRALITY_MOD4.md` therefore gives integrality of
every formal primitive nonbacktracking count. Together with
`NONBACKTRACKING_POSITIVITY_AUDIT.md`, the preceding window and moments
give nonnegativity at **all lengths**, not merely a checked prefix.
The equivalent all-length ordinary-walk congruences pass too.

## Induced defect ledger and Hoffman checks

Using D=15I+J-A^2 spectrally, with J acting by 256 on the principal
line and zero on the remaining sectors, gives

    D: 15^1, (-1)^5, 11^2, 13^6, 1^198, (-7)^44.

Here superscripts are multiplicities. The first three traces are
0,3840,4320; the putative defect graph is 15-regular with 720 triangles.
The principal root is simple and all residual roots have modulus <15.
This is consistent with connectedness at the spectral level only.

Its reciprocal polynomial also passes the finite mod-four square test:

    P_D(t)=(1-15t)(1+t)^5(1-11t)^2(1-13t)^6
           (1-t)^198(1+7t)^44
          = (1+t)^8(1-t)^248 modulo four
          = (1-t)^256 modulo four.

The last expression is an integer-polynomial square. Although D has odd
degree, both n and m_D-n=256*15/2-256 are even, so the square-prefactor
argument of the integrality audit also applies to this particular D ledger.
No all-length positivity claim about D is needed here.

For the minimum-degree monic annihilators of the nonprincipal spectra,

    h_A(x)=(x+4)(x+2)(x-4)(x^2-2)(x^2-14)(x^2-22),
    h_D(x)=(x+1)(x-11)(x-13)(x-1)(x+7),

one has v_2(h_A(16))=8 and v_2(h_D(15))=9. Hence both values are
divisible by n=256. These pass the previously used Hoffman projector
divisibility obstruction; merely using nonminimal annihilators would
not have established this check. The factors above are distinct
irreducible factors over Q and exhaust the corresponding residual roots.

But h_A(0)=19712 is even, whereas

    h_A(16)=62136771840=256*242721765

has an odd quotient by 256. This contradicts (1) and rejects the ledger.
Equivalently h_A is x^9 modulo two, so its diagonal is even, while the
projector identity demands the same odd integer on every diagonal entry.
The general proof above does not require h to be a monomial modulo two.

## Verification and decision

`verify_q16_hoffman_diagonal_parity_rejection.py` verifies the root counts, moments,
window, reciprocal polynomials, exact mod-four congruences, induced D
ledger, and both minimal Hoffman products. It independently recovers
moments from polynomial coefficients and calibrates primitive counts
through length 20. The all-length statements follow from the two cited
in-repository proofs, not from that finite prefix. It then verifies the
exact odd quotient/even constant contradiction. Positive matrix checks
include the actual q4 graph and a triangle (whose h(0) is odd, so the
constant correction in (1) matters).

The previous q16 ledger in `NONBIP_CONNECTED_ODD_POWER_MOD4_AUDIT.md`
is still excluded; this different ledger passes its all-length walk
congruence obstruction but is rejected by (1). No search over graph
realizations has been performed.

**Decision:** the low moments, stated spectral windows, both minimal
Hoffman divisibility tests, and complete primitive-cycle tests on A
admit this q16 formal spectrum, but the stronger Hoffman diagonal parity
condition rejects it. This is a scoped improvement in necessary conditions,
not a classification of all spectra or a uniform A-REG exclusion. No Lean
theorem status is changed.
