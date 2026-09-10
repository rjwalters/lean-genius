# H5/H7 weighted Perron-projector parity — 2026-09-10

Owner: codex-sol-3. **Paper review1596 PASS (codex-sol-2).** This
derives a necessary mod-eight condition for H5; the analogous H7 mod-four
condition is already implied by the reviewed Ihara condition. No spectrum
enumeration, graph witness, or profile exclusion is asserted.
The graph scope is the three listed H5 profiles and the remaining H7/T0
sector; empty and singleton vertices are supplied by those exact censuses.

Throughout, S is the **forward** binary polynomial such that
psi(x)=(x²+x+1)S(x)² modulo2, of degree18 for H5 or16 for H7. This differs
from the reciprocal notation in the Ihara worksheet by reversal.

## Integral scalar in the Perron projector

Use the actual low adjacency C of the [H5/H7 setup](Q7_H5_H7_SQUEEZE_20260910.md).
Put l=49-h, a=(7+sqrt(49-4h))/2, b=7-a, and z=a1-t. Then Cz=az and z>0.
The forced factorization is

    chi_C(x)=x^(h-1)(x-a)(x-b)psi(x).

The eigenvalue a is simple: all eigenvalues from K have absolute value at
most sqrt(6+rho(D))<a, and the other fixed roots are0 and b. Work in the
quadratic order O=Z[a]. Let f_a(x)=chi_C(x)/(x-a), a polynomial in O[x].
Spectral projection gives

    f_a(C)=tau*z*z^T,
    tau=a^(h-1)(a-b)psi(a)/<z,z>
        =a^(h-1)psi(a)/(l*a-8h).

For the last equality, sum t=8h, sum t²=h(h+7), and a²-7a+h=0 give
<z,z>=(a-b)(l*a-8h). There is an empty-support vertex e and a singleton
vertex s, so z_e-z_s=1. Therefore

    tau=(e_e-e_s)^T f_a(C)(e_e-e_s) belongs to O.

Thus the division used here is integral in the quadratic order. Merely
reducing the displayed fraction modulo2 before proving this would be invalid.

## Diagonal parity determines tau modulo two

The reduction O/2O is F4: a²+a+1=0, b=a², ab=1. For a symmetric
zero-diagonal integer matrix C, in characteristic two

    diag(C^(2j+1))=0,   diag(C^(2j))=C^j 1.

The first identity follows from alternation of C applied to C^j e_i; the
second follows by squaring the entries in the i-th row of C^j, which are
in F2. It includes j=0. Hence for any polynomial f with coefficients in
F4, diag(f(C))=f_even(C)1, where f_even(x)=sum f_(2j)x^j.

Write n=(h-1)/2. Characteristic parity gives, modulo2,

    f_a(x)=(x-a)H(x)²,   H(x)=x^n(x-b)S(x).

Its even-coefficient polynomial is a H^(2), where H^(2) means squaring
each coefficient, without changing its exponent. Frobenius sends b to a,
so H^(2)(x)=x^n(x-a)S(x). The vector

    (C-aI)1=b1-t=z²

is a b-eigenvector modulo2; here z² is coordinatewise squaring. Consequently

    diag(f_a(C))=a*b^n*S(b)*z².

On the other hand the projector formula gives diag(f_a(C))=tau*z².
At an empty vertex z²=a² is nonzero in F4. Cancellation proves

    tau = a*b^n*S(b) modulo2.                         (1)

This argument does not require C to have even constant row sum. It uses
the actual weighted Perron vector and zero-diagonal parity instead.

## H5 and H7 consequences

For H5, l*a-8h=44a-40=4(11a-10), whose factor in parentheses reduces
to a modulo2. Also a is a unit modulo powers of2, and n=2. Multiplying
(1) by the denominator and using a³=1 in F4 gives

    psi_5(a) = 4*b*S(b) modulo8 in Z[a].              (2)

For H7, l*a-8h=42a-56=2(21a-28), with the same unit reduction a and n=3.
This gives

    psi_7(a) = 2*b*S(b) modulo4 in Z[a].              (3)

Condition(3) is redundant with the reviewed Ihara congruence. In forward
notation Ihara gives psi7(x)=(x²+3x+1)S(x)² modulo4. At a,
x²+3x+1 becomes2(a-1) modulo4; modulo2, a-1=b and S(a)²=S(b).
This gives precisely(3).

For H5, Ihara only forces psi5(a)=0 modulo4. Condition(2) determines
the next bit in each of the two coefficients in the basis(1,a). The controls
below show that it does not follow from the particular earlier coefficient
constraints tested. This is not a claim of independence from every Sachs,
walk, or other arithmetic theorem in the repository.

The same derivation gives psi1(a)=8*a*S(b) modulo16 and
psi3(a)=2*b*S(b) modulo4. Those sectors belong to sol1; this note does not
run their consumers. The H3 condition is likewise implied by Ihara.

## Exact calibration and limits

`verify_q7_h5_h7_weighted_hoffman.py` checks the field reductions and the
H7 redundancy. It then constructs three actual symmetric zero-diagonal
0/1 matrices C of order24 with C1=7·1-t and Ct=5·1, t=0 on four vertices
and1 on twenty vertices. Their characteristic polynomials have the required
fixed factor x^4(x²-7x+5). The graph controls are connected and check the
integral tau and parity(1), including nonzero F4 outputs. They have C4s,
the wrong order/support census, and are **not** q7 graph candidates.
The four empty vertices0,1,2,3 explicitly form a C4 in every control;
the verifier checks and records those four edges. Their denominator is24a-20,
so(2) is not applied to them.

Separate degree38 coefficient controls have the exact first four H5
Newton coefficients for T=5 or6, the reviewed Ihara congruence modulo4,
psi5(8)=0 modulo13, x^4 dividing psi5 modulo7, and a nonzero constant
divisible by7^4. Four lifts for each T retain all those properties but
vary the two new mod-eight bits. Exactly one lift per T passes(2); the
other three fail. These are only coefficient controls. Real roots, spectral
bounds, all remaining moments, an integral C, and graph realizability are
not asserted for any of them. No q7 profile has been eliminated by this test.

Independent review1596 checked the projection normalization, integrality,
Frobenius step, modulus specialization, H7 redundancy, and all clarified
controls. It independently recomputed the first four Newton coefficients
of the eight coefficient controls. The full argument remains a paper proof.

`Proofs/Erdos85NonregularDiagonalParity.lean` supplies the two matrix-power
identities over ZMod2 without a row-sum assumption. Both lemmas compile and
report only propext, Classical.choice, and Quot.sound; independent compile
review1598 passed with the same axiom reports. This formalizes the base matrix-power identities,
not their coefficient-field extension or the Perron-projector argument.
