# An unbounded formal family passes the specified spectral filters

2026-09-08, Sol3, with independently derived multiplicities and checks by
Sol1. Prose algebra and exact executable checks; not Lean-formalized.

**These are formal eigenvalue lists, not graphs or integer matrix
realizations.** The family passes the specific conditions enumerated here
for every binary q=2^k with k>=10. It does not refute A-REG,
establish any graph-existence claim, or show that all spectral methods fail.

## Parameter and full spectrum

Let t=2^j with j>=5, alpha in {1,2}, q=alpha*t^2, and n=q^2.
These two cases cover respectively even and odd k>=10. Use real roots

    q once; -4 with multiplicity q/4; -2 twice; +4 once.

In addition, include each root +sqrt(a) and -sqrt(a) with multiplicity c_a:

| a | c_a when alpha=1 | c_a when alpha=2 |
| --- | --- | --- |
| 4 | (t^2-8t+48)/16 | (t^2-4t+12)/4 |
| 8 | (t-24)/8 | (t-12)/4 |
| q-alpha*t | (5t^4+11t^3+46t^2-28t-544)/32 | (2t^4+5t^3+15t^2-6t-72)/8 |
| q | (3t^4-6t^3-43t^2+38t+496)/16 | (6t^4-3t^3-14t^2+11t+60)/4 |
| q+alpha*t | (5t^4+t^3+34t^2-36t-512)/32 | (2t^4+t^3+9t^2-10t-64)/8 |

Multiplicities add when roots coincide: the paired roots at a=4 add to
the two explicit copies of -2. All counts are integers because 32|t
and the constant numerators are divisible by their respective denominators.
They are strictly positive for t>=32. In the alpha=1 case, for c_4 the numerator is
(t-4)^2+32; c_8 is immediate. For c_(q-t), the two negative terms have
sum at most 2t^2. For c_(q+t), they have sum at most 3t^2. For c_q,
write the numerator as t^2(3t^2-6t-43)+38t+496, all positive at t>=32.
In the alpha=2 case, c_4 has numerator (t-2)^2+8 and c_8 is immediate.
Each outer quartic's negative terms total at most 2t^2, dominated by its
positive quadratic term. For c_q, use
t^2(6t^2-3t-14)+11t+60>0.

## Exact moments and spectral windows

Put N=sum c_a, S_1=sum a*c_a, S_2=sum a^2*c_a. Direct polynomial identities give

    N   = (q^2-q/4-4)/2,
    S_1 = (q^3-q^2-4q-24)/2,
    S_2 = (q^4-q^3-64q-288)/2.

Consequently the full list has n roots and

    tr A=0, tr A^2=q^3,
    tr A^3=q^3-16q+48,
    tr A^4=q^3(2q-1).

In particular 2n<=tr A^3<=nq: the lower-bound difference is
q^2(q-2)-16q+48>0 for q>=1024, and the upper bound is immediate.
These are the named square-order degree/triangle/C4 moment conditions,
not evidence of entrywise C4-freeness.

All roots are nonzero. The principal root q is simple. Every other
squared root is at most q+alpha*t<=2(q-1), since t>=32. Thus the existing
residual spectral window holds. The formal defect D=(q-1)I+J-A^2,
with J acting by n on the principal line and zero elsewhere, has spectrum

| D root | multiplicity |
| --- | --- |
| q-1 | 1 |
| q-17 | q/4+1 |
| q-5 | 2+2c_4 |
| q-9 | 2c_8 |
| alpha*t-1 | 2c_(q-alpha*t) |
| -1 | 2c_q |
| -alpha*t-1 | 2c_(q+alpha*t) |

The order is n, tr D=0, and tr D^2=n(q-1). All residual roots have
modulus strictly less than q-1. This permits connected, nonbipartite
defect behavior spectrally; it does not supply such a defect graph.

## Complete primitive-cycle tests on A pass

The reciprocal polynomial factors as

    P_A(z)=(1-qz)(1+4z)^(q/4)(1+2z)^2(1-4z)
           product_a (1-a z^2)^c_a.

Every a in the table is divisible by four. The displayed real-root
factors are also 1 modulo four, including (1+2z)^2. Hence P_A=1 modulo
four, without needing to expand its degree-n coefficient list.

`NONBACKTRACKING_INTEGRALITY_MOD4.md` now implies integrality of the
formal primitive nonbacktracking counts at every length. The moments
and window above invoke `NONBACKTRACKING_POSITIVITY_AUDIT.md` to give
nonnegativity at every length (strict positivity at lengths >=5).
Equivalently, all the classical ordinary-walk congruences in that
integrality audit hold. This is an all-length proof, not extrapolation
from a finite prefix.

Every D root is -1 modulo four, so P_D(z)=(1+z)^n modulo four, itself
an integer-polynomial square because n is even. The square-prefactor
argument for integrality also applies to D: although its degree is odd,
n and n(q-1)/2-n are both even because 4|n. We do not use the A positivity
theorem to assert all-length positivity for D.

## Minimal Hoffman divisibility and the extra parity bit pass

The minimal monic nonprincipal annihilator for A is

    h_A(X)=(X^2-16)(X^2-4)(X^2-8)(X^2-q)
           ((X^2-q)^2-alpha*q).

Its twelve distinct roots are exactly the nonprincipal A roots: the six
positive squared values 16,4,8,q-alpha*t,q,q+alpha*t are distinct, and
both signs occur for each. All roots are present because all multiplicities
are positive. Repeated roots have not artificially inflated the divisibility
check; irreducibility of each quadratic is unnecessary.

Write e=v_2(alpha) in {0,1}, so k=log_2(q)=2j+e. Evaluating the five
displayed factors at q gives valuations 4,2,3,k,k+e respectively, and therefore

    v_2(h_A(q))=2k+9+e.

For the quartic value (q^2-q)^2-alpha*q, the two terms have valuations
2k and k+e, distinct because k>e; its valuation is therefore k+e.

For the minimal degree-six nonprincipal annihilator of D,

    h_D(q-1)=16*4*8*(q-alpha*t)*q*(q+alpha*t)
             =512q^2(q-alpha),

so its valuation is also 2k+9+e. Both ordinary Hoffman divisibility
tests n|h(q) pass. The strengthened A condition from
`HOFFMAN_DIAGONAL_PARITY.md`, requiring 2n|h_A(q), also passes, with
eight or nine valuation bits to spare. Moreover h_A(0)=512q^2(q-alpha) is even,
and h_A(q)/n has valuation 9+e, agreeing with the general constant-term
parity correction in `Q16_HOFFMAN_DIAGONAL_PARITY_REJECTION.md`.

## Verification and decision

The standard-library verifier checks the multiplicity/moment identities
symbolically over rational polynomials, including positivity via shifted
coefficients, then checks both compressed spectra at j=5..12. It verifies
the residue arguments and valuations without expanding a polynomial of
degree q^2, and calibrates formal primitive counts through length 20.
The uniform proofs above, rather than those sampled powers, establish the
claims for every j>=5 in both cases, hence for every k>=10.

The family passes: the listed A moments and residual window; the induced
D order, first two moments and strict residual window; complete A
primitive-cycle positivity/integrality; D's finite mod-four square test;
both minimal Hoffman divisibility tests; and A's extra diagonal-parity bit.
No other graph-realizability condition is claimed to pass. In particular
we have not constructed symmetric 0/1 matrices with these spectra.

**Decision:** the new factor-of-two obstruction does reject the separate
q16 ledger, but the combined filters listed here still admit formal
spectra for every binary k>=10. Repeating those tests at more cycle lengths or more j
cannot exclude this family. A further constraint must be named and tested;
A-REG and Erdős 85 remain open.
