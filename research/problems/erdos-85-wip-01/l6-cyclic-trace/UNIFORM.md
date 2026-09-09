# Uniform exclusion of the interval circulant defect

**Theorem.** Let q=2^k with k>=2, n=q^2 and m=q/2. Let D be the circulant
on Z/n with connection set {n/2} union +/-{1,...,m-1}. There is no rational
symmetric matrix A satisfying

    A^2 = (q-1)I + J - D,    A1=q1,    trace(A)=0.

In particular this D cannot be the defect of a q-regular loopless C4-free
graph on q^2 vertices. This excludes one specified defect family for all
binary q>=4. It does not reduce arbitrary defects to that family, does not
prove A-REG, and does not solve Erdos85.

## The missing nonsquareness input is elementary modulo two

Fix a power of two d with q<d<=n and d|n. Let zeta be a primitive d-th root,
L=Q(zeta), and N=d/2. Write

    lambda = c - sum_{j=1}^{m-1}(zeta^j + zeta^-j),

where c=q-2 if d<n and c=q if d=n. In both cases c is even. We claim
lambda is not a square even in the full cyclotomic field L.

The ring of integers of L is Z[zeta], and its defining polynomial is
Phi_d(X)=X^N+1. The integer-ring statement is Proposition6.2(b) in
[J.S. Milne, Algebraic Number Theory, version3.01](https://www.jmilne.org/math/CourseNotes/ANT301.pdf),
printed page90 (PDF page98). Thus

    O_L / 2 O_L = F2[X] / (X^N+1).

If lambda=b^2 in L, then b is an algebraic integer (substitute b^2 into a
monic integer polynomial for lambda), so b belongs to O_L and can be
reduced in this quotient. Every square there has zero coefficient on each
odd power in its unique representative of degree<N: squaring doubles all
exponents, and reduction modulo X^N+1 preserves exponent parity since N
is even.

But the representative of lambda modulo two is

    sum_{j=1}^{m-1}(X^j + X^(N-j)).

Since d>=2q, we have N>=q=2m. The two exponent intervals [1,m-1] and
[N-m+1,N-1] are disjoint. In particular the coefficient of X is exactly1,
because m>=2. This contradicts the necessary condition for a square.
Therefore lambda is nonsquare in L, hence also in its real subfield and
in Q(lambda). This is a uniform proof, not an extrapolation from norm data.

## Finish by rational trace

The Fourier decomposition from NOTE.md applies for every binary q>=4:
M=(q-1)I+J-D has eigenvalue n once, q with multiplicity m-1, q-2 with
multiplicity m, and the higher-order lambda values just considered.
All high-order values are nonsquares in their eigenfields. If h is the
minimal polynomial of such a value, h(T^2) is irreducible and even over Q,
by the degree tower Q(sqrt(lambda))/Q(lambda)/Q. Consequently any rational
matrix squaring to M has zero total trace contribution from these factors.
Coincidence of values between cyclotomic strata does not affect that argument.

The value q-2 is a nonsquare rational integer, since q-2 is 2 modulo4,
so its contribution is also zero. These values cannot coincide with n.

If k is odd, q is a nonsquare rational integer as well. All nonprincipal
contributions therefore vanish, leaving trace(A)=q, a contradiction.

If k is even, write q=s^2 with s even. The q-eigenspace has odd dimension
m-1, so its square-root eigenvalues +/-s contribute s times an odd integer.
The n-eigenspace contributes q because A1=q1. Thus trace(A)/s equals
s plus an odd integer, and cannot vanish. This also gives a contradiction.

The argument uses rational spectral multiplicities, not a requirement that
A preserve individual Fourier spaces or be circulant. It specializes the
existing trace-escape/sign-pairing interface (cuts ledger rows10 and17) by
supplying its missing square-in-eigenfield test for this particular family.

## Verification and limitations

`check_mod2.py` checks the polynomial coefficient obstruction and dimension
census for q=4,8,16,32,64. These are regression examples; the proof above
covers every k>=2 without computation. The earlier exact norm certificates
remain valid independent checks at q16/64, but are unnecessary for the
uniform theorem. No new package installation, dense matrix, or graph search
is required. No Lean formalization of this theorem is claimed.
