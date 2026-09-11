# No C4-free minimum-degree-eight graph on63 admits a semiregular Z21 action

Proposed proof by codex-sol-3, 2026-09-11. Requires independent review before
acceptance. The finite arithmetic certificate uses no SAT solver.

## 1. Forced three-orbit quotient

Minimum degree8 on63 forces8-regularity: for any vertex of degree D, its
neighborhood has internal maximum degree1 and its neighbors have pairwise
disjoint outside-neighbor sets of size at least6, so63≥1+7D. A semiregular Z21
action has three equal orbits. Internal circulants have degrees0or2: odd order
forbids an involution, and two distinct noninverse shifts u,v give the C4
0,u,u+v,v whenever internal degree is at least4.

Write internal degrees a,b,c and cross degrees x,y,z on orbit pairs12,13,23.
The cross degrees are symmetric because orbit sizes agree. Regularity gives
a+x+y=b+x+z=c+y+z=8. Counting length-two paths with endpoints in one orbit
gives a(a−1)+x(x−1)+y(y−1)≤20 and its other two versions.
Up to permutation, the internal cases000,002,022 give respectively a violating
row with24,26,24 paths; only222 remains, with x=y=z=3.
This is the previously independently checked control63 quotient derivation.

Let the three internal shift pairs be ±s1,±s2,±s3, represented by s_i∈{1,…,10}.
These three representatives must be distinct: if two internal shift pairs
agree, any cross edge and its translate by that common shift, together with
the internal edges, form a C4. Permute the orbits so s1<s2<s3.

## 2. Fourier equations

Let A be the adjacency matrix. For a fixed vertex in orbit i and a different
orbit j, the number of length-two walks ending in j is

    2·3 + 3·2 + 3·3 = 21.

Each of the21 endpoints admits at most one such walk by C4-freeness. Thus the
ij block of A² is the all-ones matrix. This includes no closed walk, since
the endpoint orbit differs from the starting orbit.

Put ω=exp(2πi/21). For a primitive character k (gcd(k,21)=1), the three-by-three
Hermitian Fourier block of A has real diagonal

    λ_i = ω^(k s_i)+ω^(−k s_i) = 2 cos(2πk s_i/21)

and offdiagonal entries z12,z13,z23 (with conjugates below the diagonal).
Each z_ij is the sum of the three character values on that cross-offset set.
The offdiagonal blocks of A² are all-ones, so their nontrivial Fourier
coefficients vanish. Hence

    (λ1+λ2) z12 = −z13 conjugate(z23),
    (λ1+λ3) z13 = −z12 z23,
    (λ2+λ3) z23 = −conjugate(z12) z13.

Every z_ij is nonzero. Three complex numbers of modulus1 summing to zero
form an equilateral triple: after division by one of them, |1+u|=1 forces
Re(u)=−1/2, and the third is the conjugate nontrivial cube root. Since k is
coprime to21, a vanishing z_ij therefore forces the offset set to be a coset
of {0,7,14}. Vertices with first-orbit residues0and7 would then have the same
three neighbors in the second orbit, violating C4-freeness.

Multiply each equation by the conjugate of its left-side z. The right sides
are either −z12 z23 conjugate(z13) or its conjugate. The left sides are real,
so all three are equal:

    (λ1+λ2)|z12|² = (λ1+λ3)|z13|² = (λ2+λ3)|z23|².

Since the squared moduli are positive, the three pair sums λ_i+λ_j must all
have the same sign (unless zero; the next step excludes zero).

## 3. Exact finite sign contradiction

For each i let r_i=min(k s_i mod21,21−(k s_i mod21)), an integer from1to10.
The cosine is unchanged by this folding. The identity

    cos(2πr_i/21)+cos(2πr_j/21)
      = 2 cos(π(r_i+r_j)/21) cos(π(r_i−r_j)/21)

has a strictly positive second factor since |r_i−r_j|≤9. The first factor
is positive exactly when r_i+r_j≤10 and negative exactly when r_i+r_j≥11;
it is never zero because21/2 is not an integer.

The120 distinct triples from {1,…,10} are checked by check.py. The primitive
characters up to sign are k∈{1,2,4,5,8,10}. For EVERY triple, results.json
records one such k for which the three pair sums have mixed signs, contradicting
the necessary Fourier equations. This check is entirely integer arithmetic,
with no floating point, graph enumeration, time cap, or solver verdict.

Therefore no graph in the specified N63/m21/minimum-degree8 class exists,
subject to verification of the paper reduction and finite certificate.
Together with the elementary m63 circulant obstruction, this would show that
neither of the operator-specified second-control action orders can work.
It does not exclude the known N63 affine graph with other cyclic actions, any
q9 class, or the global Erdős85 problem; it is not a Lean proof.
