# Odd-power congruence rejects the q16 unpaired spectrum

Date: 2026-09-06. Node: A-REG-NONBIP / NONBIP-CONNECTED.

**The formal spectrum in squad #40388 cannot be the spectrum of an integer
symmetric regular matrix with zero diagonal.** This excludes that specific
control; it does not exclude every candidate graph or close A-REG. The
argument below is an exact prose proof with an executable verifier, not a
Lean theorem.

## Necessary congruence

For any symmetric integer matrix B with even diagonal,

    tr(B²) ≡ sum_ij B_ij − tr(B)  (mod 4).

Indeed, each diagonal square vanishes modulo four, and each off-diagonal
pair contributes 2b² ≡ 2b modulo four.

Let A be an integer symmetric matrix with zero diagonal and constant row
sum q, of order n. For any positive odd m=2r+1, the diagonal entries of
A^m are even: each is vᵀAv with v=A^r e_i, whose off-diagonal summands
pair and whose diagonal summands vanish. Also A^m has row sum q^m.
Applying the preceding identity gives

    tr(A^(2m)) + tr(A^m) ≡ n q^m  (mod 4).              (1)

No C4-freeness, connectedness, nonnegativity, or evenness of q is needed
for (1). In particular, every regular simple graph satisfies it.

## Classical provenance in the graph case

This graph obstruction is a specialization of Harary and Schwenk,
[The spectral approach to determining the number of walks in a graph](https://msp.org/pjm/1979/80-2/pjm-v80-n2-p15-s.pdf),
Pacific Journal of Mathematics 80(2), 443–449 (1979), Corollary 5a,
page 448. Burnside counting of closed walks under rotation and reversal
gives, for walk length N>=3,

    sum_(d|N) phi(N/d) tr(A^d) ≡ 0                         (mod 2N), N odd;
    sum_(d|N) phi(N/d) tr(A^d) + (N/2) 1ᵀA^(N/2)1 ≡ 0   (mod 2N), N even.

Here phi is Euler's totient. For N=6 in a q-regular graph, this becomes

    2 tr(A) + 2 tr(A²) + tr(A³) + tr(A⁶) + 3nq³ ≡ 0 (mod 12).

Since tr(A)=0 and nq=tr(A²) is even, reduction modulo four recovers
the m=3 case of (1). Thus the candidate rejection below is an application
of a classical graph invariant, not a new invariant class. The direct
matrix proof above additionally covers signed integer weights.

## The candidate and its rejection

The q16 unpaired control was

    p_A = (x−16)(x+4)^4(x−2)(x+1)^2 ∏(x²−a)^c,
    (a,c) = (2,2),(10,3),(12,1),(14,92),(18,1),
            (21,22),(22,1),(23,1),(26,1).

Its first six moments are exactly

    0, 4096, 3846, 126976, 1044510, 17807980.

For m=3, n=256, q=16, the left side of (1) minus its right side is

    17807980 + 3846 − 256·16³ = 16763250 ≡ 2 (mod 4).

This contradicts (1). Its prior passes on the minimal-polynomial Hoffman
test, low moments, and characteristic-polynomial parity were insufficient
for realization. The local interlacer search ending UNKNOWN neither proved
nor refuted this spectrum; the present global congruence now refutes it.

An independent calculation uses D=15I+J−A² and B=AD. Its diagonal is even
because diag(AD)=16−diag(A³). The proposed spectral data give

    tr(D³)=6036,
    tr(AD)=250,
    tr((AD)²)=15·3840+256·15²−6036=109164,
    sum_ij (AD)_ij=256·16·15=61440.

Thus 109164−61440+250=47974 ≡ 2 modulo four, the same obstruction.
These AD identities use the proposed square-order defect relation; the
direct A³ argument avoids that extra structure entirely.

Equivalently, in any even-q square-order C4-free instance, A and its defect
graph D have the same parity of triangle counts. Indeed,

    tr(A⁶) = q⁶ + q²(q−1)²(q+2) − tr(D³).

The polynomial terms vanish modulo four, so (1) says
tr(A³) ≡ tr(D³) modulo four. Dividing their values 6T_A and 6T_D shows
T_A ≡ T_D modulo two. Here T_A=641 is odd and T_D=1006 is even.
This reformulation, independently observed by Sol1, does not need D
connected and is the same obstruction rather than a separate filter.

## Verification and scope

Run `python3 research/problems/erdos-85-wip-01/verify_nonbip_connected_odd_power_mod4.py`.
It verifies the factor ledger, both rejection calculations, and actual
q4/H36 graphs plus a triangle and a single edge at odd powers 1,3,5,7.
The latter controls check that disconnected defect, odd graph order, and
odd degree are not inadvertently excluded.

The older Capell completion was separately excluded by Hoffman divisibility
in `ceea46101f`. Neither exclusion supplies a classification of all possible
spectra. The missing link remains a uniform obstruction for arbitrary
binary-square regular C4-free graphs, not another test of these two ledgers.
