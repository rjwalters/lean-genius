# H5/H7 monic integer spectral controls — 2026-09-10

Owner: codex-sol-3. Passed independent arithmetic review1624 by codex-sol-2. The two explicit
polynomials below pass the listed necessary scalar conditions. They are not
simultaneous integer C/D representations or graph witnesses. No full H5 or
H7 profile is excluded or asserted realizable.

## Exact polynomials

For H5, take

    psi5=(x-3)^2(x+3)^2(x²-6)^8(x²-3)^2
         (x²+x-7)^4(x²+x-4)^2(x²+x-3).

For H7, take

    psi7=(x²-x-5)(x²-7)^5(x²-6)^2(x²-3)
         (x²+x-7)^3(x²+x-5)^3(x²+x-3)^2.

| quantity | H5 | H7/T0 |
| --- | --- | --- |
| residual degree | 38 | 34 |
| low triangles T from p3 | 19 | 13 |
| mixed overlap R from p5 | 16 | 30 |
| p1 | -7 | -7 |
| p2 | 229 | 203 |
| p3 | -124 | -118 |
| p4 | 1573 | 1379 |
| p5 | -1387 | -1267 |
| p6 | 11908 | 10190 |
| tr(D³) | 18 | 156 |
| implied defect triangles | 3 | 26 |
| local R upper bounds | 246,242,238 for T0,T1,T2 | 192 |

Both examples have the exact strict squared root windows in the current
[worksheet](Q7_H5_H7_SQUEEZE_20260910.md). Every displayed factor is monic,
integral and degree at most two; all roots are real. The adjacent verifier
checks exact radical inequalities, so discovery rounding is not evidence.

## Verified necessary conditions

The self-contained polynomial verifier checks:

- degrees and the first six residual power sums;
- the local overlap envelope for every listed incidence profile, even R,
  and R=3T+h+4 modulo5;
- the complete finite reduced Bass polynomial is a square modulo4, using
  (1-u²)H5 for H5 and H7 for H7;
- psi5(8)=0 modulo13 and psi7(3)=0 modulo5;
- the nonzero constant term is divisible by7^(h-1), separately from
  x^(h-1) dividing psi modulo7;
- the H5 weighted-projector condition psi5(a)=4bS(b) modulo8, where
  a²-7a+5=0, b=7-a and psi5=(x²+x+1)S² modulo2;
- every mixed trace tr(C^i D^j) for 0<=i,j<=8 is nonnegative, via exact
  companion matrices for the residual factors plus the fixed quotient and
  h-1 zero-C modes with D=-1;
- tr(D³)=15876-790h-p6 is a nonnegative multiple of6;
- primitive oriented nonbacktracking counts for the full A through length20
  are nonnegative even integers. Counts at lengths1..4 are (0,0,78,0) for
  H5 and (0,0,82,0) for H7.

The full-A Bass calculation uses H_h times the residual Bass factor,
(1+6u²+42u⁴)^(h-1), and (1-u²)^((245+h)/2). In particular the exponent is
125 for H5 and126 for H7. The extra (1-u²) in the reduced H5 parity test is
not counted twice in the full-A calculation.

## Scope and bounded discovery

Discovery used a fixed degree-one/two catalog with24 factors for H5 and21
for H7, an8-row parity system, and integer multiplicities. Each optimizer
call had a3-second limit. Two H5 objectives were tried: the first missed
weighted parity and the second supplied psi5. One H7 call supplied psi7.
No graph/SAT/certificate/cloud run, arbitrary-degree spectrum enumeration,
or infeasibility claim is part of this diagnostic. The retained verifier
has no SciPy dependency and checks the two fixed products directly.

The examples show that the listed scalar constraints, including the new
sixth-moment bound and H5 weighted parity, do not by themselves exclude
these sectors. The actual residual lattice determinant and invariant kernel
subspace have not been represented by a common symmetric integer operator.
Polynomial divisibility modulo7 does not construct that subspace. No
assignment of vertex-local spectral weights to these new polynomials has
been checked; the earlier rational seven-node local measure is a separate
example. Off-diagonal projectors, 0/1 entries, and support incidences remain
necessary joint conditions. Nothing here covers mixed traces outside the
finite rectangle or primitive counts beyond20.
