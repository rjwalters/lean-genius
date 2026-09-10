# H1: an induced-block spectral relaxation survives interlacing

2026-09-10, codex-sol-1. Independent review #1606 PASS (codex-sol-2): private exact verifier rerun, independent factor moments and all81 Bass coefficients, and paper compression/scope check. This is an exact pair of integer polynomials, **not** a pair of simultaneously realized matrices or a graph. The first polynomial is the reviewed H1 residual psi in `Q7_H1_SPECTRAL_RELAXATION_20260910.md`, with T=43 all-low triangles.

## Necessary induced-block conditions

Partition the low vertices into the eight neighbors N of the high vertex and the forty empty-support vertices E. Then

    C = [[M,P],[P^t,F]],

where M is a matching, P has row sums5 and column sums1, and F is a6-regular C4-free graph on40 vertices. The two-dimensional space of vectors constant on N and E is invariant. Its orthogonal complement is the46-dimensional residual space K. On K, the E-sum-zero subspace has dimension39 and codimension7; compressing C to it gives F restricted to E-sum-zero. Therefore its eigenvalues beta, in increasing order, must satisfy

    alpha_i <= beta_i <= alpha_(i+7),  1<=i<=39,

where alpha are the roots of psi. This removes both quotient dimensions before interlacing and is stronger than merely deleting eight vertices in the full48-dimensional low block.

Write char(F)=(x-6)rho(x). The permitted local triangle count T_N is12..16, and triangles inside F number T_F=43-T_N. Thus rho has moments0..4

    (39,-6,204,6*T_F-216,1344).

Here tr(F^4)=40*6*(2*6-1)=2640 follows from regularity and C4-freeness. The regular even-degree Hoffman condition gives80 dividing rho(6). The Bass determinant is checked using degree correction5 and exponent m-n=80, not the mixed-degree correction for the original graph.

## Explicit second polynomial

At T_N=16 and T_F=27, take

    rho(x)=(x-3)x^2(x+1)^2(x^2-x-4)(x^2-8)
           (x^2-7)^5(x^2-6)^3(x^2-5)(x^2-3)
           (x^2+x-5)^2(x^2+2x-2)^3.

Its degree is39 and its first five moments, including degree, are
(39,-6,204,-54,1344). All39 exact radical comparisons in the rank7 interlacing inequalities pass. In addition,80 divides rho(6), the full finite Bass factor is a square modulo4, and oriented primitive nonbacktracking counts through length20 are nonnegative even integers. Lengths1..4 give0,0,54,0, corresponding to27 triangles and no4-cycles at the spectral level.

The self-contained verifier hardcodes both factor lists, reconstructs and orders exact algebraic roots, and checks all reported properties without the optimizer or its output. The JSON includes full rho coefficients and primitive counts. Discovery searched only linear and quadratic factors; it was not a complete search over degree39 polynomials.

## Scope

These necessary induced-block spectral tests still do not reject the supplied H1 residual. Neither interlacing nor the arithmetic tests constructs the coupling P, the matching M, an integer F, or simultaneous C and D. Additional matrix constraints, or a stronger graph argument, remain necessary. No full H1 profile exclusion follows in either direction.
