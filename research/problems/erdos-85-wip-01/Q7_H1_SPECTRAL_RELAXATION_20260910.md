# H1: an explicit spectral relaxation passing the current scalar filters

2026-09-10, codex-sol-1. Independent review #1602 PASS (codex-sol-2): exact verifier rerun and independent factor recurrence/mixed-fifth check; paper scope and Bass recurrence inspected. This is a fully specified monic integer polynomial with verified real roots and listed arithmetic properties. It is **not** an adjacency matrix, a joint integer C/D representation, or a C4-free graph. It does not decide the H1 sector or Erdős85.

## Polynomial

```
psi(x)=(x+3)(x+1)(x²-2x-4)^2
       (x²-8)^3(x²-7)^3(x²-6)^6(x²-5)^2
       (x²+x-7)(x²+x-5)^4(x²+2x-1).
```

The degree is46. Every root lambda satisfies the strict H1 interval
(7-sqrt45)/2 < lambda² < (17+sqrt45)/2. The first five power sums are
-7,281,-64,1961,-507, corresponding to43 all-low triangles and47 total triangles under the fixed H1 identities.

The exact verifier confirms all of the following:

- the complete reduced mixed-degree Ihara polynomial is a square modulo4 in the required formal-series sense;
- x²+x+1 divides psi modulo16;
- psi(1)=0 modulo5;
- the mixed fifth quantity R=p5+3847-72T is244, below the local bound510 at T=43;
- the oriented primitive nonbacktracking counts through length20 are nonnegative even integers, with lengths1..4 equal to0,0,94,0.

No claim is made about primitive-count nonnegativity at every length. The mod4 square-series gate is checked for the full finite reduced polynomial, not merely a prefix.

## How it was obtained and independently checked

A bounded diagnostic first listed all6 linear and28 irreducible quadratic integer factors in the strict root window. Integer multiplicities were searched using moment constraints and necessary arithmetic conditions. That search is not complete for arbitrary degree46 polynomials and supplies no exclusion evidence.

The deliverable is the explicit polynomial above. `verify_q7_h1_spectral_relaxation.py` independently reconstructs it and checks every reported property using exact integer/radical arithmetic, without SciPy, optimizer output, numerical root approximations, or the search's parity encoding. Its JSON includes the full coefficients and the finite primitive-count list. Thus validity of this one relaxation does not depend on trusting the search procedure.

## Consequence and remaining work

The listed scalar conditions do not by themselves exclude H1: this polynomial satisfies them. A next rejection must use an additional condition, such as a joint integer matrix/lattice realization, a compressed spectral form, stronger local-state constraints, or a primitive-cycle condition beyond the tested prefix. The polynomial has not passed those untested conditions. Conversely, failure of any further test would reject this relaxation alone, not every H1 candidate.
