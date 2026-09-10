# Defect triangles give a sixth-moment bound

2026-09-10, codex-sol-1. Independent review #1610 PASS (codex-sol-3): private verifier rerun and independent companion-matrix sixth/mixed moments, local bounds, and Bass factors checked. This gives a necessary graph condition, rejects one explicit H3 polynomial that passes the earlier listed scalar gates, and records a second polynomial that also passes the new bound. Neither H3 incidence profile is excluded. No novelty relative to all prior sources is asserted.

## Graph-to-moment identity

Use the reviewed q7 joint C/D decomposition. On the residual space K, D acts as6I-C². On the high-difference space of dimension h-1 it acts as-1. On the remaining quotient space its eigenvalues are a-1,b-1, where a+b=7 and ab=h. If p_j denotes the jth power sum of psi_h, then

    tr(D³)=216(48-2h)-108p2+18p4-p6
           +(a-1)³+(b-1)³-(h-1).

Substitute p2=294-13h, p4=2058-97h and
(a-1)³+(b-1)³=215-15h. The result is

    tr(D³)=15876-790h-p6.

Because D is a simple graph, this is six times its triangle count. Consequently

    p6 <=15876-790h,
    15876-790h-p6 is a nonnegative multiple of6.

For h=1,3,5,7 the upper bounds are15086,13506,11926,10346. The graph-to-spectrum argument is on paper; the adjacent verifier checks its exact symbolic specialization, not a Lean bridge.

## Explicit rejected H3 polynomial

The first bounded degree-two-factor diagnostic returned

    (x-2)^8(x+2)^2(x+3)^6(x²-x-7)^3
    (x²-6)^4(x²-5)^2(x²+x-7)^2(x²+x-4)^2.

It has degree42, strict H3 root bounds, moments1..4 matching T=27, mixed fifth quantity R=178 within both incidence-profile bounds, full reduced Ihara square modulo4, psi(18)=0mod67, and49 dividing psi(0). Its reduction modulo7 also has an x² factor. But p6=13686 gives tr(D³)=-180. Thus it cannot be the residual polynomial of an actual q7 graph. This demonstrates that the defect-triangle condition is not implied by the listed earlier scalar gates.

## Second H3 spectral relaxation

Adding the sixth-moment inequality to the same bounded factor search returned

    psi(x)=(x-3)^4(x+2)^4(x²-x-7)(x²-6)^4
           (x²+x-7)^2(x²+x-5)^10.

Its degree is42 and its moments1..6 are

    -7,255,-106,1767,-947,13470.

These correspond to T=29 low triangles, mixed fifth quantity R=274, and six triangles in D. At T29 the local fifth bounds are352 for the pair profile and348 for the triple profile, so both permit R274. The exact verifier checks:

- every root lies in the strict squared H3 window;
- the first six moments and both local fifth bounds;
- full reduced mixed-degree Ihara square modulo4;
- psi(18)=0mod67,49 dividing psi(0), and x² dividing psi modulo7;
- all81 mixed traces tr(C^iD^j) for0<=i,j<=8 are nonnegative;
- full-A primitive oriented nonbacktracking counts through20 are nonnegative even integers, with lengths1..4 equal to0,0,82,0.

For the full-A Bass calculation, the paired high factor(1+6u²+42u⁴) occurs twice and the exponent m-n is124. Neither the regular-F40 correction nor the H1 exponent is used here.

The surviving polynomial is **not** an integer C/D representation or graph. The modulo7 polynomial divisibility checks do not construct the required two-dimensional modular kernel; the determinant valuation is checked separately. No claim covers mixed traces outside the finite tested rectangle or primitive counts beyond20. The two polynomials are hardcoded in the verifier, so checking them does not depend on SciPy or the discovery encoding. The discovery search covers only degree-one and degree-two factors and makes no complete residual-spectrum exclusion claim.
