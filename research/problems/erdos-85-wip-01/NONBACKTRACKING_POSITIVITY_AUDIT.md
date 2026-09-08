# Primitive nonbacktracking positivity adds no square-order exclusion

2026-09-08, Sol3, divergence #109, A-REG-NONBIP.
Independently reviewed by Sol1 (#1476 PASS). Uniform prose argument, not
Lean-checked. This audits a proposed filter;
it neither constructs a graph nor excludes all candidate spectra.

## Exact scope

Let q>=8 be an even integer, n=q^2, s=q-1. Consider real spectral data consisting
of one principal value q and n-1 residual values lambda_i with

    |lambda_i| <= sqrt(2s).

Assume the adjacency moments a_j (including the principal value) satisfy

    a_1=0, a_2=nq, a_4=nq(2q-1), 0<=a_3<=nq.

These are necessary for a simple q-regular C4-free graph on q^2 vertices.
The residual bound follows from A^2=sI+J-D on the orthogonal complement
of the all-ones vector and the (q-1)-regular defect graph D. The upper bound
on a_3 follows because each neighborhood induces a matching. The argument
below requires neither a realization nor an integer characteristic polynomial.

For these spectral data define the formal Hashimoto traces T_l by the
Ihara-Bass formula, and define

    C_l = (1/(2l)) sum_(j|l) mu(l/j) T_j.

For an actual simple undirected graph, C_l counts primitive, cyclically
nonbacktracking closed walks up to rotation and reversal. These walks may
repeat vertices; they are not restricted to simple cycles. The condition
of no immediate reversal also applies across the cyclic seam.
Reversal acts freely on the primitive cyclic classes: a reflection fixing
a class would force either a self-inverse directed edge or an immediate
backtrack. This accounts for the factor two.

**Result:** every such spectral datum already has C_1=C_2=C_4=0,
C_3>=0, and C_l>0 for all l>=5. Thus nonnegativity of these formal counts,
even at every length, cannot strengthen these existing A-REG relaxations.
Their **integrality** is a different condition and is not proved automatic.

## Trace formula and bounds

See Rangarajan, [A Combinatorial Proof of Ihara-Bass's Formula for the Zeta
Function of Regular Graphs](https://doi.org/10.4230/LIPIcs.FSTTCS.2017.46).
For a q-regular graph with m=nq/2 edges, its Hashimoto spectrum consists of
the two roots of z^2-lambda*z+s for each adjacency eigenvalue lambda,
together with m-n extra copies of each of +1 and -1. The same algebraic
list defines our formal traces without assuming a graph exists.

The principal roots are s and 1. Each residual pair has modulus sqrt(s),
since |lambda_i|<=sqrt(2s)<2sqrt(s). There are nq roots in total, all of
modulus at most s. The extra +1/-1 pairs contribute nonnegatively to each
trace. Consequently, for l>=1,

    T_l >= s^l - 2(n-1)s^(l/2),
    |T_l| <= nq s^l.                                      (1)

One can compute the same traces without complex roots: set
P_0(x)=2, P_1(x)=x, P_l(x)=xP_(l-1)(x)-sP_(l-2)(x). Then

    T_l = sum_i P_l(lambda_i) + (m-n)(1+(-1)^l),

where this sum includes lambda_0=q. The stated moments give
T_1=T_2=T_4=0 and T_3=a_3. This settles lengths 1 through 4.

## Lengths five and six

For length five the proper divisor trace is zero, so 10C_5=T_5.
For s>=7,

    2(n-1)/s^2 = 2+4/s <= 18/7 < sqrt(7) <= sqrt(s),

where (18/7)^2<7. Thus s^(5/2)>2(n-1), and (1) gives T_5>0.

For length six, 12C_6=T_6-T_3. By (1) and T_3<=nq,

    T_6-T_3 >= s^6-2(s^2+2s)s^3-(s+1)^3
             = s^4(s^2-2s-4)-(s+1)^3 > 0.

Indeed s^2-2s-4>=31 for s>=7, while (s+1)^3<= (8/7)^3 s^3<2s^3.

## All lengths at least seven

Write r=s^(l/2). Every proper divisor j of l is at most floor(l/2).
Using |mu|<=1 and (1), the numerator of C_l is at least

    T_l - sum_(j=1..floor(l/2)) |T_j|
      >= r^2 - 2(n-1)r - nq * (s/(s-1))r
       = r [r-2(n-1)-nq*s/(s-1)].                         (2)

For s>=7,

    2(n-1) = 2s^2+4s < 3s^2,
    nq*s/(s-1) = (s+1)^3*s/(s-1)
                <= (8/7)^3*(7/6)*s^3 < 2s^3.

Their sum is less than (17/7)s^3, whereas

    r >= s^(7/2) >= sqrt(7)s^3 > (17/7)s^3.

The last comparison is exact: 7>(17/7)^2. Hence (2) is positive at
every l>=7. This completes the all-length argument.

## Calibration, integrality, and decision

`verify_nonbacktracking_positivity_audit.py` independently forms the directed
edge transition matrix of the actual q4 control. Direct traces agree with
the spectral recurrence through length 12; the primitive counts at lengths
3..8 are 8,0,24,100,144,394. This checks formula conventions, including
the factor two for reversing orientations. q4 is a calibration outside
the q>=8 positivity theorem.

For the already-rejected q16 ledger in
`NONBIP_CONNECTED_ODD_POWER_MOD4_AUDIT.md`, counts at lengths 3..8 are

    641, 0, 75606, 2157713/2, 12200814, 159517689.

All counts through 20 are nonnegative; lengths 6 and 12 are nonintegral.
The existing length-six congruence already rejects this ledger, so the
half-integer at length six is not an independent new exclusion. We make
no assertion that all higher integrality tests follow from that one test.

**Decision:** stop the proposed primitive-cycle positivity filter. It is
uniformly automatic under the stated existing relaxations for q>=8.
Do not stop all spectral methods: primitive-cycle integrality, other
integer-matrix constraints, or entrywise realizability may still add
information. No classification of the surviving spectra or A-REG terminal
has been established here.
