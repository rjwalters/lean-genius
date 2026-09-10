# Five exact H7 local seventh-moment cuts — 2026-09-10

Owner: codex-sol-3. Independent review pending.

For the fixed polynomial from the reviewed H7 integer control,

    psi7 = (x²-x-5)(x²-7)^5(x²-6)^2(x²-3)
           (x²+x-7)^3(x²+x-5)^3(x²+x-3)^2,

five local configurations are impossible. This does not exclude the
polynomial, the H7 support profile, or a graph sector. The local target
identifications remain paper-level graph identities; the retained verifier
checks exact arithmetic certificates and is not a Lean formalization.

Here t is high-neighbor count, tau is all-low triangle count at the vertex,
R=(CD²)vv and delta=(D³)vv/2. The exact rational bounds in the JSON imply:

| (t,tau,R,delta) | Strict interval for (C⁷)vv |
|---|---|
| (0,2,4,1) | (8212,8214) |
| (0,2,4,7) | (8226,8228) |
| (0,3,4,3) | (8440,8442) |
| (1,2,0,5) | (5712,5714) |
| (1,2,2,6) | (5750,5752) |

For a symmetric integral zero-diagonal matrix C, every odd diagonal
(C^(2j+1))vv is even: put a=C^j e_v and pair the off-diagonal terms of
a' C a. Thus no value in any displayed interval is possible.

## Exact dual argument

Use the local targets from [the H7 Galois measure](Q7_H7_GALOIS_LOCAL_MEASURE_20260910.md):

    Q=[[7,7],[-1,0]], G=[[42,56],[56,98]],
    qk=[1,t] Q^k G^-1 [1,t]', z=t(7-t)/49,
    m0=1-q0-z, m1=-q1, m2=7-t-q2,
    m3=2tau-q3, m4=(7-t)(13-t)-7-q4,
    m5=R+12m3-36m1-q3+2q2-q1,
    m6=216m0-108m2+18m4+q3-3q2+3q1-q0-z-2delta.

At every residual root lambda the spectral projector diagonal weight
w_lambda is nonnegative. The JSON supplies two rational vectors y0,...,y6,
one for each sign epsilon=1,-1, such that

    epsilon*lambda^7 - sum_j yj*lambda^j >= 0.

Multiplying by the nonnegative weights and summing gives
epsilon*m7 >= sum_j yj*mj. Since (C⁷)vv=q7+m7, the two vectors yield the
lower and upper bounds recorded exactly in the JSON. This argument allows
all nonnegative root weights; it does not restrict them to an inner cone.

The verifier reduces each dual slack polynomial modulo every distinct
quadratic x²+b*x+c. The remainder is A*x+B and its values at the two roots
are center ± A*sqrt(b²-4c)/2, where center=B-A*b/2. Both are nonnegative
exactly when center>=0 and center²>=A²*(b²-4c)/4. These are rational checks.
The verifier rebuilds the local targets and checks both strict interval
endpoints without floating point or an optimizer.

## Discovery and limits

A bounded numerical LP screen tested all315 allowed (t,tau,R,delta) types
with t in0..2. Of these,96 admitted numerical measures through degree6;
five had numerical seventh-moment intervals containing no even integer.
Their dual vectors were rationalized, shifted conservatively in the
constant coefficient, and verified exactly. Numerical infeasibility for
the remaining types is not retained as an exclusion certificate.

The earlier exact H7 measure claims moments only through degree6. Its
particular weights fail degree7 integrality, which rejects those weights
as full integer matrix data but does not reject alternative weights.
None of the five newly excluded types occurs in its saved census. This
artifact therefore supplies necessary local cuts, not a contradiction
for the fixed polynomial or its global allocation.

Run `python3 verify_q7_h7_seventh_local_cuts.py` beside the JSON.
