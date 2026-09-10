# Local C4-sensitive defect-overlap bound — 2026-09-10

Owner: codex-sol-3. **Paper proof and finite arithmetic passed independent review1603 by codex-sol-1.** Scope: the
three H5 profiles and remaining H7/T0. This supplies a bound on R=tr(CD²)
and excludes T=4 in H5/T2. It does not exclude a full H5/H7 profile.

## Local isolation

Use the actual low adjacency C, defect graph D, support count t, and number
tau_v of all-low triangles through v from the reviewed q7 setup. Put

    L_v=N_C(v) intersect N_D(v),
    k_v=|L_v|=7-2t_v-2tau_v,   deg_D(v)=6-t_v.

Every vertex of L_v is isolated in C[N_D(v)]. Indeed, if w lies in L_v
and u lies in N_D(v), an edge uw of C would make w a common neighbor of
v and u. This contradicts the defining no-common-neighbor condition of Dvu.
Thus all edges of C[N_D(v)] lie on the remaining

    m_v=(6-t_v)-k_v=t_v+2tau_v-1

vertices. This induced graph is C4-free, as a subgraph of the actual graph.
The reviewed local-state bounds give m_v between0 and5.

The maximal edge counts for C4-free simple graphs of orders0,...,5 are

    e_max=(0,0,1,3,4,6).

For the only less immediate upper bounds: at order4 maximum degree<=2
gives at most4 edges, while a degree3 vertex has a matching among its
neighbors and hence at most4 total edges. At order5 maximum degree<=2
gives at most5 edges. A degree3 vertex has at most one edge among its
three neighbors and the sole remaining vertex has at most one neighbor
there, giving at most5 edges. A degree4 vertex leaves a matching on four
neighbors, giving at most6 edges. Triangle-with-pendant and two triangles
sharing a vertex attain the order4 and order5 bounds respectively.

The general mixed-word identity, already formalized in
`Erdos85RootedFifthWalkDefectNeighborhood.lean`, gives

    R=tr(CD²)=2 sum_v e_C(N_D(v))
      <=2 sum_v e_max(t_v+2tau_v-1).                  (1)

The possible local terms are:

| t | tau | m | upper bound for local edges |
| --- | --- | --- | --- |
| 0 | 1,2,3 | 1,3,5 | 0,3,6 |
| 1 | 0,1,2 | 0,2,4 | 0,1,4 |
| 2 | 0,1 | 1,3 | 0,3 |
| 3 | 0 | 2 | 1 |

This uses C4-sensitive local information missing from the old standalone
R-mod5 audit. No independence from every prior local theorem is claimed.

## Census bounds and Newton congruences

Impose each fixed support census and sum tau_v=3T. A finite dynamic program
maximizes the right side of(1) over these integer local states. This gives
a necessary upper bound; it does not assert simultaneous graph realization
of local maximizing states.

For H7/T0, whose census is(7,14,21,0), the exact local-state maximum is

    R <=18T-42-4 max(0,ceil((3T-42)/2)),   3<=T<=23.  (2)

The seven empty vertices consume seven triangle incidences at zero edge
score. Additional incidences on empty/pair vertices earn three edges each,
up to35 such incidences. Beyond that, singletons incur an edge-score loss
of two for each singleton with positive triangle count; the fewest needed
is ceil((3T-42)/2). This gives(2), and those allocations attain the stated
local-state maximum. The verifier independently computes every DP value.

For H5 the three exact upper-bound tables are recorded in the adjacent JSON.
Their triangle ranges before the new congruence check are5..30,5..30,4..30.

For clarity, the fifth-moment input is derived for the actual nonregular
graph, not imported from a regular graph. With full adjacency A and full D
(zero on highs), the general fifth-trace expansion from the prior audit is

    tr(A^5)=2 sum d_v(d_v-1)+2n|E|-2tr(AKD)-2d^TD1+tr(AD²),
    K=diag(d_v-1).

Here n=49, |E|=(343+h)/2, tr(AD)=343-23h-6T,
tr(AKD)=6tr(AD), and d^TD1=7(294-14h). Substitution gives
tr(A^5)=12691+549h+72T+R. The paired ±sqrt7 sectors cancel in this odd
moment, and the forced cubic contributes16807+280h. Thus the residual
fifth power sum is R+72T+269h-4116.

Newton's fifth identity, with the already-known first four residual moments,
gives the next coefficient of the monic integral psi:

    h5: c5=(-R+828T+150709)/5,
    h7: c5=(-R+698T+116991)/5.

Consequently R=3T+4 modulo5 for H5 and R=3T+1 modulo5 for H7. Also R is
nonnegative and even by its edge-count interpretation.

## H5/T2 with T=4 is impossible

This profile has census(12,26,4,2). The twelve empty vertices already
require12 triangle incidences. If T=4, they each have tau=1 and every
other vertex has tau=0. The local table then gives zero edge contribution
except possibly at the two triple-support vertices, each contributing at
most one. Hence0<=R<=4. But R must be even and R=3*4+4=1 modulo5;
none of0,2,4 satisfies that. Thus T>=5 for H5/T2.

No other triangle value in the inspected H5/H7 ranges is excluded solely
by this DP bound, nonnegativity, parity, and the fifth Newton congruence.
In particular no H7/T0 triangle value is excluded. The bounded next question
is whether the new R interval helps the existing residual moment/count test;
it is not a completed spectrum exclusion.

## Verification

`verify_q7_local_defect_overlap_bound.py` checks all labeled simple graphs
through order5 to verify the small extremal numbers, all nine local states,
every census DP value, the H7 closed form, and the exact Newton coefficients.
It records allowed even Newton residue ranges as arithmetic progressions.
This is exact finite arithmetic supporting the paper graph-to-local bound,
not a Lean formalization or a q7 graph search.
