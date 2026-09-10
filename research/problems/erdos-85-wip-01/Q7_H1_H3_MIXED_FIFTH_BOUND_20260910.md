# H1/H3 local defect-neighborhood bound for the fifth moment

2026-09-10, codex-sol-2. Pending independent paper review. This extends
codex-sol-3's September10 defect-neighborhood isolation argument to H1/H3.
No graph, spectrum, connected-profile exclusion, or Lean graph proof is asserted.

## Local isolation and the mixed trace

Use the actual low adjacency C, missing-common-neighbor adjacency D, support
size t_v, and number tau_v of all-low triangles through v from the reviewed
Q7 block setup. Put R=tr(C D²). Its v contribution is twice the number of
C edges in the D neighborhood of v.

Every u in N_C(v) intersect N_D(v) is isolated in C[N_D(v)]: an edge u-w
with w in N_D(v) would make u a common C neighbor of v,w, contradicting
D_vw=1. Consequently the edges in this induced graph lie on at most

    (6-t_v) - (7-2t_v-2tau_v) = t_v+2tau_v-1

vertices. This count lies between0 and5 for the nine permitted local tuples.
The exact C4-free extremal edge counts for orders0..5 are0,0,1,3,4,6.
The verifier exhausts all labeled graphs at these orders (at most1024).
Thus each vertex contributes at most twice the corresponding table entry.
The induced graph is C4-free because C is C4-free. This is an upper bound;
local extremizers need not fit together into an actual graph.

## Additional prior H1 coupling: T is at least18

In H1 let N be the eight neighbors of the unique high vertex, and F the
remaining forty vertices. Every F vertex has exactly one N neighbor; N is
a matching. Thus an all-low triangle cannot contain two N vertices, and
sum of tau_v over N is precisely the number of internal matching edges in
the eight attachment branches. The prior five branch profiles give this
number between12 and16. See
`proofs/Proofs/Erdos85OneHighGlobalMissLabelCounting.lean`, especially
`card_oneHighAllMatchedVertices_eq_profile` and
`sum_two_mul_oneHighFamilyInternalEdges`; their parameter ranges0..4.
These formal statements use the branch-profile hypotheses, supplied by the
existing H1 classification. This note does not re-formalize that application.

Each of the forty empty-support vertices has tau_v>=1, by the prior
`Erdos85OrderFortyNineLowTriangles.lean` result. Therefore

    3T = sum_F tau_v + sum_N tau_v >=40+12=52,
    18<=T<=45.

This improves the14 lower bound in the current scalar worksheet by combining
existing facts. Neither the branch bound nor the empty-vertex lemma is new.

## Exact allocation envelope

`verify_q7_h1_h3_mixed_fifth.py` performs finite dynamic programming over the
nine permitted (t,tau) tuples, using the fixed support censuses. Its state
tracks total triangle incidences and singleton triangle incidences; the
objective is the sum of local upper bounds for R. For H1 it also imposes the
prior12..16 singleton-incidence count. Every actual graph provides a state,
but not every state is asserted realizable. The JSON records all upper bounds.

For H1 this gives

    R <=18T-264, for18<=T<=44;
    R <=538, forT=45.

Indeed the empty vertices contribute exactly the local upper envelope
6(sum_F tau-40). For singleton incidence sum u, the maximum singleton
contribution is8 floor(u/2)+2(u mod2), with12<=u<=16. Optimizing this expression
subject to40<=3T-u<=120 gives the displayed result.

The H3 pair and triple censuses are respectively(25,18,3,0) and(24,21,0,1).
Their tables retain T ranges9..38 and8..38. At their largest T, the upper
bounds on R are462 and458 respectively. No H1-specific branch constraint
is imposed on H3.

## Residual fifth-power-sum form

On K, D=6I-C². The two fixed C eigenvalues a,b satisfy a+b=7,ab=h;
the corresponding D eigenvalues are a-1,b-1. The other fixed C eigenvalues
are zero. Hence, writing p_j for residual power sums,

    R = (252-17h) +36p1-12p3+p5
      = p5+4116-269h-72T.

Thus every table entry imposes

    72T-4116+269h <=p5<=72T-4116+269h+R_upper(T).

The lower bound uses nonnegativity of R. The evenness of R also follows
from its edge-count interpretation. The derivation is paper algebra; the
verifier certifies the small extremal tables and finite allocation only.
No residual polynomial enumeration or solver run is part of this artifact.

## Explicit H1 spectral relaxation survives

Sol1 supplied a degree46 product of linear/quadratic factors in the squad
on September10 (message42824). The verifier records those exact factors and
independently computes their first five power sums by integer recurrences:
(-7,281,-64,1961,-507). Thus T=43 and R=244, below the510 upper bound.
This test does not eliminate that spectral relaxation. This artifact verifies
only its power sums and the mixed bound, not every other claimed filter or
any graph realization.
