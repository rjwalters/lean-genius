# Universal H3 support-edge ledger

The H3 pair profile forces its empty-support induced graph to have53 or54 edges. The triple profile forces49. These are consequences of the established q7 identities C1=7*1-t, Ct=3*1 and the H3 support census; no choice of residual spectrum is made. This note records the algebra explicitly, without claiming a full-profile exclusion or a new Lean graph bridge.

Let C be the low induced adjacency matrix. Write E for vertices with t=0 and S for t=1. Edge counts eij below are undirected, with internal edges counted once. Since Ct=3 and t is nonnegative, every low vertex has at most one neighbor of support at least2.

## Pair profile

There are25 empty,18 single and3 pair-support vertices P, with t=0,1,2 respectively. Every vertex has at most one P-neighbor. In particular C[P] is a matching, so b=e22 is0 or1. Summing degree and support-weighted degree over the three classes yields

    2e00+e01+e02=175,    e01+2e11+e12=108,
    e02+e12+2e22=15,
    e01+2e02=75,         2e11+2e12=54,
    e12+4e22=9.

Their unique solution for fixed b is

    (e00,e01,e02,e11,e12,e22)
      =(53+b,63-4b,6+2b,18+4b,9-4b,b).

Pointwise, if nP(v) counts P-neighbors, then

    nE(v)=4-t(v)+nP(v),    nP(v) in {0,1}.

Therefore C[E] has degree distribution

    degree4: 19-2b vertices; degree5: 6+2b vertices.

The three pair vertices have pairwise disjoint C-neighborhoods: a common C-neighbor would have support sum at least4. Since each has C-degree5, their neighborhood union has15 vertices. Its intersections with E,S,P have sizes6+2b,9-4b,2b.

The indicator relation is 1_E=1-t+1_P. Consequently their residual projections, after removing span(1,t), coincide. Also C*1_E=4*1-t+C*1_P; the squared norm is691 in either b case. This is an exact support-derived moment, not a new spectral exclusion.

## Triple profile

There are24 empty,21 single and one triple-support vertex z. Since z has no loop, its C-neighbors have only supports0/1. The equations deg_C(z)=4 and (Ct)(z)=3 give three single neighbors and one empty neighbor. Thus e13=3 and e03=1. Summing Ct and degree over the other classes then gives

    (e00,e01,e03,e11,e13,e33)=(49,69,1,27,3,0).

Here 1_E=1-t+2*1_{z}, so

    C*1_E=4*1-t+2*C*1_z.

Exactly one empty vertex neighbors z. Therefore C[E] has one vertex of degree6 and23 vertices of degree4. The single class has three vertices with5 empty neighbors and18 with3; z has one empty neighbor. The squared norm of C*1_E is642.

## Verification and scope

`verify_q7_h3_support_edge_ledger.py` solves the six pair equations symbolically and checks the degree/count distributions and squared moments exactly. It checks the triple equations independently. The graph-to-equation reasoning is above; the script does not replace it with a graph theorem.

The induced empty-support graphs inherit C4-freeness. Their stated degree sequences and edge counts are necessary conditions only. This note neither constructs such induced graphs nor shows they extend to the complete order49 configuration. The ledger may be implicit in earlier support arguments; its contribution here is an explicit reusable constraint, not a claim of independent novelty.
