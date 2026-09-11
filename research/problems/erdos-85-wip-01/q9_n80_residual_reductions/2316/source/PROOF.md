# Exclusion of residual orbit degrees (1,2,2,2,3)

Assume the N80/F10 cubic-fixed branch with the displayed residual degrees. Use accepted2251/2297 for the attached patterns, defect identities and exact two-step budget. This proof does not depend on the pending two-cubic-orbit exclusions.

The identities give total attached deficit five and e_E(R,W)=4n_311-6. Thus n_311>=2, while the deficit bounds it by two. There are exactly two311 groups, centered at h,j, and one211 group centered at p. All other groups are111. There are four high vertices of residual degree three and two of residual degree two.

## High degree-three vertices and their fixed defect targets

A degree-three attached vertex cannot meet a cubic residual vertex. In the exact budget

 sum over residual neighbors r of (d_R(r)-1)
 + sum over attached neighbors w of (k(w)-1) <=2,

a cubic neighbor uses the whole budget and would force the other two neighbors to be leaves from distinct involution orbits. There is only one leaf orbit. Therefore every degree-three attached vertex meets the leaf orbit and two degree-two orbits. Its support-degree sum is five, exhausting the budget. All five of its W-neighbors have residual degree one, and its residual defect degree is10-5-5=0.

For clarity, the fixed-target bookkeeping used below follows directly from missing slots. An attached vertex of residual degree k has8-k neighbors in W out of seven possible slots: its own group and the six groups not adjacent to its center in H. Each occupied slot gives its unique common neighbor with that fixed center; each absent slot gives a fixed E-target. It has exactly k-1 fixed E-targets. Low vertices have none. All targets are exceptional centers, since an ordinary center has zero E-neighbors in W. Cross-slot absences are reciprocal between equal-size groups, and the involution pairs them. Thus on the exceptional centers h,j,p the high-orbit target matrix Z is binary symmetric, including possible diagonal entries, with row degrees2,2,1. A cross entry requires the corresponding centers not to be adjacent in H.

There are exactly two forms, up to interchanging h,j:

 (I) Z_hh=Z_hj=Z_jh=Z_jj=Z_pp=1;
 (II) Z_hj=Z_jh=Z_hp=Z_ph=Z_jj=1.

To see completeness, either p has its loop, forcing the other two rows to contain their loops and mutual edge, or p has exactly one cross edge, say to h. The degree-two row j must then use its loop and edge to h; h has its two cross edges.

## Summed commutation forces form I and one adjacency

Let Y_f be the missed residual orbits of a fixed center f. Put delta_f=2-|Y_f|, so delta_h=delta_j=2, delta_p=1, and other deltas zero. Define q_f=e_E(B_f,R)/2, a nonnegative integer, because the involution pairs these edges. Since e_E(W,R)=2, sum_f q_f=1.

Summing ME=EM at (f,r) over one representative of each residual orbit gives

 q_f = sum over s in Y_f of d_s
       + sum over high orbits targeting f of their residual degree
       - (6 - sum over g adjacent to f in H of delta_g).

Indeed the left side before rearrangement is HY plus the B_f-to-R defect sum; the right side is YQ plus the targeted attached incidences. Each paired high orbit of degree k contributes k after summing over residual representatives.

In form II, h receives one degree-three and one degree-two high orbit. It misses no residual orbit and is H-nonadjacent to both other exceptional centers. The formula gives q_h=5-6=-1, impossible.

In form I, h and j are H-nonadjacent. Let k be the number of H-adjacencies from p to {h,j}, and let d be the degree of p's unique missed residual orbit. Then

 q_h+q_j=k,
 q_p=d-4+2k.

Since d<=3, nonnegativity of q_p requires k>=1. Since the total q is one, k<=1. Hence k=1, and q_p=d-2 with total q at least d-1. This forces d=2, q_p=0, and all ordinary q values zero. Relabel so p is adjacent to h. All two W-to-R defect edges lie in B_h.

Neither high vertex of B_h has a residual defect. Its two low orbits meet the remaining degree-two orbit and the cubic orbit. A low vertex meeting a cubic vertex has only low W-neighbors by the exact budget and has residual defect degree10-7-3=0. Thus precisely the two low vertices meeting the degree-two orbit in B_h have residual defect degree one. Every other low vertex in W has residual defect degree zero.

## The211 group and the final capacity contradiction

The two degree-two high vertices in B_p have self as their fixed E-target, so are internally unmatched. They cannot neighbor either degree-three high orbit, whose vertices have only low W-neighbors. They cannot neighbor each other, since they are in B_p and the internal slot is absent. Hence all six W-neighbors of each are low. Since q_p=0, their residual support-degree sum is10-6=4. They therefore meet either two degree-two orbits, or the leaf and cubic orbits.

The latter alternative is impossible. Since B_p misses a degree-two orbit, its two low orbits would then meet the other two degree-two orbits. Every such low vertex u has zero residual defect and a degree-two residual neighbor. Counting endpoints gives

 10=7+sum over w in N(u) intersect W of (k(w)-1)+2.

The excess sum is one, so u needs a degree-two W-neighbor. Both available degree-two attached vertices lie in B_p and are internally unmatched, so neither can neighbor u. A degree-three neighbor cannot supply an excess of one. This is a contradiction. Therefore the high vertices in B_p meet two degree-two residual orbits.

Across the six degree-two residual vertices there are42 incidences with W, since each has seven attached neighbors. The four degree-three high vertices contribute eight of these incidences, and the two degree-two high vertices contribute four. The remaining thirty incidences belong to thirty low attached vertices. Exactly two of those have residual defect degree one, as shown above. Each of the other twenty-eight has zero residual defect and therefore needs exactly one degree-two W-neighbor by the same endpoint equation.

This requires at least twenty-eight edges to the two degree-two attached vertices. Each has only six W-neighbors, so together they can support at most twelve such edges. Contradiction.

Hence residual orbit degrees (1,2,2,2,3) are impossible. This is a paper exclusion with no finite enumeration, graph solver, capped-search premise or Lean formalization. Other residual patterns remain open.
