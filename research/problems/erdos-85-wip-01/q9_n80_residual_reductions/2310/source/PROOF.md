# Two cubic residual orbits force independence of high attached vertices

Assume the N80/F10 cubic-fixed branch, no isolated residual vertex, and exactly two cubic residual involution orbits. Accepted2295/2297 give residual degrees1,2,3 and five free residual orbits. Write C for the four cubic residual vertices and L=R minus C for the six noncubic vertices. Every attached vertex u has residual degree k(u) in{1,2,3} and8-k(u) attached neighbors. Call k>=2 high.

The exact two-step inequality from2297 is

 sum over residual neighbors r of u of (d_R(r)-1)
 + sum over attached neighbors w of u of (k(w)-1) <=2.

Every summand is nonnegative. Thus an attached vertex meeting C has only degree-one attached neighbors. Equivalently, the residual supports of every W-neighbor of a high vertex lie in L. These supports are nonempty and pairwise disjoint, since a repeated residual endpoint produces a C4.

If k(v)=2, its six W-neighbors therefore have six nonempty disjoint supports inside L. Each support is a singleton and they cover L. In particular all six W-neighbors have k=1.

If k(v)=3, it has five W-neighbors. None can have k=2, by the preceding paragraph applied to that neighbor. If any had k=3, the five nonempty disjoint supports would have total size at least3+1+1+1+1=7, exceeding |L|=6. Hence all five also have k=1.

Consequently the high attached vertices form an independent set in G[W]. This restriction applies to11133 and11233 as well as the already excluded12233.

For k(v)=2 the six W-middle endpoints cover all of L. Therefore every residual neighbor r of v has all its residual neighbors in C; otherwise a second two-step walk to a covered endpoint gives a C4. Such an r cannot itself be cubic: on two free involution orbits, a vertex has at most its partner plus one vertex of the other orbit as neighbors. Two neighbors in that other orbit would, by involution symmetry, give the vertex and its partner two common neighbors. Hence k2 vertices meet only residual vertices of degree1 or2 whose residual neighborhoods lie wholly in C.

The defect entry E(v,r)=1-codegree(v,r) for v in W,r in R sums to10 minus the number of distinct two-step endpoints in R. Its fixed middle neighbor contributes zero. Thus for every high vertex v the number of residual defect neighbors is

 k(v)+2 - sum over r in N(v) intersect R of d_R(r).

This is4 minus the support-degree sum for k2 and5 minus that sum for k3. No zero-defect assumption is used. Distinct residual neighbors of an attached vertex lie in different involution orbits, since otherwise it and its involution partner would share two neighbors.

These are necessary structural restrictions, not exclusions of11133 or11233. No finite search, solver or Lean formalization is used.
