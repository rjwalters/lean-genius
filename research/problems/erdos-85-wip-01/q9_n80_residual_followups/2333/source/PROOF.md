# Exclusion of residual orbit degrees (0,1,2,3,3)

Assume the N80/F10 cubic-fixed branch with displayed residual degrees. Let I be the isolated residual pair and C the four cubic residual vertices. Use the attached pattern and exact defect identities of accepted2251, and the exact endpoint budget

 sum over r in N(u) intersect R of (d_R(r)-1)
 + sum over w in N(u) intersect W of (k(w)-1) <=2.

## No degree-three attachments

If an attached vertex v had k(v)=3, every one of its five W-neighbors u would have a residual neighbor of degree zero or one. Otherwise its nonempty residual support contributes at least one to the first sum, while v contributes two to the second, a contradiction. The other W terms are nonnegative. There are only four residual vertices of degree zero or one. Residual supports of different W-neighbors of v are disjoint by C4-freeness, so five such nonempty supports are impossible. Thus n_311=0.

D=9 gives n_211+2n_221=6. Hence there are twelve high attached vertices, all with k=2; every other attached vertex is low with k=1. The exact identity gives

 e_E(W,R)=30+2[-3-4-3-3]=4.

## All residual defects meet the isolated pair

For r in I, let f be the unique fixed center whose attached group misses r. At (g,r), ME=EM reads

 1[g adjacent to f in H] + sum over u in B_g of E(u,r)
 = sum over u in N(r) intersect W of E(g,u).

The residual and fixed adjacency contributions on the right vanish because r is isolated in R and has no fixed neighbor. Summing over all fixed centers gives

 3+e_E(r,W) = number of high W-neighbors of r,

since low vertices have zero fixed defect targets and high vertices have one.

Put e_I=e_E(I,W), an even integer at most four by involution invariance. No attached vertex meets both members of I, because it and its involution partner would then have two common residual neighbors. Thus the eighteen distinct attached neighbors of I include6+e_I high vertices and12-e_I low vertices. Let L be this low set.

For u in L, its seven W-neighbors contribute7+h(u) two-step endpoints in R, where h(u) counts its high W-neighbors. Its isolated residual neighbor and its fixed neighbor contribute none. Hence e_E(u,R)=3-h(u). With e_L=e_E(L,R)<=4, the number of edges from L to the twelve high vertices is

 3(12-e_I)-e_L >=36-3e_I-4.

Each high vertex has at most two neighbors in L: two with the same isolated support would give a C4. The edge count is therefore at most24. This forces e_I>=8/3; since it is even and at most four, e_I=4.

Every W-to-R defect edge consequently ends in I. In particular every attached vertex has exactly one common neighbor with each of the four vertices of C.

## High attachments cannot reach all four cubic vertices

A high attached vertex cannot have two cubic residual neighbors: their budget contribution is four, exceeding two. If it has one cubic residual neighbor, its other residual neighbor must be isolated or a leaf; a degree-two neighbor would already give contribution three. Residual neighbors also lie in distinct involution orbits.

A low attached vertex meeting C has no high W-neighbor: its cubic residual neighbor contributes two to the budget, while any high W-neighbor would contribute one more. Thus for any high vertex v, only its high W-neighbors can provide two-step endpoints in C through W, and each such neighbor provides at most one C endpoint.

If v has support degrees0 and3, the residual part of its budget contributes one, so it has at most one high W-neighbor. Its R-middle walks contribute at most two endpoints in C: the isolated neighbor contributes none, and its cubic neighbor has at most two neighbors within C. The latter bound follows from the two-free-orbit C4 bound (partner plus at most one member of the other orbit). Therefore v has at most three two-step endpoints in C, contradicting the required four.

If v has support degrees1 and3, the residual budget contribution is two, so it has no high W-neighbor. Its R-middle walks contribute at most one C endpoint from the leaf and two from the cubic neighbor. Again at most three are possible, a contradiction.

Hence no high attached vertex meets C. Now fix any high vertex v. None of its W-neighbors can meet C: low ones are forbidden by the budget, and high ones were just excluded. Its residual support uses two distinct orbits among degrees0,1,2, so their degree sum is at most three. Its R-middle walks therefore contribute at most three endpoints in C. This again contradicts the four required endpoints.

There are twelve high vertices, so this contradiction excludes residual pattern01233. The argument uses no pending no-isolation bound, finite residual classification, graph solver, capped search or Lean formalization. The broader N80 branch remains unresolved.
