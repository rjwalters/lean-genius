# Paper exclusion of residual pattern 01223

Assume the N80/F10 cubic-fixed branch and residual involution orbit degrees 0,1,2,2,3. Let I be the isolated residual pair. Use the exact attached endpoint and E-defect identities from accepted2251 and the isolated commutation calculation in accepted2333. No finite packing result is needed.

First n311=0. If a vertex v had k(v)=3, each of its five W neighbors would have to meet a residual vertex of degree at most one: otherwise that neighbor's residual budget is at least one and v contributes two, exceeding two. There are just four residual vertices of degree at most one, and the five W-neighbor supports are nonempty and pairwise disjoint by C4-freeness. This is impossible.

Thus the deficit equation t+2s=15-D with D=8 gives seven high2 orbits, fourteen high vertices, and all other attached vertices are low. The exact defect identity gives

    e_E(W,R)=30+2(-3-4-4-3)=2.

Write e_I=e_E(I,W). The isolated commutation identity, summing over fixed centers, gives h_I=6+e_I, where h_I counts high incidences at I. No attached vertex meets both isolated vertices: it and its involution partner would then have two common residual neighbors. The isolated pair consequently has eighteen distinct attached neighbors, of which 6+e_I are high and 12-e_I are low. Write L for this latter low set, and e_L=e_E(L,R). Both e_I and e_L are at most two and nonnegative.

For a low vertex u meeting an isolated residual vertex, the exact identity is

    e_E(u,R)=3-number of high W neighbors of u.

Therefore the number of edges between L and the fourteen high vertices is

    3(12-e_I)-e_L.

Each high vertex can meet at most two vertices of L: two lows with the same isolated support would form a C4 with that high vertex and the isolated support. The edge count is at most28. Consequently 36-3e_I-e_L<=28. Since e_I,e_L<=2, the left side is at least28; equality is forced throughout. Hence

    e_I=e_L=2,
    every high vertex has exactly two neighbors in L,
    every high vertex has one such neighbor at each member of I.

All E(W,R) edges have their W endpoint in L, because e_L equals the total defect two. In particular every high vertex v has e_E(v,R)=0. Also h_I=8, so some high vertex meets an isolated residual vertex.

Choose such a high vertex v and r in S_v intersect I. It cannot have a high W neighbor w. Indeed w has a low neighbor u in L with residual support r, by the equality above. Then v-w-u-r-v is a C4: all four vertices are distinct, because v,w are high, u is low, and r is residual.

Thus v has no high W neighbors. Its exact defect is

    e_E(v,R)=4-sum_{x in S_v}d_R(x).

Its support consists of r of degree zero and a second residual vertex of degree at most three. Hence e_E(v,R)>=1, contradicting its required zero defect. This excludes01223.

This proof uses neither the pending finite support review2358 nor the invalid intermediate defect-location run, nor the corrected local-coverage computation. It does not require acceptance of the 11123 exclusion. It is a paper consequence of the established structural identities, and makes no full N80 or global Erdős85 claim.
