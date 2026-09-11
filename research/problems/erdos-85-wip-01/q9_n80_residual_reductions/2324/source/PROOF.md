# Exclusion of residual orbit degrees (0,2,2,3,3)

Assume the N80/F10 cubic-fixed branch with displayed residual degrees. Use the no311 restriction submitted as2323, conditionally until accepted. It gives exactly five high attached involution orbits, all of residual degree two, and e_E(W,R)=2. Thus there are ten high attached vertices, and all other attached vertices have residual degree one.

Let I be the isolated residual pair, and let L be the set of low attached vertices whose unique residual neighbor lies in I. Each isolated residual vertex has nine neighbors in W. No attached vertex can meet both vertices of I: by applying the involution, it and its distinct involution partner would share those two residual neighbors, making a C4. Consequently the eighteen incidences from I to W involve eighteen distinct attached vertices. At most ten are high, so

 |L|>=8.

For u in L, let h(u) be its number of high W-neighbors. The vertex u has seven W-neighbors. Their residual degrees contribute7+h(u) distinct two-step endpoints in R, because every attached degree is one or two. Its residual neighbor is isolated and contributes zero such endpoints; its fixed neighbor also contributes zero. C4-freeness makes all those endpoints distinct, so the residual defect degree of u is

 e_E(u,R)=10-(7+h(u))=3-h(u).

Summing over L and using the total of only two W-to-R defect edges gives

 sum over u in L of h(u)
 =3|L|-sum over u in L of e_E(u,R)
 >=3*8-2=22.

The left side counts edges from L to the ten high vertices.

On the other hand, any high vertex v has at most two neighbors in L. If two distinct L-neighbors of v had the same unique residual neighbor r in I, then v and r would have those two vertices as common neighbors, a C4. Since I has only two vertices, at most two L-neighbors are possible. The ten high vertices therefore support at most twenty edges to L, contradicting the lower bound twenty-two.

Thus residual orbit degrees (0,2,2,3,3) are impossible. The proof uses2323 and no local residual graph classification; accepted2321 is unnecessary. It uses no finite enumeration, graph solver, capped-search premise or Lean formalization. The stronger uniform residual bound from combining all equality exclusions requires their separate accepted reviews.
