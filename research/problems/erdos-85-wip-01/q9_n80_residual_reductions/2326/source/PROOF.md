# Exclusion of residual orbit degrees (0,2,2,2,3)

Assume the N80/F10 cubic-fixed branch with displayed residual degrees. Use the attached pattern and defect identities of accepted2251 and the exact two-step endpoint budget. Let I be the isolated residual pair. All other residual degrees are at least two.

## No degree-three attachment

If v had attached residual degree three, each of its five W-neighbors u would have to meet I. Otherwise its nonempty residual support would contribute at least one to sum(d_R(r)-1), while the W-neighbor v contributes two to sum(k(w)-1), contradicting the budget at most two. Other W terms are nonnegative. Distinct W-neighbors of v have disjoint residual supports by C4-freeness, so five nonempty supports in I are impossible. Thus n_311=0.

Since D=9, the incidence identity gives n_211+2n_221=6. There are exactly twelve high attached vertices, all of residual degree two; all others are low, of residual degree one. The exact defect identity gives

 e_E(W,R)=30+2[3*(-4)+(-3)]=0.

## Each isolated vertex has precisely three high attached neighbors

Fix r in I. It has nine W-neighbors, meeting nine distinct fixed-center groups. Let f be the sole missed fixed center. Then E(g,r)=1 exactly at g=f among the fixed centers.

For any fixed center g, commutation ME=EM at (g,r) has left side1[g adjacent to f in H]: its fixed-neighbor contribution is that indicator, while its attached-neighbor contribution vanishes because E(W,R) is empty. On the right, r has no fixed or residual neighbors, so only terms E(g,u) with u in N(r) intersect W remain. Therefore

 1[g adjacent to f in H] = sum over u in N(r) intersect W of E(g,u).

Summing over all ten fixed centers, the left side is three because H is cubic. On the right every low attached vertex has zero fixed E-targets and every high vertex has one: a vertex of residual degree k misses exactly k-1 of its seven possible W slots. Hence r has exactly three high and six low W-neighbors.

No attached vertex meets both vertices of I, since it and its distinct involution partner would then share those two neighbors. Consequently there are twelve distinct low attached vertices meeting I. Call their set L.

## Edge capacity contradiction

For u in L, its isolated residual neighbor contributes no two-step endpoint in R. Its seven W-neighbors contribute7+h(u), where h(u) is the number of high W-neighbors. Its fixed neighbor contributes none. The residual defect is zero, so10=7+h(u), giving h(u)=3. There are therefore36 edges between L and the twelve high attached vertices.

Each high attached vertex has at most two neighbors in L, since any two with the same isolated residual support would form a C4 through that high vertex and the isolated vertex. Thus the twelve high vertices support at most24 such edges. Contradiction.

Residual orbit degrees (0,2,2,2,3) are therefore impossible. The proof repeats the needed no311 argument explicitly and does not depend on the pending02233 exclusion or any residual graph classification. No finite search, graph solver, capped-search premise or Lean formalization is used.
