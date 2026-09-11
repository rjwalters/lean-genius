# Review 2190 — PASS (redirect of 2187)

codex-sol-2, 2026-09-11. Source pins and live accepted premises2176/2179/2184 verified. No graph search or producer mutation.

For a fixed source vertex in attached orbit (u,a), every residual orbit having colours (a,b) supplies exactly one length-two matching path into attached orbit (v,b). Hence the residual contribution is precisely T_uv. With permutation matrices indexed by source rows and destination columns, the internal-source contribution is E P_uv and the internal-destination contribution is P_uv E. Each of the three other attached groups contributes P_uw P_wv. The source's sole fixed neighbour u has no neighbours in B_v, so fixed middle vertices contribute zero. These middle classes partition all vertices. The target orbit has three vertices, each allowing at most one common neighbour with the source, which is outside that orbit. Thus the entrywise bound is valid. Its total is 10+2+2+9=23, against capacity27, leaving slack4.

For endpoints in R, the middle classes contribute 4(4-e), 12+h, 3e and zero respectively: residual neighbours, four other attached groups, an internal matched partner, and the fixed neighbour. This totals28-e+h. All thirty residual vertices differ from the source, so C4-freeness bounds this total by30 and yields h(0)<=2, h(1),h(2)<=3. Each of the four permutations has one preimage of label zero, giving sum h=4. The unmatched-to-unmatched relation is symmetric under inverse permutations, and consequently forms a simple graph of maximum degree two.

Independent scalar verification checked the walk identity for all3888 source-label/four-permutation combinations, together with the total/slack arithmetic. This verifies the count formula, not feasibility of those permutation assignments. Matching phases can change endpoint collisions, but cannot invalidate these necessary multiplicity bounds.

Scope: the paper's necessary attached-orbit capacity constraints only. This neither constructs nor excludes a complete residual permutation system or any graph witness. Review2187 was cancelled solely for reassignment; this review supplies its mathematical acceptance under ID2190.
