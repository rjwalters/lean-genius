# Literature check — 2026-09-13

This is a source-scoped fallback check, not certification that no newer result exists. Write r(s)=R(C4,K1,s), distinct from the paper's graph-order extremal function.

The authors' institutional record for [Zhang–Chen–Cheng, Some values of Ramsey numbers for C4 versus stars (2017)](https://research.polyu.edu.hk/en/publications/some-values-of-ramsey-numbers-for-csub4subversus-stars/) states r(q(q−1)−t)=q²−t for odd prime powers q≥5 and even t=2,4,…,2ceil(q/4). Substitution at t=2 gives r(108)=119 for q=11 and r(154)=167 for q=13. Consequently no C4-free graph has minimum degree11 on119 vertices or minimum degree13 on167 vertices: its complement would avoid the corresponding star. The theorem does not give r(109) or r(155), since either would require t=1.

[Boza, Exact values and bounds for Ramsey numbers of C4 versus a star graph, v2 (2026)](https://arxiv.org/html/2409.12770v2) gives the general upper bound r(s)≤s+ceil(sqrt(s−1))+1 in Corollary3. Combining it with elementary monotonicity and the preceding exact values gives the conservative bounds 119≤r(109)≤121 and167≤r(155)≤169. These are deductions from the checked statements, not claims of the best published bounds. Boza's special m²+3 theorem does not apply to109 or155. The two functional inequalities also do not directly assign either requested exact value.

The Ramsey definition gives: a C4-free N-vertex graph with minimum degree d exists iff r(N−d)>N. Thus the two target questions are precisely r(109)>120 and r(155)>168. Neither is settled by the sources checked above. I have not independently established the stronger assertion that both are currently open throughout the literature; the final report must preserve that distinction until a broader literature review is accepted.

Independently of literature, below-square regularity follows from elementary counting: in a C4-free graph of minimum degree d, the second-neighborhood count at v gives N≥1+deg(v)(d−1). A vertex of degree≥d+1 would force N≥d². Therefore N<d² implies every vertex has degree d. Any target witness is accordingly11-regular at120 or13-regular at168. This deduction does not prove existence or nonexistence.
