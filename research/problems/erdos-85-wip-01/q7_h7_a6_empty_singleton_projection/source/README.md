# Complete a6 empty/singleton projection

Under the accepted H7 incidence premises (2091 and 2099), six empty-empty edges imply eleven singleton vertices with two empty hosts and singleton degree one, and three with one empty host and singleton degree three. At empty x with F degree d, the number of singleton incidences is 7-2d. F is a seven-vertex, six-edge, subcubic C4-free graph.

cover.py checks all 54264 labelled six-edge subsets of K7. Exactly 31332 pass, covered by 19 disjoint S7 orbits. For each representative it chooses eleven distinct pairs with no common F neighbor, subject to degree_X(x)<=7-2degree_F(x). These conditions are necessary and sufficient for the E/S host graph to be C4-free: an E/E pair may acquire a second common singleton only from repeated host pairs, and an E/S pair has two common empty neighbors precisely when a double host pair has a common F neighbor. The remaining singleton multiplicities are forced by the capacities. Relabelling empty vertices by Aut(F), and naming otherwise indistinguishable single-host vertices, loses no extensions.

All 26012 candidate X subsets were inspected. Seven F classes admit 2192 raw X graphs and 358 Aut(F) orbits. Every base is directly checked for degree and C4-freeness.

complete.py exhaustively fills singleton stars using the independently reviewed 2107 graph algorithm. Target E/S total degree is 5 minus the singleton empty degree, equivalently singleton-only degree 5-2e. New edges join unfixed vertices. The candidate-to-existing and candidate-to-candidate neighborhood tests exclude exactly the newly created C4s; fixing a vertex and enumerating all its remaining neighbors is exhaustive. Each terminal graph is directly validated. The sole pass completed all 358 bases: 267 negative, 91 positive, 3284 distinct labelled E/S graphs, 85134 recursive states, maximum 8568 per base, about 1.04 seconds. No UNKNOWN or unvisited cases.

verify.py independently enumerates with fixed ascending vertex order and whole-graph length-two path collision checks. It reproduced the exact solution sets on all 358 bases: 1062951 states, maximum 56903, 17.662 seconds. Both algorithms used 100000 states per base and 60 seconds aggregate. Neither pass hit a limit or was restarted.

The output is a complete necessary E/S projection, not a completed 49-vertex graph or an a6 exclusion. All seven F classes with host graphs still have singleton extensions. High colours and pair vertices remain to be assigned. The three single-host vertices must belong to different sum-three highs, each paired with a double-host vertex. Remaining double-host vertices form four sum-four highs. Only mixed pairs inherit the accepted same-high nonadjacency condition; imposing it on double/double pairs would be unjustified.

No historical capped host search, SAT queue, Lean proof, or global problem status is changed. Independent peer review is requested for this package.
