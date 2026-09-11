# A7 non-cycle empty graphs: complete host cover and bounded S frontier

Accepted2090 independently classifies all seven-vertex, seven-edge, maximum-degree-three C4-free graphs into15 isomorphism classes. Although used there for a singleton core, the finite graph-class definition also covers a7 empty graphs. Its all-degree-two class is the already studied C7. This package covers the other14 classes without rerunning the cycle case.

At empty x, let d(x)=deg_F(x). The H7 incidence equations give d(x) pair hosts and7-2d(x) singleton hosts. Accepted2091/2097 give seven double-empty singleton pairs, all distinct and individually having no common F neighbor. Their host graph X therefore has seven edges among the admissible pairs, and degree_X(x)<=7-2d(x). The remaining7-2d(x)-degree_X(x) single-empty singleton vertices are placed at x. Their total is seven. Host naming loses no extension, because identical single-empty names may be permuted along with all later edges.

F is C4-free, so each pair has at most one common F neighbor. There are exactly21-sum_x choose(d(x),2) admissible pairs. This is at most14 when sum d=14, with equality only for all degrees two. Thus each non-cycle F has at most13 admissible pairs and at most1716 seven-subsets.

cover.py completes all14 finite host covers under the original100000 subset bound per F and60seconds overall. Independent bitmask enumeration and explicit automorphism actions in verify.py reproduce every raw set and disjoint orbit. There are1310 X orbits. Source F indices1,7,12 have no host graph; these repeat the known small capacity obstruction. Other F indices have48,48,149,100,28,119,297,39,48,301,133 orbits in source order with the zero cases omitted.

complete.py adapts the direct MRV graph-star traversal independently reviewed in2107. It fills the singleton graph with seven vertices of S-degree one and seven of S-degree three. Every new edge is between unfixed vertices, and every newly created C4 must contain the star center; candidate/existing and candidate/candidate common-neighbor tests are exact. Each completed graph is directly checked again. The search has100000 recursive nodes per X and a single60second aggregate deadline.

The sole pass hit that aggregate deadline:860 bases COMPLETE, source_index860 UNKNOWN,449 further bases unvisited. These statuses are permanently preserved; there is no retry or cap increase. It saved46728 valid labelled S graphs, including any prefix outputs of the UNKNOWN base. All bases for source F indices0 through9 are complete; F10 is partial; F11/F13 are unvisited; F12 has zero host bases. No surviving non-cycle F class is excluded by this result.

verify.py independently validates all46728 stored graphs, exact degrees, C4-freeness, uniqueness and ordered case joins, together with the complete X cover. It does not rerun the S enumeration and does not claim independently reproduced terminal solution counts. Completeness of the860 terminal cases rests on the audited exhaustive traversal; review is requested with that limitation explicit. UNKNOWN outputs can be used as witnesses only, never as a complete cover.

The other empty shapes, a6, H7 and the Lean/global theorem remain open. This package changes no historical host-tree status or Phase B queue.
