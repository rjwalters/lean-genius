# H5/T1 heavy-core and singleton-host feasibility

This bounded census is a necessary finite-structure reduction, not an exclusion of H5/T1. It finds 2,578 labelled heavy cores in 249 symmetry classes. A per-colour singleton-host matching condition rejects 138 labelled cores in 14 classes, leaving 2,440 labelled cores in 235 classes. The exhaustive run within this core model used 18,005 DFS nodes and about 0.13 seconds, below the 100,000-core / 60-second caps. No SAT solver or terminal extension search ran.

## Premises and model

The canonical T1 support system has one triple {0,1,2} and the seven pairs not contained in that triple. These eight vertices are the heavy core. There are 23 singleton vertices, with colour multiplicities (5,5,5,4,4), and 13 empty-support vertices. The low adjacency/support identity BC=J says that the supports of a low vertex's low neighbours partition the five high colours. Degrees are 7 minus the vertex's support size.

Let a=e22 count pair/pair edges and b=e23 count triple/pair edges. There is only one triple, so e33=0. The support-edge ledger gives e00=a+2b+12, e01=68−4a−7b, e02=2a+2b, e03=b−1, e11=4a+6b+15, e12=35−4a−3b and e13=5−2b. Nonnegativity forces b=1 or2 and the additional inequalities checked in the census. These are necessary ledger conditions, not an assertion that a completion exists.

The DFS enumerates every subset of the 28 possible heavy edges. Adding an edge is allowed only when neighbour supports remain disjoint and no second common heavy neighbour creates a C4. Together with the fixed high-support edges this ensures C4-freeness of the partial graph. At leaves it applies ledger nonnegativity. Quotienting uses all S3 permutations within the triple and S2 permutations of its complement, the full colour automorphism group of this support system. `audit.py` independently builds each retained representative as an explicit 13-vertex partial graph, checks every pair of common-neighbour sets, and checks orbit sizes under all 12 colour transports. This audits representation and orbit weights; it is not a second exhaustive census.

## Necessary singleton-host test

For a given colour c, every heavy vertex whose heavy neighbours do not already cover c must acquire exactly one singleton neighbour of colour c. A singleton can host at most two heavy vertices, since each heavy support has size at least two and BC=J permits total support weight only five. Two required heavy vertices can share a singleton only if their supports are disjoint and they have no existing common heavy neighbour; otherwise a high colour repeats or a C4 is formed. Hence compatible pairs form a graph, and the minimum number of singleton hosts is number-required minus maximum matching size. This must not exceed the available singleton count for that colour.

The matching test is applied independently for each of the five colours. It does not enforce consistency between colour assignments, prevent repeated heavy pairs across different singleton colours, or complete singleton and empty edges. Passing therefore establishes only this necessary condition. The 235 survivors remain open; no Phase B root is removed.

Run `python3 census.py` and then `python3 audit.py` from a scratch copy. They write only small JSON results. No Lean theorem or kernel certificate is claimed for this census.
