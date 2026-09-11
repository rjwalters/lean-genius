# A genuinely different a7 empty-first normal form

This is a parametrization of the edges incident to all high and empty vertices, conditional on accepted H7/a7 premises (including2091). It does not enumerate or resume any old high0 host tree. Credit: the proper-edge-colouring observation was independently discussed by codex-sol-3 in room47210.

Let the high colours be0..6. Let R be C7 or C3 disjoint union C4, and Q=K7\R. Let F be the graph induced by the seven empty vertices: seven edges, maximum degree3, and no C4. A pair-support vertex Pij has one empty neighbour exactly when ij is in Q, and no empty neighbour otherwise. Write phi(ij) for that neighbour's empty label.

The complete pair-empty incidence is exactly a proper edge-colouring phi:E(Q)->V(F) whose colour class x has size deg_F(x). Properness means every colour class is a matching, forced by C4 with a high vertex. Class size follows from the empty vertex's degree and high-colour saturation: its pair-neighbour count equals its empty-neighbour count. Thus the fourteen Q edges partition into seven matchings of prescribed sizes.

For each high i, its four incident Q edges have four distinct colours. Let U_i be the three unused empty colours. The high has one double-empty singleton D_i and one single-empty singleton L_i (2091 plus2085). Choose a two-element set T_i contained in U_i for D_i; the remaining element of U_i hosts L_i. There are initially exactly three choices at every high. These choices exhaust all singleton-empty incidences up to the within-high singleton naming convention.

Every empty vertex now has degree7 automatically. If its F degree is d, its d incident pair-support vertices cover2d high colours. The other7-2d high colours each contribute exactly one singleton neighbour, so total degree is d+d+(7-2d)=7. Every high has degree8 from the fixed supports. Every high-empty pair has exactly one common neighbour. No edges among the35 nonempty low vertices have yet been chosen.

## Exact C4 condition for this partial graph

In addition to F being C4-free and phi proper, the partial49vertex graph is C4-free if and only if:

1. each selected pair T_i has no common neighbour in F;
2. the seven selected pairs T_i are pairwise distinct.

Proof by vertex-pair types: high-high pairs have their unique pair-support common neighbour; high-empty pairs have exactly one by the unused-colour construction; high/nonempty-low pairs have none. Two pair-support vertices cannot gain a second common neighbour because phi is proper. Pair-support/singleton pairs cannot share both a high and empty because U_i omits colours incident to i. Same-high singleton pairs have disjoint empty hosts; different-high singleton pairs can have two common neighbours only when two D hosts coincide. Empty/nonempty-low pairs can have two common neighbours only when a D-host pair has a common F neighbour. Finally an empty pair x,y has |N_F(x) intersect N_F(y)| common empty neighbours, no common pair-support vertex, and one common singleton for each T_i={x,y}. The two conditions are exactly what is needed to keep this total at most one.

Consequently, for fixed F and phi, existence of a C4-free high+empty-complete partial graph is a seven-row system of distinct representatives: row i contains the at most three two-subsets of U_i with no common F neighbour. A matching selecting seven distinct row values is necessary and sufficient. It determines all D/L incidences. This allows an exact small matching test before any remaining-low-edge completion.

This is stronger than checking F-only host-pair capacities, because the candidate pair sets are tied to the particular Q edge-colouring. It is still only a necessary partial-graph stage for H7: the remaining low degrees and all additional common-neighbour constraints must be fulfilled later. It establishes neither a7/H7 exclusion nor a Lean theorem. No capped search is reclassified or retried.

## Degree identities behind the premises

For any low vertex of supportweight w, let p,s,e count its low neighbours of supportweight2,1,0. The seven saturated high rows give2p+s=7, while low degree is p+s+e=7-w. Hence p-e=w and p<=3. In particular pair emptydegree<=1, singleton emptydegree<=2, and empty pairdegree equals its emptydegree<=3. These identities follow from C4freeness and the H7 high-degree saturation, not from a sampled computation. With a7 and accepted2091, every high has singleton-empty sum3, so deg_Q(i)=4 and R is2regular.

## Finite equivalence checks

check.py chooses one proper-colouring witness for each of two R types and two valid F graphs, then checks all2187singleton choices per fixture. It reconstructs all49vertices and checks high degree8, empty degree7, all high-empty common-neighbour equations, and direct all-pairs C4freeness. All8748outcomes match the two pair conditions. A separate subset-of-pairs dynamic programme counts distinct representatives and agrees:54/0/63/0 completions of the four fixed incidence fixtures. The zero counts exclude only those fixed colourings, not their R/F classes. No full colouring space, low-edge completion, or old capped host domain was enumerated.
