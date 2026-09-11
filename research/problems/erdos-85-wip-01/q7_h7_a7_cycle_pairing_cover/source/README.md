# Exact proper-colouring cover when the empty graph is C7

Accepted2091 and2097 reduce a7 incidence construction to R=C7 or C3+C4, Q=K7 minusR, an empty graph F, and a proper Q-edge-colouring whose colour-class sizes are the F degrees. This package fixes F=C7. Every colour class is then a pair of disjoint Q edges, and all seven classes partition the fourteen Q edges.

check.py enumerates unordered partitions into seven such pairs by choosing the least remaining edge and each compatible mate. It visits12,074/11,955 recursive states and obtains2,355/2,340 raw partitions for the two R types. All automorphisms of R are independently derived by the7! vertex permutations: group orders14/48. Explicit orbit sets are disjoint and cover the raw partitions, leaving191/72 canonical partitions. No symmetry pruning occurs during the raw enumeration.

For a fixed partition with its seven blocks canonically indexed, assigning distinct empty colours means placing those blocks around the seven-cycle F. Its dihedral automorphism group acts freely on such placements, leaving7!/14=360 cyclic orders. colour_orders.py normalizes an order by rotating block0 first and taking the smaller orientation. It then quotients these360 orders by the full stabilizer of the partition in Aut(R), acting on block indices. Explicit orbit sets again partition all360 cyclic orders for every pairing representative.

This two-stage orbit decomposition is complete: first move an arbitrary edge-pair partition to its Aut(R) representative; the remaining ambiguity is exactly that partition's stabilizer. Then quotient labelled block placements by Aut(F) and that stabilizer. Different first-stage partition orbits cannot merge. Within each partition, cyclic orbit sets are disjoint. A final representative whose pairing orbit has size b and cyclic-order orbit has size c represents14*b*c labelled colourings; Aut(F) is free because every empty colour occurs.

The resulting complete proper-colouring cover is:

- R=C7:60,801 representatives, covering11,869,200 labelled colourings; full orbit sizes196:60,318 representatives,98:477,28:3,14:3.
- R=C3+C4:17,922 representatives, covering11,793,600 labelled colourings; full orbit sizes672:17,178 representatives,336:744.

The raw labelled totals also equal the independently enumerated raw pair-partition count times7!. The files retain every representative, all group actions, each orbit size, and the correspondence between a colouring's block cycle and its partition. A block at cycle position x receives empty colour x. Both finite enumerations completed on their first run, with no capped host census or remaining-low graph search.

Independent review is requested. This is a complete incidence-colouring domain only for F=C7 and the two a7 auxiliary R types. It does not assert that any singleton choices are possible, does not cover other F graphs, and excludes no H7/R/F class or Lean/global case. Historical UNKNOWN crossed6/7/8 host censuses remain untouched.
