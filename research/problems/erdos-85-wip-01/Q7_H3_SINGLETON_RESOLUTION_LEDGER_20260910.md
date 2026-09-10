# H3 triple singleton resolution ledger

Every actual H3 triple profile supplies three partitions of eighteen empty vertices into six triples, with no empty-vertex pair repeated across the partitions. This necessary condition does not fix a triangle count or residual spectrum. Two explicit induced graphs pass the per-color condition but fail its joint form, so neither can extend to the H3 triple profile at any triangle count. No whole profile is excluded.

## Derivation

Use the reviewed universal triple partition: z is the unique triple-support vertex; its neighbors are the empty vertex u and special singleton vertices s0,s1,s2, one of each high color. The five empty neighbors Ui of si are disjoint. E consists of u, U0,U1,U2 and R, with sizes1,5,5,5,8.

Each high vertex has degree8 and neighbors z plus seven singletons of its color. One is si, leaving six ordinary singletons of each color. The special si has low degree6, already exhausted by z and Ui. Thus it has no ordinary-singleton neighbor.

For an ordinary singleton x, Ct=3 and absence of a z-neighbor imply exactly three singleton neighbors. Since its low degree is6, it has exactly three empty neighbors. The identity BC=J says that every empty vertex has exactly one low neighbor incident with each high color. At u this is already z for all three colors; at each vertex of Ui, the color-i neighbor is already si. Every other empty vertex therefore has exactly one ordinary singleton neighbor of color i.

Consequently the six ordinary singletons of color i have disjoint three-element E-neighborhoods partitioning E minus ({u} union Ui), a set of size18.

Each such triple contains no pair with an existing common neighbor in the known induced graph on E union {z,s0,s1,s2}: otherwise adding its ordinary singleton creates a C4. In particular it has at most one vertex from each Uj and at most one from N, the six E-neighbors of u. Across different colors, two triples cannot share two empty vertices, since the corresponding singleton vertices would give a C4. Equivalently, the sets of unordered E-pairs used by the three color partitions are disjoint.

These are only necessary conditions. Passing all three partitions does not supply the required edges among the eighteen ordinary singletons.

## Explicit finite examples

The accompanying standard-library verifier embeds two fixed49-edge graphs on24 empty vertices. Its literal edge lists are the complete fixture definitions. Vertices0..14 are the three Ui blocks,15..20 are N,21..22 are the other R vertices, and23 is u. It checks degree4 on23 vertices and degree6 at u, adds z=24 and si=25+i with their prescribed edges, and checks C4-freeness by all common-neighbor intersections.

For each color, it enumerates all eligible triples with no existing common-neighbor pair, then exhausts their exact covers by choosing an uncovered vertex and branching over every available triple containing it. Every partition is reached, because any exact cover contains precisely one such triple. It then checks every Cartesian product of the three per-color cover lists for repeated pairs.

The first fixture has2,4,1 individual covers for the three colors; the second has4,3,4. Both have zero compatible joint covers. Thus the failure is in the joint condition, not merely the existence of a partition for one color. The verifier has no timeout and asserts both exact counts and zero joint covers; it regenerates its adjacent JSON.

The fixture labels5 and58 identify their scratch provenance only. They are not a claim to classify all graphs in an isomorphism class or all completions of a U/R structure. The retained result concerns precisely the two literal induced graphs and the general resolution constraint derived above.
