# Period-seven fixed-graph reduction — Lean checked

Integration modules `Erdos85TwoNineDegreeReduction.lean` and `Erdos85OrderSevenFixedGraph.lean` prove the fixed-graph reduction for a nonidentity period-seven adjacency-preserving map on a C4-free minimum-degree-nine graph of order78 or80. The fixed set has cardinal8 at78, or3/10 at80; every fixed vertex has exactly two fixed neighbours.

All cardinal, degree-congruence and boundary hypotheses are derived in the assembly. The proof combines accepted prime fixed-degree, moved-cardinality and boundary lemmas with a new degree-moment reduction and handshake parity. Author targeted builds and combined-source audit passed. Independent review2183 compiled all seven source bodies without importing precompiled submitted theorems, and passed with only propext, Classical.choice and Quot.sound.

This is the first half of accepted paper2169. Excluding the remaining attached-orbit configurations is still a formalization obligation; this package does not claim the full no-order-seven theorem in Lean or unrestricted graph nonexistence.
