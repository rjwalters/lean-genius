# Prime-orbit matching obstruction — Lean checked

`proofs/Proofs/Erdos85PrimeOrbitMatching.lean` proves that a fixed-point-free period-p map on p vertices, p prime, is transitive. If p is odd, an adjacency-preserving such map cannot preserve a nonempty graph of maximum degree one on that set.

The first proof uses prime minimal period and equal-cardinality surjectivity. The second propagates any edge to make every degree one, contradicting handshake parity at odd order. No C4-freeness is assumed by these generic lemmas.

Author targeted build/direct-source audit and independent review2185 passed. Both declarations use only propext, Classical.choice and Quot.sound. The source and peer evidence are archived here.

The attached-neighbour application must still establish the invariant subset, prime cardinality, free action and maximum-degree-one hypotheses. This is not the full order-seven automorphism exclusion or an unrestricted graph exclusion.
