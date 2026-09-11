# Strict tight-point cardinality — Lean checked

`proofs/Proofs/Erdos85TightCardinality.lean` transports the existing Fin tight-point obstruction to arbitrary finite vertex types, then proves that a nonempty C4-free graph of minimum degree at least k>=3 has strictly more than k(k-1)+1 vertices.

The proof reuses the existing friendship-theorem obstruction and distance-layer bound. In particular a nonempty induced graph of minimum degree4 has at least14 vertices, and one of minimum degree8 has at least58.

Author targeted build and direct-source axiom audit passed. Independent review2174 compiled the full source and passed; both declarations use only propext, Classical.choice and Quot.sound. All source and independent evidence are archived here. This is a reusable formal bound, not a global exclusion at78/80 or a solution to Erdős85.
