# Moved-vertex regularity — Lean checked

The integration module `proofs/Proofs/Erdos85MovedRegularity.lean` proves that the moved induced graph is eight-regular when it has fewer than64 vertices, for an adjacency-preserving map of a finite C4-free graph of minimum degree at least9. If the original graph is nine-regular, each moved vertex has exactly one fixed neighbour.

Author targeted build and direct-source audit passed. Independent review2177 compiled the full new source and passed; both declarations use only propext, Classical.choice and Quot.sound. Original and peer evidence is archived here.

This proves an exact boundary contribution for moved cardinalities60/63. It does not exclude those cases, classify order-three actions or solve the unrestricted graph problem. No bijectivity, prime period or total-cardinality hypothesis is imposed by the module.
