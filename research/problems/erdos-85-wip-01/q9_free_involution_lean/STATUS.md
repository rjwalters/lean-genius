# Free-involution obstruction — Lean checked

The integration module `proofs/Proofs/Erdos85FreeInvolution.lean` proves that a common neighbour of a moved pair under an adjacency-preserving involution must be fixed in a C4-free graph. Consequently, a fixed-point-free involution pair has disjoint neighbour sets. This holds without finiteness or degree assumptions.

Author targeted Docker build and axiom audit passed. Independent review 2167 compiled the full theorem source with read-only dependencies and passed; all three declarations use only propext, Classical.choice and Quot.sound. Author pins and peer evidence are archived here.

This formalizes the antipodal missing-two-step-offset premise used in even-order cyclic-action restrictions. It does not formalize the full N80/m16 exclusion or prove the Erdős 85 conjecture.
