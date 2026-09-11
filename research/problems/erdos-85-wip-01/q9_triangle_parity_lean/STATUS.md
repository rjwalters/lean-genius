# Local triangle parity — Lean checked

The integration module `proofs/Proofs/Erdos85TriangleParity.lean` proves that, in a finite C4-free graph, a vertex whose every incident edge lies in a triangle has a 1-regular induced neighbourhood and even degree. An odd-degree contrapositive is included.

Author targeted Docker build and direct full-source axiom audit passed. Independent review 2170 repeated full-source compilation with read-only dependencies and passed. All three declarations use only propext, Classical.choice and Quot.sound. Author pins and peer evidence are archived here.

This is the local parity endpoint of the all-singleton quotient obstruction accepted in review 2164. It does not formalize the quotient saturation premise, full mixed-orbit triangle divisibility or an unrestricted graph exclusion at 78 or 80.
