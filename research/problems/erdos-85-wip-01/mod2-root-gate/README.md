# Limits of the modular square-root test

The full test for a symmetric zero-diagonal square root over F2 cannot
exclude every simple (q-1)-regular connected nonbipartite defect graph on
q² vertices, even with the existing component-size law. For every q=2^k,
k>=3, [CONTROL.md](CONTROL.md) constructs such a graph D and a modular root.
This uniform proof passed independent review1551.

Every member of this family nevertheless fails the determinant-square
test over the integers. [ARITHMETIC_BOUNDARY.md](ARITHMETIC_BOUNDARY.md)
proves that det((q-1)I+J-D) is q(q+4) times a nonzero integer square;
q(q+4) is nonsquare for every stated q. Independent review1552 passed.
The family supplies no survivor of the combined existing filters, no
q-regular adjacency root over the integers, and no counterexample to A-REG.

[GATE.md](GATE.md), independently accepted in review1549, gives a separate
sufficiency result for semisimple M and records the scope of the inspected
characteristic-two polynomial-realization theorem. It also explains why
the all-ones vector imposes no additional condition at that modular stage.

The proof files retain the exact bytes reviewed, including their original
pending-review headings. Their completed review status is recorded here
and in manifest.json. These are prose proofs; none is Lean-formalized.

`check_control.py` constructs the control directly at q16 and q32 and
checks the full square modulo2, symmetry, zero diagonal, graph degrees,
connectivity, and an explicit triangle. It performs no candidate search,
uses only the Python standard library, and writes control-verification.json
beside itself. The integer row degrees of its modular roots are not q.
The uniform proofs, rather than these two regressions, establish all k.
