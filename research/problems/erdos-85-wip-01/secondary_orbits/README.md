# Secondary configurations: 132 covered by 21 representatives

`generate.py` enumerates all 294 parameter codes, selects the 132 admissible
codes, and supplies matching-preserving permutations to 21 representatives.
The permutations preserve the six near labels and two far labels. Every
adjacency entry is checked by the generator. `witnesses.json` retains the result.

`render.py` produces the explicit Lean witness table. Reproduce from this folder:

```sh
python3 generate.py
python3 render.py /tmp/Erdos85ThreeHighSecondaryOrbitTable.lean
```

Compare that output with `proofs/Proofs/Erdos85ThreeHighSecondaryOrbitTable.lean`
in the repository. The Lean theorem checks the table using ordinary kernel
`decide`, with only `propext`, `Classical.choice`, and `Quot.sound` in its axiom
report. Python is a generator, not a trusted proof oracle. Kernel compilation
may transiently use about 10 GB; avoid overlapping table builds.

`Erdos85ThreeHighSecondaryOrbitCover` covers every admissible tuple, and
`Erdos85OrderFortyNineThreeHighTripleSecondaryOrbitCoordinates` transports the
existing actual graph chart to these representatives. Both preserve matching
size, near/far membership and all adjacency entries.

The formal claim is coverage by 21 indexed representatives, not minimality
of that list. This does not evaluate the full graph search, exclude the H3
case, or solve Erdős 85.
