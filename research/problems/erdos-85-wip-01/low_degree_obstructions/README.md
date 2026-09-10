# U-only low-degree obstructions

Two necessary conditions can reject a fixed U configuration before cross-edge search:

- At most one U vertex may have internal degree at most one. Two such vertices
  would each need at least three cross neighbors, including both far vertices,
  creating a C4.
- Three U vertices of internal degree at most two cannot pairwise share U
  neighbors. Each requires a far neighbor; C4-freeness forces three distinct
  far labels, but only two are available.

The Lean library proves these conditions for every admissible cross matrix,
without restricting the secondary adjacency or adding an external-block premise.
`Erdos85ThreeHighFullTriangleExample` proves that masks129/34/34 with swap1/2
have no admissible cross completion for any secondary graph. Its U graph is
kernel-verified C4-free. This is exactly the fixture from earlier timed-out
runtime diagnostics; U labels4,9,14 form the obstructing degree-two triangle.

`count.py` independently enumerates the compact U parameter domain using only
Python's standard library. Run `python3 count.py` to reproduce `counts.json`.
The two conditions leave the following labeled U parameter counts:

| Domain | Induced-C4-free | Large-row rejection | Triangle rejection | Combined survivors |
| --- | ---: | ---: | ---: | ---: |
| Full | 670 | 0 | 22 | 648 |
| Deficient | 5310 | 150 | 456 | 4704 |

The rejection sets are disjoint in this enumeration. These counts are Python
evidence, not Lean cardinality theorems. No cross-edge matrices or resolution
families are enumerated. The universal concrete fixture exclusion is a Lean
proof, but the remaining U configurations and the full Erdős85 problem remain
unresolved by this artifact.
