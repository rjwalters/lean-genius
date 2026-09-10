# Deficient representative pruning

The finite set starts with 370 explicitly listed U representatives and the eight
secondary representatives of degree total six. Exact compact-parameter equalities
connect seven reviewed obstruction tables to their representative indices.

The union of unconditional obstruction tables contains 142 representatives.
Ninety further representatives are excluded when the secondary far edge is present;
this applies to the three degree-six secondary codes `{0,1,11}`. The resulting set
has 1554 pairs, down from 2960. The union/difference definitions handle overlap.

`actual_pair_mem` retains the same cross matrix and requires its cross-domain
membership, external block cap, and secondary degree-class membership. It does
not assert that the remaining searches return false or exclude the full branch.
This artifact uses the representative definition from the first completed shard;
it does not depend on, or assert, completion of the 200-shard coverage proof.
Connecting an arbitrary graph to these representatives is a separate theorem.

From the repository's `proofs` directory, with a verified deficient coverage build:

```
lake env python3 ../research/problems/erdos-85-wip-01/deficient_orbit_pruning/check.py --coverage-build /path/to/deficient/build
```

`indices.json` records the generator's lookup data. The Lean equalities and finite
cardinality theorem independently verify the mathematical assertions; Python is
not part of the proof trust base. All exported proofs must use only the standard
axioms `propext`, `Classical.choice`, and `Quot.sound` (or a subset).
