# Full U block-permutation coverage

The 55 full-U entries from the complete compact coverage map to 29 existing entries under explicit permutations of all three canonical blocks and their vertices. The Lean certificate checks both inverse identities, exact adjacency preservation, canonical-row images, membership in the target set and its cardinality. `joint_transport` preserves R and transports the same cross-domain, external-cap and joint-family witness. This does not prove that the 29 entries are nonisomorphic or exclude any graph.

The generic dependency is `Proofs.Erdos85ThreeHighBlockPermutationTransport`. The representative definition imports the existing verified `Full_3_3` shard and is definitionally equal to the complete full-coverage assembly representative.

From the integration `proofs` directory, after building the generic dependency:

```
lake env python3 PACKAGE/check.py --coverage-build FULL_COVERAGE_BUILD
```

The coverage build must contain `Full_3_3.olean`. The retained compile log/run receipt records the original kernel check with private olean output. No olean is distributed in this package.

`audit.py --witnesses FULL_WITNESSES_JSON` reproduces explicit Python witnesses, with no cross enumeration. It tries all block permutations and labels of an anchor block, propagating the labels through the two full matching links. `render.py` generates the Lean certificate from `audit.json`. Python is not a trusted proof step; Lean independently checks the finite data with ordinary `decide`, with no `native_decide` or `sorry`.
