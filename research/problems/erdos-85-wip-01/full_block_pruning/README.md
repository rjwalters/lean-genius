# Full-branch reduction to 276 representative pairs

The completed compact-U coverage supplies55 full-template representatives.
The checked block-permutation certificates send all55 to29 listed targets,
transporting the same cross matrix and joint families with the secondary graph
fixed. Reapplying the existing triangle/far-color obstructions at those targets
leaves276 U/R pairs. `remainingPairs_card` checks the count in Lean.

`joint_witness_reduced` retains cross-domain membership, the external block cap,
and the joint witness together. `actual_full_witness_pruned` connects an actual
49-vertex graph in the full-template (`hr = 4`) branch to this reduced set.
`actual_full_excluded_pruned` requires only the276 remaining searches to return
false, along with the explicit external-search and terminal soundness premises.
Those false-search obligations are not proved here. The deficient branch and
Erdős85 itself remain open.

The new set is a checked subset of the previous565-pair set. No claim that the
29 targets are pairwise nonisomorphic is needed or made.

From the repository `proofs` directory:

```
lake env python3 ../research/problems/erdos-85-wip-01/full_block_pruning/check.py --coverage-build /path/to/verified/full/coverage/build
```

The coverage build must contain the previously verified full-U shard and assembly
oleans. The wrapper independently recompiles the three retained source dependencies
(`Transport`, `Pruning`, `Certificate`) into a temporary directory before checking
`Reduction.lean`. Optional `--build-dir` retains these new oleans in an empty
private directory for inspection. Repository artifacts contain source and logs,
not binary proof certificates. The receipt pins all three source dependencies.
