# Full-branch reduction to 565 remaining pairs

The seven Lean exports certify the exact remaining set of full-U/R representative pairs. Four triangle-obstructed U representatives remove 52 of the initial 715 pairs. Fourteen other U representatives with a checked far-color obstruction remove 98 pairs when paired with the seven degree-eight R representatives containing the far edge. `remainingPairs_card` proves the remaining cardinality is **565** using ordinary kernel evaluation.

`actual_full_witness_pruned` proves that every actual 49-vertex graph in the four-secondary-edge branch has a completion witness on this remaining set, preserving cross-domain membership, external block cap, and all three joint families. `actual_full_excluded_pruned` requires false search results only for these 565 pairs, plus both search soundness proofs. **Those 565 false-search results remain unproved.** This does not exclude the deficient branch or solve Erdős 85.

All seven exports compiled with only propext, Classical.choice, Quot.sound (or a subset). The indices and no-color certificates are checked in Lean; Python was used only to discover the explicit table of low-degree vertices.

Reproduce after building the full coverage package: from `proofs`, run `lake env python3 ../research/problems/erdos-85-wip-01/full_orbit_pruning/check.py --coverage-build PATH_TO_BUILT_FULL_COVERAGE`. This compiles the neighboring Transport.lean into a temporary directory, then checks Pruning.lean. The coverage build must contain Assembly.olean and its shard dependencies.
