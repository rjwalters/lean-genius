# Exhaustive permutation code shard

Kernel-checked full-U mask pair 129/66/66, using the public exhaustive Fin 120 permutation codes and generic cycle-or-orbit decoder. The 120 certificates contain 108 explicit C4 witnesses and 12 relabeling witnesses into the 55-entry representative list.

`UCodeShard.arbitrary_covered` covers every Lean permutation of Fin 5 for this fixed mask pair, conditional only on its induced U graph being C4-free. All three exported theorems use only propext, Classical.choice and Quot.sound. This does not establish all 225 full mask pairs, any deficient mask pair, actual graph transport, or H3 exclusion.

Reproduce from the parent compact_u_orbits directory: run `python3 generate.py` to produce witnesses.json, then `python3 code_shard/render.py`. From the integration worktree proofs directory run `lake env lean ../research/problems/erdos-85-wip-01/compact_u_orbits/code_shard/Shard.lean`. An explicit `--witnesses PATH` is also supported. Generation is deterministic; the output is checked in Lean using ordinary decide, with no native_decide.
