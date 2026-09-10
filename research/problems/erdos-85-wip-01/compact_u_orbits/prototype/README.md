# Kernel-checked U coverage prototype

This prototype fixes the full-U masks to [129,66,66] and checks120 explicitly coded permutations. Each code has verified left/right inverse data. The certificate table contains108 explicit C4 witnesses and12 relabelings into the existing55-entry representative list. It uses the production `threeBlockMatchingAdj` definition.

`UPrototype.checked` verifies each certificate by ordinary kernel `decide +revert`. `UPrototype.covered` uses the actual encoded-C4-free premise to rule out the explicit cycle branch and obtains a bijective relabeling preserving every adjacency. Both exports compiled with only propext, Classical.choice and Quot.sound. The retained log and receipt pin the checked source.

This is one mask-pair shard only. The Lean completeness proof for coding every arbitrary Fin5 permutation, the other224 mask pairs, the deficient case and actual E24 transport remain outstanding. It is not the full55/370 coverage theorem or any whole-graph rejection.

To reproduce, first run `python3 generate.py` in the parent compact_u_orbits directory to generate witnesses.json, then run `python3 prototype/render.py`. From the integration worktree proofs directory, compile with `lake env lean ../research/problems/erdos-85-wip-01/compact_u_orbits/prototype/Prototype.lean`. The portable renderer was checked to reproduce the exact compiled bytes in a private directory. No runtime search is involved.
