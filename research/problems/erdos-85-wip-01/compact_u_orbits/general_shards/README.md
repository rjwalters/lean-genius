# General full and deficient U orbit shard generator

`render.py` takes `--witnesses PATH --a INDEX --b INDEX --output PATH`, plus `--missing SOURCE` for deficient graphs. Mask indices use the public15-code order. Each generated theorem checks all120 public permutation codes against the production full or deficient template using ordinary Lean decide. Each entry is an explicit C4 witness or exact relabeling into the audited55/370 representative list.

Checked pilot outputs: `Full_0_0` (masks129/129/129,120 cycles,0 orbits) and `Deficient_3_3_0` (masks129/34/34,missing source0,100 cycles,20 orbits). Both source compiles terminated with rc0, and all four exported theorems depend only on propext, Classical.choice and Quot.sound. Final measured compiles took5.86s and9.73s respectively on this host; these are individual runs, not a throughput estimate. An initial deficient run hit the default recursion limit during representative-table elaboration; the final generator sets a larger limit and the repeated compile passes.

Generate input witnesses from the parent `generate.py` or `generate_deficient.py`; the per-shard JSON pins their hashes. Run emitted files using `lake env lean ABSOLUTE_PATH` from the integration worktree proofs directory. Both pilot outputs were reproduced byte-identically by the final generator. The generator itself is untrusted: only a successful Lean check establishes its output theorem.

This package establishes two individual shards, not all225 full or1125 deficient mask/source shards. Universal certificate validity, full orbit coverage and the actual graph transport remain open. The earlier `code_shard/` separately establishes masks129/66/66 for arbitrary Lean permutations.
