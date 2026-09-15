# F2 complete necessary host cover

The a7 F2 slice has 48 complete source bases and 3,944 E/S graphs (review 2116). Review 2655 independently accepts all 24,136 high pairings, with 1,496 E/S graphs admitting none.

The single host pass completed all 24,136 inputs in 37.032 s under a 60 s aggregate and 100,000-node per-input limit. No UNKNOWN or unvisited inputs remain. Exactly 16 high inputs have no host solution; 785,408 host leaves remain. Receipts contain 8,742,728 pruned prefixes in two shards (65,467,254 bytes).

The separate verifier reconstructed inputs from the 21-vertex graph, used the accepted F9 cover_reference.py and verify.dylib, and checked every complete receipt and endpoint in 42.805 s. This covers all 25,044,064 structural verification nodes. No producer rerun occurred.

This is a necessary host cover, not a residual graph existence or exclusion result. F2 and Erdős 85 remain open. Inputs resolve under the sol2 integration worktree; exact hashes, not an assumed checkout identity, establish provenance. The local integration ref during preparation was 7658415fb4670181d20aa229150fef781356ae55. Source/API hashes and reviewed premises are saved in high-launch.json and hosts/launch.json. Host runner and source files are immutable at the hashes in host-pins.json.
