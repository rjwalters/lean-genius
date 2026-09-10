# Actual full-branch reduction to 715 representative pairs

`FullUOrbitTransport.actual_full_witness` moves the actual 49-vertex graph's four-secondary-edge branch to one of 55 full-U representatives and one of the 13 degree-eight R representatives. The same cross matrix carries cross-domain membership, the external block cap, and the entire three-family joint witness. Complete full-U orbit coverage is imported from the reviewed `full_coverage/Assembly.lean`; no universal coverage assumption remains.

`actual_full_excluded` reduces exclusion of this branch to an explicit false-search premise on those 55 × 13 pairs, together with external-search and terminal soundness. **Those search rejections are not proved here.** The deficient branch and the full Erdős 85 conclusion remain open.

All three exports compiled with ordinary Lean and only propext, Classical.choice, Quot.sound. An initial linter recursion-limit failure was fixed by raising maxRecDepth; the retained log is the final successful run.

To reproduce, first build the neighboring `compact_u_orbits/full_coverage` package as its README describes. From the worktree `proofs` directory, run `lake env python3 ../research/problems/erdos-85-wip-01/full_orbit_transport/check.py --coverage-build PATH_TO_BUILT_COVERAGE`. The build directory must contain the compiled Assembly and its 100 shard dependencies. This checks the retained source without modifying the coverage package.
