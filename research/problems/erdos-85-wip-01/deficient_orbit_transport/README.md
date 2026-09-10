# Actual deficient branch reduced to 1554 representative pairs

`DeficientUOrbitTransport.actual_deficient_witness` moves the actual49-vertex graph's three-secondary-edge branch to one of370 deficient-U representatives and one of8 degree-six R representatives. The same cross matrix carries cross-domain membership, the external block cap and the complete three-family joint witness. It uses completed deficient coverage; no universal coverage premise remains.

`actual_deficient_excluded` uses the reviewed structural-pruning interface to require search rejection only on `DeficientUOrbitPruning.remainingPairs`, whose kernel-checked cardinal is1554. The false-search premise and both search/terminal soundness premises remain explicit. No remaining search rejection is proved here, and Erdős85 remains open.

All three exports compiled with ordinary Lean and only propext, Classical.choice and Quot.sound. The constructorNameAsVariable name-style linter exhausted its own recursion/heartbeat budget on the large actual-witness theorem despite raising file limits. It is disabled only for that theorem; kernel proof checking and other linters remain enabled. The retained compile log is terminalrc0.

To reproduce, build the sibling compact_u_orbits/deficient_coverage package to obtain Assembly.olean and its200 dependencies. Also compile sibling deficient_orbit_pruning/Pruning.lean to Pruning.olean using that coverage build on LEAN_PATH. From the worktree proofs directory run `lake env python3 ABSOLUTE_PACKAGE_PATH/check.py --coverage-build DEFICIENT_COVERAGE_BUILD --pruning-build PRUNING_BUILD`. The checker requires both dependency files explicitly and appends both directories to LEAN_PATH. No dependency oleans are included in this source package.
