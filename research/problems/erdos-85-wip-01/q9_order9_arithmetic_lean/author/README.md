# Kernel-checked order-nine determinant arithmetic

Erdos85OrderNineDeterminantArithmetic.lean proves that none of the128 products of the three displayed finite factor sets is a natural square. The finite sqrt certificate uses `decide +kernel`, not native_decide or a solver oracle. The public theorem uses Nat.sqrt_eq to rule out every n*n.

Targeted build completed2969jobs, new target1.0s, exit0. Direct compilation of the frozen source body and #print axioms also exited0; final theorem uses only propext, Classical.choice, Quot.sound. No sorry. Source-level proof and raw successful output are preserved here. The first ordinary decide attempt failed to unfold the sqrt expression; the final kernel-decide version is the successful source.

This formally verifies the arithmetic obstruction only. Character-space integrality, deficiency components, and graph-to-factor reduction remain paper/computational dependencies under separate review. No full order-nine graph exclusion is claimed by the Lean theorem itself.
