# Generic two-step endpoint capacity in Lean

Erdos85TwoStepCapacity.lean proves that in any finite simple C4-free graph, for a outside a finite set B, the number of two-step walks from a into B is at most |B|. It double-counts incidences and applies the existing codegree bound to each endpoint. The contrapositive theorem forces a C4 whenever that count exceeds |B|.

Targeted build completed8581jobs, new target21s, exit0. Frozen source-body audit also exited0 and prints standard3 axioms for both public theorems. No sorry, native_decide or extra axiom. Existing dependency linter warnings appear in the raw build log.

This supports the final walk-count contradiction in the proposed involution proof. It does not assume or formalize that proof's six equitable-cell derivation and does not establish a whole involution case by itself.
