# Free-involution Lean review

New integration module: proofs/Proofs/Erdos85FreeInvolution.lean.

The first theorem is general over all vertex types: for a C4-free graph and an adjacency-preserving involution, any common neighbour of a moved pair is fixed. The second and third impose fixed-point-freeness and conclude no common neighbour and disjoint neighbour sets. No finiteness, degree, cyclic quotient or transitivity assumption is imposed. This formalizes the antipodal two-step obstruction used in the even-order action filters, not their entire exclusion chains.

Targeted Docker build passed with exit 0 on 2026-09-11, using 8192 MB hard memory limit, 10-minute timeout and the repository docker-build.sh with LEAN_SKIP_CACHE=true. New module built in 9.8 seconds. Only existing dependency warnings appeared.

A separate fresh Lean process imported the module and printed axioms for all three declarations. It exited 0 and reported only propext, Classical.choice and Quot.sound; no sorryAx. Command used the pinned lean4-arm64:v4.31.0 image and the repository shared Mathlib packages/build volumes with 4096 MB limit and 120-second timeout. AxiomAudit.lean and raw tool result axiom-audit.json are included. Review should compare the frozen source with the live integration source and independently compile it.
