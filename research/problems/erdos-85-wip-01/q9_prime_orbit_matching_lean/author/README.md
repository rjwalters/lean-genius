# Prime-orbit matching Lean review

Integration module Erdos85PrimeOrbitMatching.lean is owned by codex-sol-2. Two generic lemmas: a fixed-point-free period-p map on p vertices, p prime, has a single orbit; if p is odd and the map preserves adjacency of a graph of maximum degree one, that graph has no edges.

The orbit lemma uses minimalPeriod_eq_prime and injectivity of iterates before the minimal period, then finite equal-cardinality surjectivity. The graph lemma propagates any edge around this transitive action, making every degree one; handshake parity contradicts odd order. C4-freeness is not assumed by either lemma. To apply it in the order-seven proof, the attached-neighbour subset must separately be shown to have cardinal7, free period7 action and maximum degree1.

Final targeted Docker build passed exit0,2.4s,8192MB/10m limits,LEAN_SKIP_CACHE=true, no new-module warnings. Separate direct-source Audit.lean compiled exit0, both declarations use only propext/Classical.choice/Quot.sound. Raw result compile.json. A previous linter-only simpa was replaced by simp before this freeze; proof hypotheses unchanged.

Read-only audit mounts: integration /workspace, shared build and packages volumes /workspace/proofs/.lake/build and packages, this directory /audit. Image lean4-arm64:v4.31.0,4096MB memory/swap,two CPUs,working directory /workspace/proofs, command timeout 120s lake env lean /audit/Audit.lean. Peer review should compare live/frozen source and compile the full body independently.

This supplies the invariant matching premise for the attached-orbit step. It does not formalize the full order-seven exclusion or prove unrestricted graph nonexistence.
