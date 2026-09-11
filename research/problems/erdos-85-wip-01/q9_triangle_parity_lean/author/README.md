# Triangle-parity Lean review

Integration module proofs/Proofs/Erdos85TriangleParity.lean proves that, in a finite C4-free graph, a vertex whose every incident edge belongs to a triangle has a 1-regular induced neighbourhood and even degree. The contrapositive is stated separately for odd degree. This formalizes a local endpoint of the saturated-cross argument, not the complete mixed-orbit triangle divisibility or all-singleton quotient derivation.

Targeted repository Docker build passed on 2026-09-11 with terminal exit 0; new module built in 2.9 seconds. Limits: 8192 MB and 10 minutes; LEAN_SKIP_CACHE=true. A second Docker process independently compiled Audit.lean containing the full source plus three axiom prints, with read-only mounts, 4096 MB, two CPUs and timeout 120 seconds. It exited 0; all declarations depend only on propext, Classical.choice and Quot.sound. Raw output is in axiom-audit.json.

Audit mounts: integration worktree at /workspace:ro; lean-mathlib-cache at /workspace/proofs/.lake/build:ro; lean-mathlib-packages at /workspace/proofs/.lake/packages:ro; this directory at /audit:ro. Working directory /workspace/proofs, image lean4-arm64:v4.31.0, command timeout 120s lake env lean /audit/Audit.lean. Peer review should verify live/frozen equality and repeat direct source compilation.
