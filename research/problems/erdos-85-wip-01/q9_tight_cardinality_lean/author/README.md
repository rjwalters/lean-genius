# Tight-cardinality Lean review

Integration module proofs/Proofs/Erdos85TightCardinality.lean transports the existing containsC4_of_tight_minDegree theorem from Fin(k*(k-1)+1) to any finite vertex type with that cardinality. Its second theorem uses the existing asymmetric distance-layer bound and the transported equality obstruction to prove k*(k-1)+1 < card V for a nonempty C4-free graph with minDegree >= k >= 3.

No new friendship theorem proof is introduced. The explicit Nonempty hypothesis on the strict lower bound is essential. The equality obstruction itself needs no Nonempty assumption because its cardinal hypothesis supplies a positive order.

Targeted Docker build passed, terminal exit0, new module2.4s, 8192MB limit and10m timeout, LEAN_SKIP_CACHE=true. Separate direct-source audit compiled Audit.lean (full source plus axiom prints), terminal exit0, both axioms lists exactly propext/Classical.choice/Quot.sound. Raw output in compile.json.

Read-only Docker setup: integration worktree:/workspace:ro; lean-mathlib-cache:/workspace/proofs/.lake/build:ro; lean-mathlib-packages:/workspace/proofs/.lake/packages:ro; this directory:/audit:ro. Working directory /workspace/proofs, image lean4-arm64:v4.31.0, 4096MB memory/swap, two CPUs, command timeout 120s lake env lean /audit/Audit.lean. Please independently compare live/frozen source and compile the full body.

Applications: a nonempty C4-free induced graph with minDegree4 has at least14 vertices; with minDegree8 at least58. The latter tightens the moved-vertex bound and excludes moved cardinal57 in the order3 fixed-count analysis. Neither application proves global nonexistence at78/80 or solves Erdős85.
