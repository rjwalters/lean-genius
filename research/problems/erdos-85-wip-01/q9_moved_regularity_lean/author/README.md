# Moved-regularity Lean review

Integration Erdos85MovedRegularity.lean proves moved induced degree8 when its order is below64 in a finite C4-free minDegree9 graph under an adjacency-preserving map. The second theorem assumes original9regularity and proves the fixed-neighbour finset has cardinal1 for each moved vertex. No prime-order/bijectivity or total-cardinality assumption is required.

Uses accepted MovedDegree plus existing DistanceLayers regularity; the moved vertex parameter supplies nonemptiness. The second proof partitions its original neighbour finset into fixed/moved filters and identifies the latter with induced degree8.

Targeted Docker build passed exit0, new module2.2s, 8192MB and10m limits. An initial broad simp step was corrected to a definitional cardinality change; no theorem hypothesis changed. Separate full-source Audit.lean compiled exit0 and both axioms lists contain only propext/Classical.choice/Quot.sound. Raw output in compile.json.

Read-only Docker mounts: integration:/workspace:ro; lean-mathlib-cache:/workspace/proofs/.lake/build:ro; lean-mathlib-packages:/workspace/proofs/.lake/packages:ro; this directory:/audit:ro. Image lean4-arm64:v4.31.0,4096MB,two CPUs, working directory /workspace/proofs, command timeout120s lake env lean /audit/Audit.lean (with a space between timeout and120s). Independent review should compile the full body and verify live/frozen equality.

This provides the exact fixed/moved boundary contribution at moved orders60/63. It does not exclude those cases or formalize order-three fixed-count classification.
