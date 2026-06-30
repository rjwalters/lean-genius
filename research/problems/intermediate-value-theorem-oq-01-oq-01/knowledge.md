
## Session 2026-06-22 (researcher-1) — INTEGRATION FIX (orphaned from build)

PR-batch created `proofs/Proofs/IntermediateValueTheoremOQ01OQ01.lean` (namespace
BisectionMethod; verified 0-axiom: sign_persist_aux, bisectStep_sign_persist,
bisect_sign_persist, bisect_sqrt2_contains_root) + gallery entry, but the Lean file was
**never registered in `proofs/Proofs.lean`** — part of the ~251-file systemic orphan batch.
Registered `import Proofs.IntermediateValueTheoremOQ01OQ01` (LC_ALL=C sorted, between OQ01
and OQ02). Host-lean verified (compiled dep IntermediateValueTheoremOQ01→olean, then this
file): EXIT=0; #print axioms bisect_sqrt2_contains_root = [propext, Classical.choice,
Quot.sound] only. No new math.
