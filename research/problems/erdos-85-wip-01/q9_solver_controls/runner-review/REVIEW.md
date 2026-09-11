# Review2134 — PASS revised runner, software scope

codex-sol-2, 2026-09-11. Accepted runner SHA256: `18e8584b5d48cde9a7888789c34afeea4de7767bf77f8b4185cda36ea54c5eb0`.

Inspected serialized flock ownership, atomic ledger updates, unfinished-run refusal, process-group termination/reaping, solver time limit, aggregate 48-hour accounting, explicit single UNKNOWN requeue, scope restrictions, proof-output absence, complete CNF-model validation and pinned second-seat receipt gate. Metadata is intentionally opaque; mathematical map/graph binding belongs to the independent control review, not this wrapper.

Found and reproduced a first-SAT stop defect in the original version: a solver could print SAT and a complete valid model, then time out; UNKNOWN status allowed further launches. The revised version persists `sat_observed` independently of terminal status and gates every subsequent launch on a q9 observation. The reproduction now preserves UNKNOWN, validates the model, and refuses a subsequent launch. Mismatched exit handling is similarly conservative. Requeues now bind metadata/map hash as well as CNF and seed.

All eight producer software tests pass independently, including actual tiny Kissat SAT/UNSAT, timeout process reaping, invalid-model refusal, policy checks and changed-map requeue refusal. The independent SAT-then-timeout fixture passes against the revised pins. These fixtures use temporary ledgers and are not either graph control or a q9 experiment run.

The runner requires independent PASS receipts for both graph controls before q9 launches. A receipt still needs a real second-seat check of the exact decoded graph, cyclic action and binding to the solver assignment/map. No graph control was run by this review, and no existence/nonexistence or Lean result is claimed. The original reproduction files remain historical evidence; `check_fixed.py` and `fixed-results.json` refer to the accepted revision.
