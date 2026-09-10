# Phase B reducer with reviewed historical evidence

This integration candidate extends the crash-corrected reducer approved in review2013. It accepts the original four-tool dispatcher and the five-tool historical-overlay dispatcher. It never launches a solver or executes captured Python.

Historical evidence is accepted only from the exact 95-row overlay approved in review2009 and banked in 2bf321a03d. That SHA pins the original manifest, audit and native comparison dependencies. The helper independently checks the snapshot bytes against those hashes, reconciles the complete root evidence list and skipped IDs, and joins every historical row to the current index. Expanding to another historical case requires an explicitly reviewed new pin. This is inherited historical evidence, not a new proof replay or a claim about execution authenticity.

Rows without a fresh attempt can be HISTORICAL_VERIFIED_UNSAT. Fresh UNKNOWN, ERROR and INCOMPLETE states remain explicit with historical evidence attached. SAT observations or a different fresh CNF identity conflict with historical UNSAT and produce DISAGREEMENT. The flag `all_targets_crosschecked_unsat` still requires every current target to have fresh cross-checked UNSAT. Historical-only evidence cannot set it. Historical exclusions outside the current index are not revalidated.

Review2013's uniform SAT-alarm scan is retained: partial wrapper/solver/log evidence and published capped UNKNOWN or ERROR outcomes cannot hide a SAT observation behind an older UNSAT. Malformed or inconsistent evidence aborts the report. Every parsed artifact is bounded; output files are created exclusively.

Run `python3 -m unittest -v` here. Seventeen core tests use synthetic run fixtures. Six helper tests and three integration tests use already banked historical data under the integration worktree, with synthetic root receipts; no fixture is represented as a real solve. Those data-dependent tests currently identify the local integration research path explicitly. CLI arguments remain `--index PATH --index-sha256 SHA --run-dir RUN` (repeatable), `--output NEW_JSON` and optional `--tsv NEW_TSV`.
