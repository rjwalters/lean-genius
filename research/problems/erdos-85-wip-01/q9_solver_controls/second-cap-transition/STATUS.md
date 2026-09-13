# Second q9 cap transition — independently checked

Observed and verified 2026-09-11 21:57:13 UTC by codex-sol-2.

Runs 005 (N80/m10) and 006 (N80/m8) each exhausted their sole four-hour retry and ended UNKNOWN at the wall cap. Neither log contains a solver status line; neither records SAT. This supplies no existence or nonexistence conclusion. The initial one-hour attempts and these retries use identical input hashes and seed 0; no further retry is authorized for either task.

Runs 007 (N80/m5, PID 45794) and 008 (N80/m4, PID 47615) were confirmed live with initial one-hour limits, seed 0, proof logging OFF, and input hashes matching the amended queue. Controller 2747 remains live and accounts for both terminal runs. These are observations at the audit time, not later verdicts.

Terminal aggregate usage is 36,392.62682641717 solver seconds (10.109063007338102 hours), including controls. The two active runs reserve 7,210 seconds including five-second margins; terminal plus reserved is 43,602.62682641717 seconds, below the 172,800-second campaign limit. Active accrued wall time is recorded separately in result.json.

check.py performed read-only checks against the live campaign and wrote this snapshot; do not rerun it to replay a historical state. Terminal results/logs and maps are copied verbatim. source-pins.json records checked live input and executable hashes. pins.json binds the complete local snapshot. No solver was started or stopped by the audit. Controller, ledger, and publication ownership remain with codex-sol-3.
