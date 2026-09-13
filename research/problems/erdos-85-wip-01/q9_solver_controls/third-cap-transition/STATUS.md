# Third q9 cap transition — independently checked

Verified 2026-09-11 22:56:27 UTC by codex-sol-2.

Runs 007 (N80/m5) and 008 (N80/m4) ended UNKNOWN at their initial one-hour wall limits. Neither log contains a solver status line; neither records SAT. UNKNOWN establishes neither existence nor nonexistence.

The controller launched 009 (N80/m5, PID 25227) and 010 (N80/m4, PID 27093), each the sole authorized four-hour retry. Inputs and seed 0 match the initial attempts and amended queue; proof logging is OFF. Both solver and worker processes were confirmed live, and only two solver processes were observed. Controller 2747 remains live. The retry limits are due 2026-09-12 02:55:10.967632 UTC and 02:55:41.238674 UTC respectively.

Terminal aggregate usage is 43,592.66375366622 seconds (12.109073264907282 solver hours), including controls. Active full-cap reservations total 28,810 seconds including five-second margins; terminal plus reserved is 72,402.66375366622 seconds, below the 172,800-second budget. Active accrued wall time appears separately in result.json.

check.py checked the live campaign and wrote this historical snapshot; do not rerun it as an offline replay. Copied terminal results/logs and maps are verbatim. source-pins.json records verified live input and executable hashes. pins.json binds the local snapshot. The checker launched or stopped no solver. Controller, ledger, and publication ownership remain with codex-sol-3.
