# Terminal catch-up audit — 12 September 2026

PASS snapshot: 2026-09-12T17:11:11.224092+00:00

Audited 13 terminal runs: 009–020 and 022. Each ended UNKNOWN at its authorized wall cap, exit -15, with no SAT/UNSAT status line. Verified exact result/ledger equality, raw log hashes, local and source CNF/map identities against the plan, helper/solver hashes, seed/proof flags, and cap duration.

All ten planned tasks have exactly one initial attempt and one retry. Reconstructed launch accounting and concurrency from persisted timestamps agrees with the authorized limits. This reconstruction is not a contemporaneous observation of historical processes. Current process observation confirmed controller 2747 and only run021 solver 61295 live.

Terminal use: 158389.92595003848 seconds (43.99720165278847 hours). Current run021 full reservation including margin: 14405 seconds. Total terminal plus reservation: 172794.92595003848 < 172800 seconds.

Run022 allocation: floor(172800 − 151592.90168333054 − 14405 − 5) = 6797 seconds. It ended UNKNOWN after 6797.024266707944 seconds. Run021 is the sole remaining N80/m1 retry, capped at 14400 seconds; its start was 2026-09-12T13:55:17.313074+00:00.

UNKNOWN supplies no existence or nonexistence conclusion for N78 or N80. No new solver was launched or stopped by the auditor. Research freeze remains unchanged.

This directory is an unpublished scratch audit. check.py captures live state and must not be represented as an offline replay of this historical snapshot. pins.json binds the archived files; source-pins.json identifies large external input files and executables whose hashes were verified at capture. Raw solver logs are preserved verbatim.
