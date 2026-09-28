# Certificate-bank statistics used by the cost-to-verify section (computed 2026-09-26)

Source: the UNSAT ledger lines of the 2026-08 H1 certificate fleets, `s3://2am-erdos85-certs/sat49/campaign-20260825/{h1-fleet,h1-fleet-v2,h1-fleet-v3}/ledger/*.line` (13,113 + 12,765 + 645 lines) plus the host ledger `artifacts/erdos85-sat49/campaign-20260825.noindex/ledger/h1.ledger` (393 UNSAT lines). Each UNSAT line records `solve_s` (Kissat seconds), `drat_bytes`, `raw_lrat_bytes` and `compact_bytes` (compact LRAT after `compact_h1_v2_lrat.py`). Parsed with a 20-line Python script in the wrap-up session (memory note 2026-09-26); rows without all size fields were skipped.

| Statistic | Value |
|---|---:|
| UNSAT rows with sizes | 12,102 |
| Kissat solve time, median / p90 / max | 837 s / 2,816 s / 13,705 s |
| Compact LRAT, median | 1.2 GB (1,214 MB) |
| Compact LRAT, p90 | 4.0 GB (4,045 MB) |
| Compact LRAT, max | 26.5 GB (26,522 MB) |
| Compact LRAT, total | 22.6 TB (22,579 GB) |
| Raw LRAT, median / max | 1.2 GB / 26.9 GB |
| DRAT, median / max | 1.1 GB / 19.7 GB |

Certificate growth per solver-hour (median compact MB per Kissat-hour, by solve-time bucket):

| Solve time | Rows | Median compact LRAT | MB per Kissat-hour |
|---|---:|---:|---:|
| 0–15 min | 6,383 | 588 MB | 5,316 |
| 15–60 min | 5,353 | 2,342 MB | 5,039 |
| 60–120 min | 294 | 8,420 MB | 6,403 |
| 120–240 min | 72 | 15,778 MB | 6,167 |

So compact LRAT grows at roughly 5 to 6 GB per Kissat solve-hour across the range.

Kernel-check throughput: the replay budget plan (`H1_REPLAY_SPOT_16_BUDGET_PLAN_20260916.md`, `h1_replay_fleet_costs_20260910.json`) models 984 s of Lean replay per certificate at a reported mean of 509 MB gzipped (pilot 346 MB), i.e. about 0.5 MB of gzipped certificate per second, with one replay process per 64 GB `r7g.2xlarge` host; 12,019 ready inputs → 4,831 byte-weighted compile box-hours → about $1,276 of spot infrastructure and 17 ideal allocated days on 16 hosts (31.5 planned days with the 25% non-compile and 10% spot-loss factors). Gzipped bank size on S3: about 6 TB (6.06 TB retrieval pass at $0.03/GB ≈ $182).

Cube-certified route projection (2026-09-26, session analysis, not a receipt): re-solve the 1,161 residual roots with proof logging and trimming ≈ 2× to 2.5× the measured 2,700 Kissat core-hours ≈ 6,700 core-hours (about $70–100 on spot at $0.01–0.015 per core-hour); kernel checking ≈ 2,900 job-hours packed eight jobs per 8-vCPU host ≈ 360 host-hours (about $70); gzipped certificates ≈ 4 TB (about $16 per month in cold storage). Whole-instance plan for comparison: about $2,000–2,500 (replay $1,276 + retrieval $182 + gap-row production and checking at the same rates).
