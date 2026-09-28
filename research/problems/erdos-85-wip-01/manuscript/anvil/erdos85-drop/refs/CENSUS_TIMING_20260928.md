# Residual-root census: timing joins, input-identity counts and the projection worksheet (2026-09-28)

Computed from the ledgers and run directories on Stripe (`artifacts/erdos85-sat49/h1-verdict-cloud-20260921/{,pass2,pass3,pass3b}/`, the Mac pilot `h1-verdict-pilot-20260921-claude/results.json`) by joining each residual root to its final attempt (a later pass overrides an earlier one). Receipts: `CENSUS.md`, `h1-census-table.tsv`, `h1-gap1288-audit.json`.

## Final-verdict pass per row (1,161 residual roots)

| Final attempt | Rows | Caps per solver |
|---|---:|---|
| Mac pilot (2026-09-21/22) | 24 | 4 h |
| Pass 1 (cloud, 2026-09-21/23) | 876 | 4 h |
| Pass 2 (2026-09-23/25) | 242 | 12 h |
| Pass 3 (2026-09-25/26) | 16 | 24 h |
| Pass 3b (2026-09-25/27) | 2 | 24 h |
| Pass 4 cube tree (Mac, 2026-09-26/27) | 1 | probe 1 h, leaves 24 h |
| **Total** | **1,161** | |

## Solver time of the 1,160 whole-instance UNSAT rows (final attempts only)

| Statistic | Kissat 4.0.4 | CaDiCaL 3.0.1 |
|---|---:|---:|
| Total core-hours | 2,704 | 2,996 |
| Median per row | 1.88 h | 1.99 h |
| 90th percentile | 4.1 h | — |
| Maximum | 21.9 h | 19.7 h |
| Rows above 4 h | 121 | 191 |
| Rows above 12 h | 6 | — |

Combined solver time of the census, including the cube tree (9.7 + 6.2 core-hours): about 5,716 core-hours. Time spent on attempts that later hit a cap and were rerun is not included in the per-row figures above.

## Input identity (emitted CNF versus the 2026-08 producer hash)

Every input preparation receipt (`preparation.json`) records `identity_basis`: `historical` when the frozen index carried a producer CNF hash and the freshly emitted CNF matched it byte for byte (the dispatcher refuses a mismatch), `new` when the index carried no producer hash. Over all 1,412 preparation receipts in the four cloud passes: **1,322 historical, 90 new** (pass 1: 1,042 historical + 90 new; pass 2: 261 historical; pass 3: 17; pass 3b: 2).

## Projection worksheet for the cube-partitioned certificate route (not a receipt)

Inputs: 2,704 Kissat core-hours for the 1,160 whole-instance rows (above); compact-LRAT growth of 5 to 6 GB per Kissat-hour and the kernel-check rate of about 0.5 MB gzipped per second from `CERT_BANK_STATS_20260926.md`; spot prices observed 2026-09-21 (c7g.16xlarge $0.65/h ≈ $0.010 per core-hour; r7g.2xlarge $0.15/h in the budget plan).

| Line | Arithmetic | Result |
|---|---|---:|
| Whole-instance certificate bytes | 2,704 h × 5.5 GB/h | ≈ 14.9 TB |
| Hardest rows' single files | 12–24 h × 5.5 GB/h | 60–130 GB each |
| Proof-logged re-solve + trim | ≈ 2.5 × 2,704 h | ≈ 6,700 core-hours |
| … cost on spot | 6,700 × $0.010–0.015 | $70–100 |
| Kernel checking | ≈ 2,900 job-hours ÷ 8 jobs per host | ≈ 360 host-hours |
| … cost on spot | 360 × $0.19 | ≈ $70 |
| Gzipped certificates (≈ 27% of compact size, as in the bank) | 14.9 TB × 0.27 | ≈ 4 TB |
| … cold storage | 4,000 GB × $0.004/GB-month | ≈ $16 per month |
| Whole-instance plan for comparison | replay $1,276 + retrieval $182 + gap-row production and checking at the same rates | $2,000–2,500 |
