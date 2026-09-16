# H1 v3 worker timing from original ledger lines

Goal #41 gap-solve sizing check, 2026-09-16. This measures **completed v3 worker jobs**, not the unresolved 1,288 capacity slots. No solver was started and no certificate object was read. The read-only fetch was 645 small ledger objects (372,359 bytes total) from `s3://2am-erdos85-certs/sat49/campaign-20260825/h1-fleet-v3/ledger/` using the configured `2am-admin` profile. The local directory is `/tmp/erdos85-h1-v3-ledger-sol2-20260916/`; it is a disposable copy, not proof evidence.

## Reconciliation and method

The frozen [`v3_ledger_tag_status.tsv`](../closure-inventory-evidence/h1-source/v3_ledger_tag_status.tsv) has SHA-256 `aaf507322edd75997be3b8e0a67f6090124b8ff00a1f229565bc7ab9cd0526fe`. All 596 unique frozen tags appeared in the downloaded lines; the other 49 live lines were excluded. For all 596, tag, timestamp, profile, local index, verdict, return code and node matched the frozen table exactly. For the 574 `UNSAT` rows, trim verdict, upload status and compact gzip SHA-256 matched as well. The frozen rows split into 574 verified, uploaded UNSAT and 22 UNKNOWN. The concatenation of each downloaded filename stem, NUL byte and file bytes in sorted filename order has SHA-256 `020c66b50cc92fb8db521b7ceffcb86c075028b74f99595c421e01c8d45f9076` across all 645 files.

The frozen worker script [`h1_fleet_worker.sh`](../closure-inventory-evidence/h1-source/freight/h1_fleet_worker.sh) sets `T1` immediately before Kissat, `T2` after it exits, and `T3` after `drat-trim`; its ledger fields are `solve_s=T2−T1` and `trim_s=T3−T2`, in integer wall seconds. Quantiles below use nearest-rank order statistics. The worker's `cap_s` was 14,400 seconds on every frozen solved row and all 22 UNKNOWN rows.

| Profile | Verified rows | Kissat median | Kissat p90 | Kissat max | Trim median |
|---:|---:|---:|---:|---:|---:|
| 0 | 47 | 4,181 s | 7,439 s | 9,875 s | 6,181 s |
| 1 | 149 | 4,042 s | 7,129 s | 11,662 s | 6,129 s |
| 2 | 235 | 3,981 s | 7,004 s | 13,705 s | 6,286 s |
| 3 | 107 | 4,251 s | 7,741 s | 11,050 s | 7,002 s |
| 4 | 36 | 3,315 s | 6,871 s | 10,934 s | 5,112 s |
| **All** | **574** | **4,011 s** | **7,129 s** | **13,705 s** | **6,200 s** |

Across the 574 completed rows, Kissat `solve_s` has mean **4,539 s** (1.26 h), p99 **10,897 s**, and sum **723.7 host-hours**. Proof trimming has mean **7,102 s** (1.97 h), p90 **11,739 s**, and sum **1,132.3 host-hours**. Emit, solve and trim combined have mean **11,662 s** (3.24 h), median **10,246 s**, p90 **19,105 s**, and sum **1,859.4 host-hours**; upload and queue time are outside that sum. All 22 UNKNOWN rows reached the 14,400-second Kissat cap (profiles 0/1/2/3: 6/6/8/2).

## Planning consequence

The prior 10.2-hour median claim-to-finish measurement is a **pipeline interval**, not a Kissat runtime. Using it as a per-slot solver estimate overstates runtime on the completed sample. Conversely, the 574 completed rows were selected by finishing and validating; they do not estimate the remaining gap tail. In particular, the 22 capped UNKNOWN rows and never-claimed gaps give direct evidence of censoring. Multiplying the 1.26-hour completed mean by 1,288 would be an unsupported budget quote. The next cost estimate needs actual verdict-only runtimes on a bounded, representative sample of the unresolved slots, followed by proof-logged/trim measurements for those that are UNSAT. Keep verdict-only, proof production, and Lean replay as separate cost lines.
