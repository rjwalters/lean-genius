# Revised H7 estimate review, 2026-10-08

**RESOLVED at `c95a89eced3ac79a66d369e988dee86f78c61715`.** The author
confirmed the retained tables used `--boot 20000`, then changed the default
from 5,000 to 20,000 and documented the exact commands. `verify_fix.py`
independently transported that pinned source to the existing builder and
ran both commands without a `--boot` override, on Python 3.12.14.
Both JSON and Markdown output pairs reproduced byte for byte: revised
`[2864,5392]`, original `[2864,5216]`. `FIX_VERIFICATION.json` records the
source/output hashes, runtime and verifier hash. Reproduce with
`python3 -B research/problems/erdos-85-wip-01/h7_revised_estimate_review_20261008/verify_fix.py`.

The historical findings below remain evidence about the earlier default;
their numeric outputs have not been overwritten. The resolved issue was a
missing generation setting, not an arithmetic error or altered receipt.

## Earlier finding and retained evidence

**Point estimate and sample substitution PASS; published bootstrap interval
not reproduced with the committed defaults.** Inspected commit:
`8afe018d8b0587ff2f21f31624161a227eeb99f8`.

Only the two previously capped sample items were replaced. Their replacement
records exactly match the independently reviewed follow-up receipts, with the
original sample index/seed and an explicit `replaces_capped_sample` annotation.
All other 1,426 items and the sample ordering are unchanged. The follow-up
bytes have SHA-256
`353f949b37a01018258f653e061d7b155cb342633874db1742bab4f9e769c8ea`, matching
`../h7_capped_followup_review_20261008/evidence/raw-followup.jsonl`.
The original censored sample and estimate remain separate artifacts.

| Quantity | Published | Recomputed |
|---|---:|---:|
| Revised leaf CPU-hours | 3,915 | 3,915.351700597328 |
| Revised streamed LRAT, decimal TB | 20.4 | 20.4423127612789 |
| Revised bootstrap 5%–95%, CPU-hours | 2,864–5,392 | 2,865–5,369 |
| Original bootstrap 5%–95%, CPU-hours | 2,864–5,216 | 2,867–5,208 |

`audit_cloud.py` independently recomputes the stratified sample means and
bootstrap using 5,000 replicates and `random.Random(1)`, the committed
estimator's defaults. Both archived and raw producer row orders give the
same intervals, ruling out archival ordering as the explanation. The
independent run used Python 3.9.25 on the existing builder.

The exact committed `estimate.py` was also run on the builder with Python
3.12.14, the committed input/sample bytes, and explicit `--boot 5000`.
It returns the same revised interval as the independent implementation.
Every published per-cube field except `cpu_h_lo` and `cpu_h_hi` matches.
All other top-level fields match except the interval and the derived
on-demand dollar interval: `[180,247,340]` published versus `[181,247,338]`
recomputed. The spot dollar triple remains `[50,68,93]` after rounding.
Dollar arithmetic uses the estimator's rate/utilisation assumptions; this
review does not verify current cloud prices or actual billing.

This is a reproducibility finding, not evidence that the underlying receipts
or point estimate are wrong. The generation command/replicate count for the
published interval was requested from the author (room 52896). A different
replicate count may explain it; that is not established here. The estimator
output does not currently record that setting. Before treating the exact
published interval as reproduced, retain the generation command and
bootstrap configuration, or regenerate the tables under a recorded setting.

A bounded check with `--boot 2000` returned `[2859,5383]`, also different
from the published interval. `EXACT_ESTIMATOR_2000.json` retains the output;
reproduce with `run_review.py exact 2000`. No further configuration search
is implied; the author can supply the generation command directly.

`SNAPSHOT.json` identifies each input by pinned Git path and SHA-256, avoiding
duplicate receipt archives. `AUDIT.json` retains the independent results;
`EXACT_ESTIMATOR.json` retains the exact estimator output and field differences.
From a checkout containing the pinned commit, reproduce with:

```sh
python3 -B research/problems/erdos-85-wip-01/h7_revised_estimate_review_20261008/run_review.py independent
python3 -B research/problems/erdos-85-wip-01/h7_revised_estimate_review_20261008/run_review.py exact
```

The runner transports Git snapshots; computation executes only on the
existing builder. It does not change cloud worktree refs or launch Lean,
solvers, instances, or a campaign. The reproducible runner uses Python 3.12
for both modes; the retained initial independent result records Python 3.9.
The bootstrap is conditional on the observed sample, including two 4 GB
follow-up attempts amid 2 GB original attempts. It cannot bound unseen tail
costs or establish that all remaining leaves fit the default heap/cap.
