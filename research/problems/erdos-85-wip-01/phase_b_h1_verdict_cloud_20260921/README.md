# H1 verdict-only census on AWS spot (board goal #44)

2026-09-21, claude. **SINGLE-SEAT, Sol re-audit pending.** Operator authorization: up to
$200 total on AWS for verdict-only H1 solving. No certificates, no proof logging, no Lean
replay in the cloud.

## What runs

The 1,161 fresh H1 Phase B roots split into the frozen 24-case pilot (runs on the Mac
host) and the other 1,137 (`queue-1137.ids`, sha256 `d9e4548f…6fe87`, one ID per line,
sorted). Each cloud slot runs the **reviewed, unchanged** wrapper

    sat49/dispatch_h1_residual_verdict_only.py --config …/config.draft.json \
      --config-commit bf95b3937e… --execute --case-id <ID> --workers 1 --output-dir <new dir>

from a checkout of `erdos85/integration`. So the same banked-dependency checks, the same
pinned emitter (`v2cnf`, sha256 `4bd9604c…`) inside the same pinned Docker image
(`sha256:a5ca6c4e…`), the same MATCH check, the same Kissat-then-CaDiCaL policy with
14,400-second caps, and the same receipt schema apply. One case gives one run directory,
which the reviewed `summarize_phase_b_verdicts.py` reads like any host run directory.

New code in this directory only moves work and bytes around:

- `node_bootstrap.sh`: installs Docker (containerd image store, so the image ID survives
  save/load), loads the image, installs the emitter, builds or adopts one shared build of
  Kissat `rel-4.0.4` and CaDiCaL `rel-3.0.1`, self-tests the S3 claim primitive, runs the
  wrapper's dry run and requires `selected_cases = 1161`. Any failure uploads the log and
  powers the node off.
- `node_worker.py`: one slot per CPU. Claim = S3 `PutObject If-None-Match: *` on
  `claims/<ID>`. After the wrapper exits, the whole run directory is uploaded as
  `results/<ID>.<instance>.<epoch>.tar.zst` plus a small `ledger/…json`. It never reads a
  CNF or classifies a log.
- `controller.py` (Mac): creates the scoped role, a no-ingress security group and the
  launch template; uploads freight; requests at most four spot instances; syncs receipts
  to Stripe; releases claims held by dead nodes; estimates spend and stops everything at
  $170.

## Differences from the Mac host runs (for the paper's methods text)

- Hosts are AWS Graviton (arm64) spot instances running Amazon Linux 2023. Solver
  binaries are built from the upstream release tags on the first node and shared by hash;
  each run directory records the binary path, sha256 and version.
- The emitter path and `/usr/local/bin/docker` are recreated on the node so the reviewed
  materializer runs unmodified.
- Concurrency is up to 64 one-worker wrapper processes per node instead of one
  four-worker process.

## Stop rules

`control/STOP` ends new claims. SAT_CANDIDATE or DISAGREEMENT writes `control/ALARM-<ID>`
and STOP. A slot stops at its first ERROR; a node stops claiming at six. ERROR cases are
not retried automatically. Cap hits (UNKNOWN) are final and are reported as open.

## Cost backstops

Controller hard stop at an estimated $170; spot max price $1.30/h per instance; the fleet
request expires after 30 h and terminates its instances; every node powers off after 30 h
and when idle; at most four instances per launch call (256 of the 300-vCPU spot quota).

## Cleanup (punchlist E1)

IAM role and instance profile `Erdos85VerdictWorker`, security group
`erdos85-verdict-noingress`, launch template `e85-verdict-20260921`, S3 prefix
`sat49/verdict-only-20260921/` (freight can be deleted after the run; receipts are synced
to Stripe `artifacts/erdos85-sat49/h1-verdict-cloud-20260921/`).

## Pass 2: long caps for the pass-1 cap hits (board goal #45, 2026-09-22)

About 18% of pass-1 rows stop at the 14,400 s Kissat cap. Robb: raise the cap on a second
pass. `config.longcap.json` is `config.draft.json` with H1 caps of 43,200 s for both solvers
and no `h1_residual` block; it runs through the reviewed base dispatcher
`dispatch_verdict_only.py --case-id ID --workers 1` (the residual wrapper hard-codes the
14,400 s policy, so it cannot be reused). After pass 1 is complete:

    python3 -B build_pass2_queue.py <commit-that-banked-config.longcap.json>
    git add queue-pass2.ids pass-pass2.json && git commit && git push   # then re-run with that commit
    python3 -B controller.py --pass pass2 setup --commit <commit>
    python3 -B controller.py --pass pass2 launch 1      # canary, then up to 3 more
    python3 -B controller.py --pass pass2 watch

Pass 2 uses S3 sub-prefix `pass2/`, Stripe subdirectory `pass2/`, tag and launch template
`e85-verdict-20260921-pass2`; freight and solver binaries are shared with pass 1. Worst case
per row is 24 h; nodes and fleets still stop at 30 h. Rows that still hit the cap are open.
