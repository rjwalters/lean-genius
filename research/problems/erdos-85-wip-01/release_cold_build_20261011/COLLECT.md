# Terminal collection

The execution branch remains frozen. The collector is on the separate
`erdos85/cold-build-evidence-20261011` branch and does not modify any running
proof or runner source.

- Job: `20261011T215126-commit-8d4f59c82e40-9322`
- Execution commit: `8d4f59c82e40f08ae9377458779a68fde8a7ddc9`
- Plan SHA256: `b46f4095c15134c9e8e55f47edf024f16d5f68542ffc18c9aea3a081e92cca90`
- Start: 2026-10-11 21:51:26 UTC; outer timeout: 580 minutes.
- Dedicated volume: `lean-build-e85-cold-20261011-2146` (empty before preflight).
- Preflight: `20261011T215026-commit-8d4f59c82e40-8471`, exit 0.
- Earlier preflight `20261011T214656-commit-498a23193c85-6566` failed before
  compilation on container-inaccessible Git metadata. The identity fix uses
  frozen file hashes plus the host's commit receipt; it does not skip identity
  validation.

Only after the job has a terminal host `exit` receipt:

```sh
python3 -B research/problems/erdos-85-wip-01/release_cold_build_20261011/capture.py \
  --job 20261011T215126-commit-8d4f59c82e40-9322 \
  --commit 8d4f59c82e40f08ae9377458779a68fde8a7ddc9 \
  --output /Volumes/Stripe/lean-genius/artifacts/erdos85-cold-build-20261011
```

The collector refuses a missing exit receipt, a wrong host commit or an
existing output directory. It runs with `E85_NO_AUTOSTART=1`, so collecting
does not restart a stopped builder. It preserves the original host log,
specification, commit and exit record, downloads the full output archive,
rejects unsafe archive paths/links, and runs the read-only local auditor only
for an exit-zero bundle. The local repository must still contain the frozen
source/config/runner bytes and all 32 hash-verified input files. It writes
`CAPTURE.json` only after those checks succeed (or with an explicit failed-run
status when retaining a terminal failure). A failed transfer or audit is
not a pass, and never authorizes another build attempt.

The prior accepted dependency objects total about 3.26 GB, so retain the full
download outside Git. Bank the compact receipt, raw compiler/job logs and
hash manifest in the repository; leave the large object/archive files on the
artifact volume. No public upload of the fresh object bundle is implied.

After capture/audit, inspect the result and coordinate acceptance with Claude.
Stop the builder promptly when this attempt is terminal and the evidence is
retained. The collector does not itself stop the host, and does not reset the
watchdog, resize, retry, resume or extend the attempt. Any incomplete result
stays incomplete in the paper.
