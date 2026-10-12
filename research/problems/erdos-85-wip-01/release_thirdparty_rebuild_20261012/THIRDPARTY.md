# Third-party-path cold rebuild (2026-10-12)

Purpose: repeat the accepted cold project build (`../release_cold_build_20261011/ACCEPTED.md`)
the way an outside checker would obtain the inputs. The 13 packed H7 (t>=1) certificates
are NOT copied from earlier builder worktrees; the builder fetches them with the public
recipe `proofs/scripts/fetch-h7-certificates.sh` (Requester Pays, `--request-payer requester`)
into a fresh worktree of the execution commit, and the runner's own input validation
then rehashes all 32 inputs against this plan.

Base: release assembly `87e58b130b5`; `proofs/` is byte-identical to the attempt-2
execution commit `afa46bc5078`. Same 893 sources, 32 inputs, expected exports, limits.

Runner changes relative to attempt 2 (copied from `../release_cold_build_20261011/`):
- `run.py`: `kill_group()` — no second SIGKILL after the first; an EPERM from
  `killpg` on an exiting group (macOS reports EPERM once only zombies remain; Linux
  reports ESRCH) is tolerated when the child is gone or exits within 5 s. Reproduced
  the old flake 4/120 in parallel stress on macOS; fixed runner 0/120.
- `capture.py`: runner folder derived from its own location instead of hard-coded.

Limitation: the builder's instance role and every local profile belong to the bucket
owner account. This run exercises the public script, the bucket policy
path and requester-pays flag end to end, but it is still not a download from a separate
AWS account.
