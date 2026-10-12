# Cold-build attempt: terminal failure

> **Superseded.** This records attempt 1 only. The corrected attempt 2 completed and
> was accepted; see [ACCEPTED.md](ACCEPTED.md). The statements below describe the
> evidence state at the time of attempt 1.

The approved attempt did **not** complete the cold project build. This is a
failure receipt, not an acceptance audit.

- Job: `20261011T215126-commit-8d4f59c82e40-9322`.
- Execution commit: `8d4f59c82e40f08ae9377458779a68fde8a7ddc9`.
- Frozen plan SHA256: `b46f4095c15134c9e8e55f47edf024f16d5f68542ffc18c9aea3a081e92cca90`.
- Host terminal exit: **1**, 2026-10-12 03:01:47 UTC.
- Runner duration: 18,612.738 seconds (about 5 hours 10 minutes).
- Recorded completed modules: **460 of 893**; unfinished: **433**.
- Collection status: `FAILED_EVIDENCE_RETAINED`.
- Builder `i-04a61ff360a07bef2`: **stopped**, confirmed through the EC2 API
  after collection; see [instance-state.json](terminal-evidence/instance-state.json).

## Cause

The first H3 triple-part invocation failed in 0.064 seconds while loading its
native runtime plugin, before the proof check could run. The frozen runner
requested `initialize_proofs_Proofs_Erdos85H3TripleCompletionRuntime`; the
freshly compiled library exports
`initialize_Proofs_Erdos85H3TripleCompletionRuntime`. The extra `proofs_`
component in the requested initializer is a runner defect for this layout.

Evidence:

- [Failed invocation](terminal-evidence/logs/Erdos85H3TripleCompletionPart000.json)
  and [raw error](terminal-evidence/logs/Erdos85H3TripleCompletionPart000.log).
- [Exported symbols](terminal-evidence/plugin-symbols.txt), captured with
  `nm -D` against this attempt's freshly built shared library.
- [RUN.json](terminal-evidence/RUN.json), [host log](terminal-evidence/job.log),
  [host exit](terminal-evidence/job.exit), and
  [host commit](terminal-evidence/job.sha).

The runner stopped its five other active processes. Their receipts have
`stop_reason: STOP` and exit `-9`; these are interrupted checks, not additional
independent proof failures. H5 T2 parts06 and07 are among those interrupted.
The endpoint and its final axiom audit were not reached. The earlier accepted
builds and capstone audit remain separate evidence; this attempt neither
replaces them nor verifies the uncompleted cold closure.

## Retention and collection

The complete archive is retained outside Git at
`/Volumes/Stripe/lean-genius/artifacts/erdos85-cold-build-20261011/run-output.tar.gz`.
It contains the generated objects and C/plugin artifacts as well as the raw
receipts. Its size is 206,100,022 bytes and its SHA256 is
`1d28b1d39a99a8def5514ce7bb7487b0cf75b7366c117172376626fe59486211`.
The collector verified the host exit/commit, safely extracted the archive,
and checked the transferred plan against the frozen local bytes. Since the
exit was nonzero, it correctly did not run the success auditor.

The repository retains [CAPTURE.json](terminal-evidence/CAPTURE.json), all
raw process logs/receipts, the plan and runner record, and a
[full-bundle hash manifest](terminal-evidence/full-bundle-manifest.json).
The archive/object bundle has not been publicly uploaded.

The first collection invocation failed before creating a local output
directory because the container's `run-output` directory is root-owned.
The evidence-branch collector now uses `sudo -n cp` for the four original
host receipts; it leaves existing evidence ownership and contents unchanged.
The subsequent collection succeeded. All five offline collector tests pass.
This collection retry did not restart or resume Lean.

## Proposed correction, not an executed retry

[proposed-initializer-fix.patch](proposed-initializer-fix.patch) removes the
incorrect prefix from the runner's initializer constant. `git apply --check`
passes against the frozen source. The proposed spelling matches the actual
exported symbol, but the patched runner has **not** been tested in Lean.
The original `run.py` and `PLAN.json` remain unchanged as execution evidence.

Any future execution must have a newly generated, reviewed plan and separate
spending authorization. A plugin-load smoke check should precede the expensive
closure build. A partial continuation would not establish a fresh cold build.
No retry, resume, budget extension, or additional cloud build was performed.
The manuscript must not claim a completed cold project rebuild.
