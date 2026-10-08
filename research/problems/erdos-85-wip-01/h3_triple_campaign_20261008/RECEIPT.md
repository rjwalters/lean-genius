# Required per-attempt receipt and acceptance rules

Status: the artifact-validation component and single-attempt worker are
implemented and metadata-tested. Full and deficient non-native worker preflights
have passed independent host/artifact audits (see README and their evidence
directories). Production worker execution and the independent
host execution/provenance collector remain readiness gates.
The planner's output is not a proof receipt and cannot complete a campaign.

A receipt is immutable and belongs to `(manifest_sha256, case_id, attempt_id)`.
`attempt_id` must be unique across nodes, slots, restarts, and interrupted attempts.
Each attempt retains these fields and artifacts:

- Schema `erdos85-h3-triple-receipt-v1`; manifest SHA-256, case ID, branch,
  representative indices and compact parameters; worker source commit and
  source hashes; pinned container image digest; Lean toolchain and dependency
  snapshot hashes; instance identity, slot and unique attempt directory.
- Requested memory/CPU limits and wall cap; actual container limits; UTC start
  and finish; authoritative container exit and terminal state. A missing exit
  is `UNKNOWN`, never a timeout or permission to retry by itself.
- Four ordered module records: Inputs, Membership, Certificate, Consumer.
  Each has the exact command, exit, source/object/log hashes, requested and
  parsed axiom exports, wall time, user/system CPU and maximum RSS. The Linux
  per-process/children maximum RSS is not aggregate concurrent node memory.
- Sources, raw logs, individual module receipts, `.olean` objects and the
  outer job log/exit artifact. Retain certificate objects immediately on
  success, before attempting Consumer; a consumer failure must not force the
  native certificate search to run again.

Membership must precede Certificate. Its `member` and `input_identity` exports
must match the source and use only `propext`, `Classical.choice`, `Quot.sound`
(or a subset). Certificate must export exactly `<namespace>.rejected`, with
those three plus exactly `<namespace>.rejected._native.native_decide.ax_1_1`.
Consumer must export `<namespace>.representative_rejected` and `.no_joint`,
with exactly that same axiom set. Reject `sorryAx`, any other native axiom,
missing/extra/duplicate exports, changed artifacts, incomplete inventories,
wrong commands, and evidence from a different manifest or toolchain.

The collector verifies the actual retained artifacts and independently parses
compiler logs. It must not accept a worker's `status=PASS` or a JSON list of
axioms without this check. An accepted result is `AUDITED_PASS`; each prior
pilot credit instead references its immutable old receipt, audit, exact case,
identity proof and native object. Old pilot namespaces need not match new
campaign namespaces, and their objects must not be relabeled as new builds.

`validate_artifacts.py` implements the artifact part of this contract. Its input
is an externally pinned manifest and recorded attempt root, an attempt-level
`RUN.json`, and `<case-id>/<module>.{lean,log,olean,run.json}`. It requires all
four stages in order and regenerates their exact source bytes. The receipt uses
`schema=erdos85-h3-triple-receipt-v1`, `production_native_search=true`,
`manifest_sha256`, `case_id`, `attempt_id`, `recorded_root`, and `results`.
Module records follow the existing timing fields and include `stage`, `module`,
`case_id`, exact command, artifact hashes and parsed exports. Inputs/Certificate
commands use `<recorded-root>/source-root/Proofs` and the private complete
`<recorded-root>/library`; Membership/Consumer use `<recorded-root>/<case-id>`.
The worker's textual status is never sufficient evidence.

The component returns only `ARTIFACTS_VALID`, never `AUDITED_PASS`. It does not
parse or type-check an `.olean` itself; its hash binds retained bytes to the
recorded compilation. Authentic execution and dependency provenance remain
mandatory independent host checks. The validator executes no Lean or shell
commands, launches no retries and changes no claims. `--certificate-only`
validates the first three stages even if Consumer is absent or failed, returning
`CERTIFICATE_ARTIFACTS_VALID` with `retry_authorized=false`. This preserves a
recovery candidate; it does not authorize work while the old process may live.

## Worker launch and cache inputs

The launch host prepares `erdos85-h3-triple-launch-v1` with `mode` (exactly
`preflight` or `production`), `attempt_id`,
`case_id`, `manifest_sha256`, `recorded_root`, the 40-character `execution_commit`,
an immutable `image_id` (`sha256:...`), `instance_id`, `slot`, and `limits`
(`memory_bytes`, `cpu_quota_us`, `cpu_period_us`, `wall_seconds`). Limits must be
positive integers, at most 16 GiB, two CPUs and 7,200 seconds. The worker checks
the cgroup quota and memory limit against these exact values and requires zero
swap. It also checks `code_sha256` for exactly worker.py, validate_artifacts.py,
common.py and manifest.py, `cache_inventory_sha256`, and `inherited_lean_path`.
The host must independently verify these assertions; a worker echoing an image
or commit string is not evidence that those inputs were executed.

The pinned cache inventory uses `erdos85-h3-triple-cache-v1`,
`manifest_sha256`, the manifest's exact `base_receipts`, and `roots`. Full cases
require `library`, `full_base`, `full_final`; deficient cases require `library`
and `deficient_base`. Each root has an absolute in-container `path` and a
complete relative-file-to-SHA-256 `files` map. Symlinks, missing/extra/changed
files, incomplete generic dependencies and pre-existing campaign files are
rejected. The host must establish the cache's approved source/toolchain and
audited census provenance before pinning it. The inventory itself does not
prove that arbitrary cached `.olean` bytes came from the intended source.

The worker never builds prerequisites or writes the shared library. It copies
the complete approved library and writes generated objects only in its private
attempt directory. Census roots and package/toolchain mounts must be immutable
for the attempt; host launch and collection must enforce and check that fact.
The host's hard outer wall cap is required in addition to the worker's compiler
deadline, since Python hashing and staging are not a container lifetime limit.

A successful worker result is only `WORKER_PASS`. The implemented worker does
not yet support consumer-only continuation; the artifact validator can establish
the retained certificate prefix for a future continuation implementation.
Missing terminal evidence remains `UNKNOWN`, even if `WORKER_PASS` is present.

Preflight mode compiles Inputs and Membership only. It emits the distinct
`erdos85-h3-triple-preflight-v1` schema with `production_native_search=false`
and successful status `PREFLIGHT_PASS`. The artifact validator requires an
explicit `--preflight-only` request and exactly those two ordered stages;
production and certificate-prefix validation reject preflight receipts.
Preflight cannot receive campaign rejection credit. It still requires the same
source/cache pins, hard cgroup limits and independent host execution audit.

States are `PENDING`, `CLAIMED`, `RUNNING`, `CERTIFICATE_RETAINED`,
`AUDITED_PASS`, `TIMEOUT`, `OOM`, `ERROR`, `UNKNOWN`, and `ALARM`.
Timeout/OOM/compiler failure/partial upload never prove rejection. A native
check evaluating to true is an alarm for mathematical investigation; do not
replace it with a solver timeout label. Claims only leave active states on
authoritative terminal evidence. Lease expiry or lost SSH alone is insufficient.

A duplicate successful attempt is acceptable only as additional evidence for
the identical case/formula/trust contract; never overwrite either artifact
bundle. Conflicting results or source hashes raise an alarm. The campaign is
complete only when the exact manifest ID set is covered by audited current
results or approved prior credits, with zero missing or unknown cases. A
separate cloud-compiled aggregation must connect those results to the full
and deficient graph witnesses; receipt completeness alone is not H3 exclusion.
