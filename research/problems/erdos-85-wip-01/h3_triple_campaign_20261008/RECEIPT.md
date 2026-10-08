# Required per-attempt receipt and acceptance rules

Status: contract prepared; the cloud worker and collector are not yet implemented.
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
