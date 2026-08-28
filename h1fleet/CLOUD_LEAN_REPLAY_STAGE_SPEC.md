# H1 cloud Lean replay stage specification

Status: **DRAFT — editor sign-off required before launch or cloud spend**

This stage consumes the compact LRAT objects produced by the H1 SAT fleet and
turns each one into an independently cold-compiled Lean module.  It is a
separate stage from SAT solving: Lean replay must not share a 128 GiB node with
`kissat`, `drat-trim`, or compaction.

The design generalizes the already audited 122-module external-overlay replay.
That run cold-compiled 122/122 modules, used a self-contained copy of the base
overlay (not live symlinks into a changing Lake build), stopped on import or
compile failures, kept per-module logs and accepted markers, compiled the
aggregate bank, and audited `#print axioms`.  Its durable audit receipt was
`da375ec9686c117ab7efb5f0f052f013726612f5221282cfebdebe552946748a`.

## 1. Preconditions and immutable inputs

The stage may launch only after an editor-approved replay freight manifest pins:

- the exact Lean 4.31 toolchain and platform/AMI or image digest;
- the repository commit and complete, copied external overlay (including every
  imported `.olean`), with a deterministic manifest of relative path, bytes,
  and SHA-256;
- the per-tag Lean source generator/module template and their SHA-256 values;
- the H1 inventory manifest and the Lean-exact CNF emitter identity used by the
  SAT fleet;
- the worker, receipt schema, aggregate generator, and audit script hashes;
- the S3 bucket, campaign prefix, instance role, instance type, EBS shape, and
  concurrency.

Certificate input for tag `<tag>` is exactly:

```text
s3://2am-erdos85-certs/sat49/campaign-20260825/h1/<tag>.compact.lrat.gz
```

Before generation, record the object's key, ETag, version id if one ever exists,
content length, last-modified time, metadata, and SHA-256 of both the gzip object
and decompressed compact LRAT.  Validate gzip integrity, require a final LRAT
empty-clause derivation, and require `<tag>` plus the CNF hash to agree with the
authoritative coverage/inventory manifest.  A missing or divergent identity is
a hard quarantine, never a best-effort replay.

## 2. Node and overlay layout

Use a dedicated memory-optimized replay node in `us-east-1`, adjacent to the S3
bucket, with at least 4 TB of fast working EBS.  The measured 122-module run used
5–7.5 GiB per Lean process, so a 128 GiB node starts at `P=16`; raise concurrency
only after observing peak RSS and retaining at least 20% memory headroom.  Set
`maxHeartbeats 0` in the generated source as required by the audited bank.

On boot:

1. Verify the freight archive and every manifest entry before execution.
2. Materialize a read-only, self-contained base overlay on local EBS.  Copy
   imported `.olean`s; do not symlink to a mutable checkout or shared Lake
   output.  The prior replay showed that mutable symlinks can turn unrelated
   builds into false import failures.
3. Run a cold preflight on one known certificate with the exact production
   generator and compile command.  Require source generation, Lean exit zero,
   nonempty `.olean`, receipt validation, and the expected axiom classification.
4. Write `bootstrap.ok` only after that exact preflight passes.  No worker may
   start before it exists.

Each tag gets isolated `work/<tag>/`, `logs/<tag>.log`, and output paths.  Workers
must never write into the read-only base overlay.  A tag is resumable from its
accepted receipt; a stale in-progress claim is recoverable, while a failed tag
is quarantined and blocks aggregate completion.

## 3. Per-tag replay transaction

For each inventory tag, perform this transaction:

1. Atomically claim the tag in the replay namespace and re-check that no valid
   accepted receipt already exists.
2. Download and validate the compact LRAT as in section 1.
3. Generate one deterministic Lean source module from the authoritative table,
   Lean-exact CNF identity, and compact LRAT.  Record its bytes and SHA-256.
4. Cold-compile with the pinned Lean 4.31 toolchain against a private copy-on-
   write view of the verified external overlay.  Capture the complete command,
   environment allowlist, wall/CPU time, peak RSS, stdout, stderr, and exit code.
5. Require exit zero and a nonempty `.olean`; hash the raw `.olean`.
6. Run the same source scan and axiom audit used for the 122-module bank.  The
   permitted classification is no `sorry`/`sorryAx`, standard foundational
   axioms (`propext`, `Classical.choice`, `Quot.sound`), and only the explicitly
   disclosed `native_decide` hooks.  Any other axiom or missing audit is failure.
7. Compress the `.olean` with pinned `zstd -1`, hash the compressed bytes, and
   upload source, full log, compressed `.olean`, and receipt to staging keys.
8. HEAD/read back each uploaded object and verify its recorded length and
   SHA-256.  Only then publish the accepted receipt/ledger line atomically.
9. Only after the accepted receipt is durable, self-copy the input certificate
   at the same key with tag `replay=consumed` to reset its lifecycle clock as
   specified in section 6.  Then release the claim and delete local tag scratch.

Suggested durable layout:

```text
sat49/campaign-20260825/h1-replay/oleans/<tag>.olean.zst
sat49/campaign-20260825/h1-replay/sources/<tag>.lean.zst
sat49/campaign-20260825/h1-replay/logs/<tag>.log.zst
sat49/campaign-20260825/h1-replay/receipts/<tag>.json
sat49/campaign-20260825/h1-replay/ledger/<tag>.accepted
sat49/campaign-20260825/h1-replay/quarantine/<tag>/...
```

Small receipts, ledgers, manifests, and logs remain in S3 Standard.

## 4. Receipt contract

Each accepted JSON receipt must include at least:

- schema version, tag, table serialization/hash, CNF hash, and inventory hash;
- certificate key, pre-copy ETag, gzip bytes/SHA-256, compact bytes/SHA-256;
- generator/template/repository/toolchain/base-overlay identities;
- generated module name and source bytes/SHA-256;
- exact compile command, sanitized environment, start/end timestamps, exit code,
  wall/CPU seconds, and peak RSS;
- raw `.olean` bytes/SHA-256 and zstd bytes/SHA-256, zstd version/arguments;
- log key/hash, source key/hash, compressed-olean key/hash;
- source-scan result, complete axiom-audit result, and explicit
  `sorryAx=false`;
- upload read-back results;
- certificate self-copy result: post-copy ETag/last-modified, object tags, and
  byte-identity verification;
- worker instance id, AMI/image digest, AZ, worker hash, and receipt signature or
  keyed integrity mechanism selected at sign-off.

Acceptance is a validator decision over this schema, not merely Lean exit zero.
Receipts are immutable once accepted; corrections use a new schema/run prefix.

## 5. Aggregate and completion gates

Per-tag acceptance permits lifecycle tagging but does not complete the replay
stage.  Overall completion additionally requires:

1. an authoritative reconciliation proving exactly one accepted receipt for
   every intended inventory tag and no unknown tags;
2. re-derivation of every source/certificate/CNF/olean hash referenced by the
   receipts;
3. generation and cold compilation of the aggregate bank against the complete
   uncompressed leaf-olean set on EBS;
4. an aggregate `#print axioms` audit with no `sorryAx` and no undisclosed axiom;
5. an independent review of counts, failures/quarantine, receipt schema,
   aggregate hashes, and axiom classification;
6. an EBS snapshot (or an independently tested restore of every zstd olean)
   retained until downstream aggregate/import audit is complete.

Fail fast on the first systematic import, generator, or audit error.  Individual
bad inputs may be quarantined, but the stage must not call itself complete while
any expected tag lacks an accepted receipt.

## 6. Certificate lifecycle: Glacier Instant Retrieval

The operator ruling is: certificates stay Standard until Lean replay consumes
them; nothing is deleted.  Configure a lifecycle rule scoped to prefix
`sat49/campaign-20260825/h1/` **and** object tag `replay=consumed`, transitioning
to `GLACIER_IR` after seven days.

Tagging alone does not reset object age.  Therefore the replay transaction must
self-copy the certificate to the same key and replace/add the tag, creating a
new Last-Modified time from which the seven-day transition is measured.  Because
bucket versioning is off, guard this mutation carefully:

- use a conditional copy against the pre-replay ETag;
- preserve encryption, content type/encoding, and all existing metadata/tags;
- use managed multipart copy if the object exceeds the single-copy size limit;
- verify post-copy content length and SHA-256 against the pre-copy object;
- publish the copy result in the accepted receipt;
- never self-copy before the `.olean` and audit receipt pass upload read-back.

If the conditional copy or byte-identity check fails, quarantine the lifecycle
step and leave the object in Standard.  Never transition an unconsumed object.

## 7. Capacity and storage estimate

Measured leaf output for the audited 122-module replay was 30,842,130,784 raw
bytes: 252.8 MB average and 1.066 GB maximum.  Linear projections are:

| Leaves | Raw `.olean` | zstd-1 at measured 0.2826 | conservative zstd range |
|---:|---:|---:|---:|
| 10,848 | 2.74 TB | 0.77 TB | 0.69–0.79 TB |
| 13,351 | 3.37 TB | 0.95 TB | 0.84–0.97 TB |

The measured zstd ratios were 0.2826 at level 1, 0.2894 at level 3, and 0.2504 at
level 9.  Use level 1 for streaming throughput, while receipts preserve raw and
compressed sizes/hashes.  Provision at least 4 TB working EBS because aggregate
compilation needs the simultaneous uncompressed leaf set plus the 9–12 GB base
overlay and scratch/headroom.  Alert at 70% and stop claims at 85% utilization.

At the observed roughly three minutes per leaf and memory-limited `P=16–18`,
10,848 leaves project to about 36–41 hours on one replay node.  The launch spec
must price the editor-approved instance, EBS, snapshot, S3 PUT/storage, and
expected retry margin before spend.  Do not assume the SAT fleet's c7g shape is
appropriate: the replay stage must benchmark one real large leaf and size from
measured RSS and ARM64 Lean throughput.

## 8. Launch gates and rollback

Before launch, editor sign-off must resolve all `TBD` identities in the freight
manifest and approve the dollar estimate.  Required gates are:

- exact-production cold preflight accepted;
- IAM least privilege tested (read H1 certificates; write only replay prefixes;
  conditional self-copy/tag on H1 inputs; no delete permission);
- lifecycle rule inspected in dry-run/config output;
- one real tag completes the full upload/read-back/self-copy transaction;
- its receipt is independently validated and the certificate remains readable;
- concurrency and disk alarms are live.

On systemic failure: stop new claims, preserve logs/receipts/quarantine, leave
certificates in Standard, and keep the EBS volume for diagnosis.  Never delete
source certificates or accepted replay artifacts as part of automatic cleanup.

