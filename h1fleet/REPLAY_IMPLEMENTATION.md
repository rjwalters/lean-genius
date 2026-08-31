# H1 replay implementation

Status: **implemented locally; production launch remains editor-gated**.

This directory implements the transaction in
`CLOUD_LEAN_REPLAY_STAGE_SPEC.md`.  It does not launch instances or mutate S3
unless an operator runs the worker with the production backend explicitly.

## Components

- `replay_common.py`: manifest validation, hashing, command execution, and
  local/S3 object-store adapters.  Immutable S3 publication uses conditional
  `PutObject`, embeds the payload SHA-256 in metadata, then performs HEAD and
  full GET read-back.  Lifecycle tagging preserves all existing tags and
  verifies unchanged ETag, length, digest, and Last-Modified.
- `replay_worker.py`: one tag transaction.  It validates gzip and compact LRAT
  hashes plus a final empty-clause action; generates a deterministic leaf;
  scans out `sorry`/`admit`; appends a literal `#print axioms`; compiles and
  audits; uploads zstd source/log/olean; publishes immutable replay-ready;
  adds `replay=consumed`; then publishes immutable receipt and accepted ledger.
- `audit_replay_leaf.py`: extracts exactly one literal Lean 4.31 axiom report.
  The worker independently applies the manifest's exact and regex allowlist.
- `validate_replay_receipt.py`: independently re-HEADs the certificate and all
  artifacts, checks the ready-record hash, lifecycle evidence, source scan,
  axiom classification, canonical receipt SHA-256, and manifest binding.
- `run_replay_queue.py`: single-node resumable dispatcher.  It validates the
  sorted unique JSONL queue, queue/worker hashes, expected count, manifest
  concurrency ceiling, explicit `--execute YES` latch, and a nonblocking
  host-local lock at the manifest-bound absolute path, held for the full
  dispatcher lifetime and recorded in build/`START`/`END` receipts.  A
  competing process fails before `START` even if it supplies another state
  directory.  Goal #44
  deliberately selected this single-writer contract; there is no distributed
  lease or multi-writer failover.
- `build_replay_manifest.py`: freezes a reviewed draft against a clean commit,
  queue, receipted capacity index, and every executable script hash.  It proves
  every queued tag is assigned its Lean capacity ordinal rather than a raw or
  family-local operational index.  Final freezes use
  `--require-complete-capacity-queue`, which requires the exact 13,351 tags and
  all five contiguous capacity-ordinal ranges.
- `capacity_queue.py`: validates the capacity-reindex receipt and the exact
  queue tag-to-`(profile, local_index)` binding before a manifest can freeze;
  it also parses each sparse JSON table serialization and recomputes its orbit
  tag, so the free-form job field cannot silently describe another table.
- `test_replay_transaction.py`: complete local-store tests of acceptance,
  idempotent resume, dispatcher execution, corrupt-certificate rejection,
  undisclosed-axiom rejection, and literal axiom parsing.

## Queue and module contract

Each JSONL row has:

```json
{
  "tag": "0123456789abcdef",
  "profile": 0,
  "local_index": 3,
  "certificate_key": "sat49/campaign-20260825/h1/0123456789abcdef.compact.lrat.gz",
  "certificate_gzip_sha256": "...",
  "compact_lrat_sha256": "...",
  "cnf_sha256": "...",
  "table_sha256": "..."
}
```

The generator command receives placeholders `{tag}`, `{profile}`,
`{local_index}`, `{stem}`, `{module}`, `{compact_lrat}`, `{source}`, `{olean}`,
`{audit_json}`, `{log}`, and `{work}`.  The fixed naming interface is:

```text
module  = Erdos85H1V2CertP<profile>I<local_index:05d>
stem    = h1V2P<profile>I<local_index:05d>
theorem = Erdos85.<stem>Checked
entry   = Erdos85.<stem>Entry
```

This is the contract requested by the checked-union generator; it supports
all profiles rather than only the existing P0/P2/P4 baselines.

## Acceptance ordering

```text
compile + audit
  -> upload/read back source, log, olean
  -> immutable replay-ready record
  -> add/read back replay=consumed without changing object identity
  -> immutable final receipt
  -> immutable accepted ledger
```

A replay-ready record is deliberately not acceptance.  A crash after it
resumes at lifecycle tagging and does not recompile.  An existing final receipt
is accepted only when bound to the current manifest and its
`canonical-json-sha256-v1` digest verifies.  Immutable create collisions GET
and verify the winner; divergent bytes fail closed.  Receipts are bookkeeping
evidence, while the final cold build and literal axiom audit remain the proof
trust root.

## Remaining launch gates

Before production use, build and receipt the 13,351-row capacity-reindexed
certificate index, derive the replay queue from those capacity ordinals, and
freeze it with `--require-complete-capacity-queue`.  Provide the copied-overlay/generator/toolchain identities and
commands, obtain directed review, run one real P=1 leaf, independently validate
its receipt, then derive concurrency/cost from measured RSS and throughput.
Use exactly one dispatcher and one reviewed state directory; exercise live
competitor rejection before P=1.  No second dispatcher or cloud scaling is
authorized by this implementation.
