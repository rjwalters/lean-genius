# H1 cert-root v3 batched packing and Lean replay

This is the operational plan for turning the approximately 13,000 H1 fleet
certificates into content-addressed packed payloads and checked Lean stubs
without retaining the full certificate corpus on the local host.

## Capacity facts

At the 2026-08-25 checkpoint, cert-root v3 contains 472 indexed rows and 485
packed objects.  The packed directory occupies 159 GiB, or about 336 MiB per
object.  Linear projection to 13,000 rows is 4.3 TiB packed.  This is a sizing
estimate, not a quota: the new fleet's observed compact LRAT size remains the
authoritative input.  The local Stripe volume cannot be the durable store.

## Immutable inputs and identities

Each accepted row must retain the existing v3 fields from `index.v3.tsv`:
orbit/profile/local index, CNF hash, raw and compact LRAT hashes, action and
clause counts, every intermediate binary/frame hash and byte count, final
packed hash and byte count, and `stub_ready`.  The final object key is

```
packed/<packed-sha256-prefix>/<packed-sha256>.lrat.lz4p7
```

An index row becomes publishable only after direct Lean replay of its source
compact and byte/hash verification of its packed payload.  Batch scheduling
must never weaken these per-row gates or rewrite a published content-addressed
object.

## Streaming batch pipeline

Use batches of 8 certificates by default (configurable by a byte ceiling;
target at most 12 GiB local working data).  For each batch:

1. Stage only the accepted compact LRATs and their immutable worker manifests.
2. Recheck manifest identity, compact hash, CNF hash, and direct Lean replay.
3. Encode binary LRAT, frame-compress, and create the packed LZ4 payload using
   the tool versions recorded in `cert-root/tools.txt`.
4. Recompute every v3 hash and byte count, upload the content-addressed packed
   object, and verify the remote object checksum/size.
5. Write a sorted batch index fragment and an upload receipt.  Merge fragments
   into `index.v3.tsv` by unique `(profile,localIndex)`, orbit, compact hash,
   and packed hash; an unequal duplicate is a hard failure.
6. Download or retain that batch's packed objects in the canonical local
   cert-root path, run `generate_h1_v2_lean_stubs.py`, and build the generated
   modules with a bounded Lean worker pool.
7. Record the module source hash and successful olean build in the batch
   receipt.  Only then evict compact/binary/frame/local-packed payloads.  The
   generated source remains reproducible because the receipt binds its remote
   payload object.

Interrupted batches are resumed from receipts.  A row lacking the final olean
receipt remains eligible for restaging even if its packed object was already
uploaded.  No global index lock is held during compression or Lean replay;
only the short deterministic fragment merge is serialized.

## Parallelism and expected throughput

Packing is I/O-heavy and may run independently of solving.  Lean LRAT replay
is the limiting stage: the measured refinement sample was about 200 seconds,
so 13,000 rows project to roughly 722 CPU-hours.  Two Lean workers take about
15 days; six take about 5 days before contention.  On the current shared host,
start with two nice'd Lean workers and an 8-row/12-GiB staging ceiling.  Raise
parallelism only when solver load and memory permit.  A separate six-worker
checker host would keep replay off the solver critical path.

## Required external capacity

- A durable object prefix with at least 5 TiB initial quota, versioning or
  immutability, checksum-preserving upload, and approximately 20% growth room.
- Credentials scoped to that prefix plus a command that can HEAD/verify an
  object before local eviction.
- At least 12 GiB local staging space per active batch and enough memory for
  the configured Lean workers.
- A stable local mount/path for `include_str` during replay.  Cold verification
  restores objects to the same canonical cert-root layout before building.
- A scheduler/receipt ledger that can atomically claim batches; packing and
  replay workers must not write the same batch or `.olean` concurrently.

## Completion audit

Completion is not the existence of 13,000 uploaded objects.  It requires:

- the authoritative terminal jobs/inventory has exact one-to-one v3 index
  coverage;
- every row is `stub_ready`, and all referenced payload hashes and sizes match;
- every generated certificate module has a successful clean Lean replay;
- aggregate checked-bank modules consume exactly those entries;
- a clean checkout can restore the content-addressed payloads and rebuild the
  full dependency cone with no `sorry`, `sorryAx`, or unexpected axioms.

