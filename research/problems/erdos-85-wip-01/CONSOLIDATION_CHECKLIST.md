# `erdos85-drop-v1` consolidation checklist

Status: **PREPARATION ONLY — the drop is not yet proved and the tag must not be
created early.**  This is the execution checklist for operator mandate 1318 and
goal #43.  A checked box requires the named durable evidence; verbal success or
an idle process is not evidence.

Current evidence snapshot (2026-08-30 17:26 PDT; only the replay-contract
selection and exact-image implementation/test boxes below are discharged):

- the reviewed Branch-A consolidation lineage ends at `7763e294de`; the
  capacity-index/replay provenance chain and hierarchical aggregate generator
  are also reviewed and banked, but neither is final campaign evidence until
  the complete accepted receipt set is generated and cold-audited;
- the latest authoritative H1 reconciliation reports 9,411 certified, 175
  in-flight, and 3,765 pending out of 13,351 (squad messages 36534 and 36537); the
  completion universe is therefore still incomplete;
- replay consumption is assigned to sol-2 and replay review gates/checklist
  maintenance to sol-3.  Goal #44 selected a single-writer, canonical-JSON,
  plain-SHA-256 receipt contract with create-only publication and no KMS or
  distributed lease.  Its v2 implementation is reviewed and banked at
  `779463f6cb` (#1155; 41/41 independent tests), but the exact-image real P=1
  transaction and production evidence remain open;
- the four-parent H3/H5 split completed with durable END at 2026-08-30
  11:17 PDT: all 264 unique jobs terminated with zero failures, comprising nine
  fresh validated UNSAT ledgers and 255 reviewed QUICK-UNKNOWN markers.  It ran
  under queue
  receipt `666538b014b717efb27a16f10dbcc3d61c5eb04487b1ca02cfc3dd34b7ebb332`,
  queue `a992dbb7474c2dd7e83b62d087733f42402facc62e9924b210b2d285a6b31879`,
  and worker
  `1e4f19c7485c1a3114759abbdca3de2221632245c688f297ec9eff8dde914dc1`,
  with durable START ledger; legacy 0-3 shutdown receipt
  `041a1a2a5ea0e62b01e1435156441c8a0c956e13fac4ecb677f2ab8a4dfbf8c2`
  and recoverable parent-0 archive receipt
  `f1470b12e17775ea979da6148bf032bb9edfc65b222db44dcbe76956cfd8dfde`
  were independently rehashed after squad message 36430.  The completed quick
  pass is solver-fleet evidence, not a discharged H3/H5 semantic socket;
- H7 host execution is live at P=1 under the 105-GiB preservation floor; the
  first leaf ended SLOW-UNKNOWN and the second is active.  Goal #44 directs
  eventual fleet handoff after H1 v2 drains, so no H7 socket is discharged; and
- the named frozen path `sat49/compact_action_manifest.txt` is still absent.
  The existing four-row file under `proofs/Proofs/Certificates/` describes old
  H9 `t2`/`t3` certificates and must not be copied as H3/H5/H7 evidence.

Canonical targets, fixed by the operator:

- reader-facing page: <https://leangenius.org/proof/erdos-85>;
- formalization permalink after tagging:
  <https://github.com/rjwalters/lean-genius/blob/erdos85-drop-v1/proofs/Proofs/Erdos85FiniteDropCapstone.lean>;
- tag: `erdos85-drop-v1`, created on `main` at the completing merge only;
- frozen certificate-manifest locations:
  `research/problems/erdos-85-wip-01/sat49/{t34_manifest.txt,lrat_manifest.txt,compact_action_manifest.txt,SURVIVOR-MANIFEST.md,SEQCOUNTER-SPEC.md}`
  and `proofs/Proofs/Certificates/`.

## 0. Trigger and freeze

- [ ] The final H1, H3, H5, and H7 campaign obligations have accepted Lean
  consumers, not merely solver verdicts.
- [ ] The final composed theorem has no campaign hypotheses and states both
  `minDegreeForC4 48 = 8` and `minDegreeForC4 49 = 7`; its strict-drop corollary
  states `minDegreeForC4 49 < minDegreeForC4 48`.
- [ ] The editor names the exact final module and fully-qualified theorem that
  replace the audit command placeholders below.
- [x] The editor selected the replay receipt contract in goal #44 (squad
  message 36482): receipts are operational bookkeeping outside the trust chain;
  use one single writer, canonical JSON with plain SHA-256, create-only
  publication via conditional `PutObject If-None-Match:*`, and apply
  `replay=consumed` only after `.olean` construction and literal axiom audit.
  Do not implement KMS signing or a distributed lease for this campaign.
- [x] Implement and independently review that selected contract end to end in
  the exact production image.  Require strict canonical schema/type checks,
  payload SHA-256 mutation failure, create-only collision GET-and-verify,
  single-writer resume behavior, and consumed-tag ordering after successful
  `.olean` construction plus literal `#print axioms` audit.  Evidence: reviewed
  implementation `779463f6cb` (#1155) and an independent read-only run of all
  41 tests plus six-module in-memory compilation in
  `lean4-arm64@sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6`
  on 2026-08-30.  This is implementation evidence only, not the real S3 P=1
  transaction required below.
- [ ] Freeze new mathematical lanes and record the integration commit, dirty
  status, Lean version, Lake manifest hash, and certificate-manifest hashes.
- [ ] Confirm every active worktree owner has pushed or explicitly abandoned
  relevant changes.  Do not absorb unrelated dirty files.
- [ ] Open a completing merge/review gate.  Do not create or push a tag yet.

## 1. Socket and manifest closure

- [ ] H1: prove the one-high exclusion over the Lean-proven 13,351 capacity-row
  universe (2,503 all-even plus 10,848 complement).  Reconcile the separate
  13,541-row compact inventory and explain its 190 extra tags; never silently
  treat them as pending H1 capacity jobs.
- [ ] H1 replay: freeze the exact 13,351-row queue only after the coverage
  bijection, production identity formats, clean/tracked-file freight freeze,
  and all manifest hashes pass validation.  Run the prescribed exact-image
  real `P=1` large-leaf transaction: durable artifact read-back and immutable
  replay-ready first, then lifecycle tagging with unchanged certificate
  identity, then schema/hash-verified final receipt and ledger.  Obtain
  editor approval of measured RSS, throughput, concurrency, EBS shape, retry
  margin, and total dollar estimate before any scaled launch.
- [ ] Before the real replay transaction, independently inspect and test the
  least-privilege replay role (no delete and no H1 certificate `PutObject`),
  the prefix-and-`replay=consumed` Glacier-IR lifecycle rule, disk/concurrency
  alarms, and the single-writer process/exclusion policy.  Preserve the dry-run/config
  evidence and editor approval.
- [ ] H3: match every accepted scout/cube leaf to the exact semantic consumer
  and its discharging commit.
- [ ] H5: match every accepted variable-high leaf to the exact semantic
  consumer and its discharging commit.
- [ ] H7: match the complete checked cover/leaf bank to
  `OrderFortyNineStratumExcluded 7` and its discharging commit.
- [ ] Generate a machine-readable socket table with columns: hypothesis,
  theorem, source module, commit, campaign manifest row(s), CNF SHA-256,
  compact-LRAT SHA-256, replay receipt, and review id.
- [ ] Require a bijection between survivor-manifest hypotheses and socket-table
  rows.  Missing, duplicate, unknown, or hash-divergent rows block the release.

## 2. Durable certificate audit

- [ ] Reconcile every required tag against the authoritative coverage manifest:
  S3-certified, host-ledgered-not-uploaded, fleet-in-flight, or pending.
- [ ] Require the completion state to have no pending/in-flight/unuploaded tags
  in the final theorem's actual certificate universe.
- [ ] HEAD/read back every required durable object and rederive hashes from
  bytes, not ETags.  Verify gzip integrity and decompressed compact-LRAT hashes.
- [ ] Replay every compact LRAT through the pinned verified checker against the
  byte-exact CNF; archive command, tool hashes, return code, and complete log.
- [ ] Validate every cloud Lean replay receipt, raw/compressed `.olean` hash,
  source hash, axiom audit, and `replay=consumed` lifecycle transaction.
- [ ] Require each accepted replay receipt to pass the complete §4 schema,
  canonical-JSON, and payload/object SHA-256 verifier selected by goal #44.  A
  local-store receipt, replay-ready object, lifecycle tag alone, malformed/TBD
  receipt, or mechanics-only test result contributes **zero** accepted leaves.
- [ ] Reconcile exactly one accepted receipt per intended H1
  tag and no unknown receipts.  Independently reload and byte-hash the bound
  immutable replay-ready record, all artifacts, the input certificate, and the
  terminal ledger; exercise the missing-ledger recovery path without rewriting
  the receipt.
- [ ] Build the deterministic hierarchical H1 aggregate: leaf banks of direct
  fan-in at most 128, profile dispatch layers with no direct leaf imports above
  the bank layer, and a top module with exactly five profile imports.  Prove a
  full `(profile, local-index, tag, theorem, module)` bijection with the 13,351
  accepted leaves and bind the aggregate layout manifest and its own hash.
- [ ] Cold-compile and literally audit `#print axioms` for every aggregate node
  at every layer, ending at the top H1 bank.  A hand-written or syntax-only
  smoke module is not completion evidence unless it is byte-bound to generated
  output.
- [ ] Retain the replay EBS snapshot, or independently restore and hash every
  compressed `.olean`, until the complete aggregate/import audit has passed.
- [ ] Confirm certificates are retained (Standard or Glacier Instant Retrieval
  according to the post-replay lifecycle); nothing required for reproducibility
  has been deleted.

## 3. Dependency-cone axiom audit

The final invocation is deliberately target-explicit:

```sh
python3 scripts/erdos85_audit_dependency_cone.py \
  --module Proofs.<FINAL_DROP_MODULE> \
  --target Erdos85.<FINAL_DROP_THEOREM> \
  --allowlist research/problems/erdos-85-wip-01/drop_axiom_allowlist.json \
  --output-dir <DURABLE_AUDIT_DIR>/dependency-cone
```

- [ ] The target is the unconditional composed drop theorem, not
  `minDegreeForC4_fortyNine_lt_fortyEight` with explicit hypotheses and not the
  conditional small-high socket.
- [ ] Review and freeze `drop_axiom_allowlist.json` at the completing commit.
  Every generated native root of the form
  `..._native.native_decide.ax_*` must match exactly one disclosed family, and
  every other non-foundational root must be rejected.
- [ ] Run the audit from the clean-checkout build.  Require `status=PASS`, zero
  undisclosed axioms, zero `sorryAx`, and no output delimiter mismatch.
- [ ] Paste `print-axioms.log` verbatim into the squad room in bounded chunks;
  preserve the complete file and receipt on durable storage.
- [ ] Independently review the exact theorem count, dependency inventory,
  native-root family counts, allowlist hash, and all audit artifact hashes.
- [ ] Separately run literal `#print axioms` on the exact-value theorem, the
  strict-drop theorem, and the final nonexistence socket and compare them with
  the dependency-cone receipt.

The allowed foundational axioms are exactly `propext`, `Classical.choice`, and
`Quot.sound`.  Lean 4.31 reports each permitted `native_decide` hook as a
declaration-specific generated root (`..._native.native_decide.ax_*`), not as a
shared `Lean.ofReduceBool` axiom.  Each such root is permitted only when its
owning theorem matches exactly one enumerated, reviewed family in the JSON
allowlist.  Any other axiom is a release blocker.

## 4. Independent clean re-verification

- [ ] Create a fresh checkout at the proposed completing commit with no reused
  project `.olean`s or mutable symlink overlay.
- [ ] Record `git status`, commit SHA, submodule/Lake manifest hashes, `lean
  --version`, platform/image digest, and all tool hashes.
- [ ] Fetch the pinned mathlib cache, then cold-build the exact final module and
  all generated certificate modules.  Preserve unfiltered logs and exit codes.
- [ ] Re-run the dependency-cone audit in that checkout.
- [ ] Independently replay the full required LRAT corpus through the verified
  checker and reconcile its tag/hash set with the socket table.
- [ ] Restore a sample of zstd-compressed cloud `.olean`s from durable storage,
  verify both compressed/raw hashes, and import them in an isolated overlay.
- [ ] Independently reproduce the real `P=1` receipt with the pinned AMI,
  container image, IMDSv2 instance identity, AWS CLI, overlay, generator,
  checker, zstd, receipt schema, and canonicalization/hash identities; verify that
  no placeholder (`TBD`, `UNKNOWN`, or local-test identity) entered the frozen
  freight manifest.
- [ ] Run the repository's relevant Python tests/generator self-checks and
  record exact commands/results.
- [ ] Obtain independent reviewer approval for Lean build, certificate replay,
  manifest bijection, and axiom scope.

## 5. Manuscript and reader-facing audit

- [ ] Replace every “campaign in flight” count with values derived from the
  final coverage receipt; do not hand-copy live ledger estimates.
- [ ] Fill manuscript §8 only after the preceding gates pass: exact theorem,
  proof architecture, disclosed axiom families, certificate corpus, and scope.
- [ ] State the finite result as the decided drop `f(49)=7<8=f(48)` and the
  literature claim only as “the first decided drop we are aware of,” with the
  reviewed citations in `manuscript/FIRST_DROP_LITERATURE_CHECK.md`.
- [ ] Keep the eventual-monotonicity question open.  One finite drop disproves
  ordinary monotonicity, not Erdős 85's eventual statement.
- [ ] Audit every theorem name, commit, count, URL, certificate path, and trust
  statement against the tree and durable receipts.
- [ ] Operator completes the required morning/read-through gate.  Nothing is
  posted, submitted, or otherwise sent externally before that approval.

## 6. Completing merge and tag

- [ ] Merge the fully reviewed integration commit to `main` without rewriting
  audited artifacts.  Record the resulting main commit SHA.
- [ ] Re-run the shortest identity gates on that exact main commit: clean status,
  final target `#check`, literal final `#print axioms`, manifest hashes, and
  audit-receipt hashes.
- [ ] Confirm `erdos85-drop-v1` does not already exist locally or remotely and
  that the operator has authorized creation.
- [ ] Create the annotated tag **at the completing main commit**, including the
  final theorem name, audit receipt hash, and certificate-manifest receipt hash.
- [ ] Verify the tag resolves to that exact commit and that the fixed permalink
  resolves to `proofs/Proofs/Erdos85FiniteDropCapstone.lean`.
- [ ] Do not push the tag or publish external material until the operator's
  explicit final instruction.  Record any eventual push as a separate action.

## 7. Stop conditions

Stop consolidation and report a blocker if any of these occurs: a missing
certificate; CNF/LRAT/olean hash divergence; an unmatched manifest hypothesis;
an undisclosed axiom/native root; `sorryAx`; a failed cold build or LRAT replay;
an unexplained inventory mismatch; a dirty completing checkout; a tag target
different from the audited merge; or absent operator authorization.
