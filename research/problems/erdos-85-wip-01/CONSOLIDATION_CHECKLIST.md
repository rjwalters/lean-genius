# `erdos85-drop-v1` consolidation checklist

Status: **PREPARATION ONLY — the drop is not yet proved and the tag must not be
created early.**  This is the execution checklist for operator mandate 1318 and
goal #43.  A checked box requires the named durable evidence; verbal success or
an idle process is not evidence.

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
  Every direct `Lean.ofReduceBool` root must match exactly one disclosed family.
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
`Quot.sound`.  `Lean.ofReduceBool` is permitted only through the enumerated,
reviewed families in the JSON allowlist.  Any other axiom is a release blocker.

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

