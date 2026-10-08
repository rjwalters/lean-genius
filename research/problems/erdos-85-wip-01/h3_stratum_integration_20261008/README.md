# H3 stratum integration preparation

Status: prepared source bundle; no stratum build or acceptance yet.
Claude requested this integration in squad message 53033 after confirming
that the bounded H3 campaign fits the builder usage already approved.
The original campaign, job
`20261008T124453-erdos85__h3-triple-formal-20261007-503105` at
`002fc52979945c83ada35b24c430e6e2103a6797`, stopped at residue 89's
90-second limit. Its audit accepts 90 cumulative parts, not the full cell.
The historical `SOURCE.json` remains unchanged. These helpers now require
an explicit `INTEGRATION.json` binding to a future independently accepted
384-part cell assembly; no binding exists yet. Do not advance a cloud
branch or change its cache while its producer is running.

The source bundle stages 418 modules outside the production library glob:
28 unchanged audited pair modules, four triple-runtime modules, 384 exact
triple-part sources, the planned triple-cell composition, and one new stratum
module. The latter applies
`orderFortyNineStratumExcluded_three_of_tripleCells` to the two cell results.
Preparing source is not computation credit.

`prepare.py` checks every pair source against both the peer commit
`85d336bfbfe` and the retained independent pair audit. It recursively follows
all pair-cell `Proofs.*` imports: the 168 shared modules outside the 28 pair
modules are byte-identical in the peer pin, our triple pin and the current
local source tree. This guards against resolving copied objects to changed
shared definitions. It does not replace actual Lean import/assembly checks.

The expected stratum trust set is listed explicitly in `SOURCE.json`:
24 pair native axioms, 384 triple native axioms, and `propext`,
`Classical.choice`, `Quot.sound` (411 total). Final acceptance must compare
the printed set exactly and reject any additional or missing axiom.

## Remaining work

1. Obtain terminal, independently accepted triple-cell evidence from the
   bounded sweep, residual pass and final cell assembly. Preserve partial results if a pass stops early; do not
   treat preparation or reported part completions as full cell acceptance.
2. Recheck the pair cache against its retained audit and inspect required
   object companions. Transfer only the audited artifacts into a complete
   destination cache, refusing differing existing files. Preserve producer
   hashes and receipts; do not rerun the 24 native searches.
3. Materialize these exact sources for integration only after acceptance of
   the full triple cell. Compile the small H3 stratum module on the existing
   cloud builder with bounded resources, using verified compiled imports.
4. Independently retain and audit the fresh stratum object, terminal job,
   exact source/dependency hashes and the 411-entry printed axiom set.
5. Report `OrderFortyNineStratumExcluded 3` only after that audit succeeds.
   H3 stratum closure does not discharge the remaining H1/H7 external
   evidence hypotheses or complete the paper's human/publication review.

This directory is prepared locally while the campaign runs; it is not
pushed into the live cloud worktree. No cloud cache transfer or stratum
compilation has occurred.

## Transfer and materialization helpers

`bind_cell.py --triple-audit PATH` validates the complete cell audit, all
384 exact part sources and axiom sets, both exact 387-axiom cell exports,
retained evidence hashes and all 418 prepared sources. It records the
producer job, execution commit, repository-relative audit path and audit
hash in a new immutable `INTEGRATION.json`, bound to the unchanged source
specification hash. It refuses a partial receipt or a different existing
binding. This performs no compilation, transfer or materialization.

`transfer_pair.py` defaults to read-only inspection on the cloud host. It
requires the bound successful cell job, a caller-pinned independent
triple audit and all 384 unique residues. It verifies retained evidence
hashes, all existing triple objects and unchanged shared sources. `--apply`
atomically publishes the 28 pair `.olean` files into the complete H3 cache,
using exclusive links and refusing conflicting destinations. A new receipt
path is required. Existing matching files are reused. The peer cache has
ordinary `.olean` files plus editor/hash/trace companions; no private/server
object companions were observed. Direct Lean theorem import uses the audited
`.olean` files; fresh assembly compilation must still verify compatibility.

`materialize.py` uses the same full-triple acceptance gate before copying
the prepared sources into `proofs/Proofs`. It checks all source hashes and
existing files first, defaults to read-only inspection, and refuses to
overwrite differing source. It must run after cell acceptance and binding, and before
the integration commit/build; it does not execute Lean.

Tiny-file/metadata tests cover object inspection, atomic copy,
idempotence, conflicting/corrupt artifacts, and rejection of partial, failed,
wrong-job, wrong-commit, incomplete, duplicate or wrong-cell triple receipts.
Binding checks reject missing bindings, changed historical sources,
invalid producer identifiers/hashes and paths outside the repository.
No real cloud cache was modified by those tests.

## Bounded final build and acceptance

`stratum_inputs.py` constructs an exact 417-module imported-object ledger
from the pair audit, runtime-chain audit and complete triple-cell audit.
The cell audit itself accounts for every part from the sample, initial
campaign, sweep and residual pass. The ledger requires its four runtime
objects to match the prior runtime audit exactly. It rejects missing or
duplicate modules, changed source hashes, empty objects and unaccepted
inputs. The transfer, binding and synthetic-ledger suite has 33 tests;
synthetic triple objects grant no credit.

After the full triple audit is retained and bound, materialize sources locally, commit
and push the integration only while the producer is terminal. Run the guarded
pair transfer on the cloud host and retain its immutable `pair-transfer.json`.
The transfer's receipt must be copied back unchanged for banking. Do not
replace or edit the existing producer receipts.

`run_stratum.py` checks the caller-pinned triple and transfer receipts, all
418 materialized sources, the 168 shared dependencies and all 417 actual
imported object hashes/sizes. It compiles only `Proofs.Erdos85H3Stratum` with
one worker, two CPUs, 16 GiB, a 90-second inner limit and a three-minute outer
limit. The same imported-object checks run after compilation. It requires
exactly the prepared 411 axioms and retains the new object, raw log and RUN
receipt. A worker success remains pending independent acceptance.

```sh
e85-remote ssh 'taskset -c 0,1 /opt/e85/bin/e85-host run erdos85/h3-triple-formal-20261007 --full --mem 16 --threads 1 --timeout 3m --no-follow -- lake env python3 -B ../research/problems/erdos-85-wip-01/h3_stratum_integration_20261008/run_stratum.py --triple-audit-sha TRIPLE_SHA --transfer-receipt-sha TRANSFER_SHA'
```

`capture_stratum.py` selects the exact submitted job and execution commit,
independently reads the actual imported and new cache objects, checks source
bytes against Git, validates the raw axiom report and creation time, and
retains immutable evidence. It reads object hashes twice to reject changes
during collection. Only `H3_STRATUM_ARTIFACT_AUDIT_PASS` grants the stratum
verdict. Preserve failed attempts and force-add ignored raw logs when banking.

```sh
python3 -B capture_stratum.py --job JOB --commit FULL_COMMIT --triple-audit-sha TRIPLE_SHA --transfer-receipt-sha TRANSFER_SHA
```

These build/collector scripts are prepared but have not run. Their execution
is gated by complete cell acceptance and its explicit producer binding.
The failed campaign's receipts and original prepared `SOURCE.json` remain
unchanged; the new binding does not retroactively grant them cell credit.
