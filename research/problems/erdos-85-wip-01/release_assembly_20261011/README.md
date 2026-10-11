# Conditional release assembly

Branch `erdos85/release-assembly-20261011` merges the completed H7 campaign
at `27a58f56e63`, accepted H3 capstone at `7717312e11b`, and integration
record at `458227dcb63`. It also merges the H5 terminal audit, later H3
campaign audits, Ramsey citation review, and H7 LRAT/split review branch.
Merge conflicts were confined to documentation: the cloud-builder override
comments and the later independently audited LRAT-adapter status were retained.

`Erdos85FiniteDropCapstone.lean` now imports the accepted conditional
`Erdos85OrderFortyNineCapstoneH3` endpoint. H1 and H7 UNSAT evidence remain
explicit hypotheses. No new axiom is introduced. These are conditional
Lean conclusions with the existing native-decision trust dependencies,
not an unconditional Lean proof or a resolution of the full Erdős problem.

## Receipt review

On 11 October, a fresh invocation of the unchanged collector on all 13,094
local `results-all` files and pinned inputs exited zero. Its complete JSON
summary and all 29 decompressed receipt tables matched commit `27a58f56e63`
exactly. Independent checks verified the complete ordered inventory and
CNF hashes of 377,776 leaves and 28 covers, and the split specification,
manifest, full split hash, 257 split-item identities, and parent-leaf link.
There are zero missing leaves, zero alarm receipts, and 233 superseded
non-certified receipts. One original leaf is certified through its split.

The collector's 4,268.71 solver CPU-hours, 705.74 checker CPU-hours and
20,210,589,568,747 proof bytes count selected successful leaf and split-item
runs. They exclude top-level covers and superseded attempts. This review
checks receipt aggregation and CNF identity; discarded proofs were not
replayed, and cloud shutdown/spending were reported by the campaign owner.

## Bounded endpoint validation

`source-manifest.json` preserves all 892 accepted capstone closure source
hashes and adds the new endpoint, for 893 sources. `validate.py` checks
these locally without running Lean. With `--cloud` it requires the existing
builder's container, two CPUs and 16 GiB, verifies all 891 accepted imported
objects before and after, and compiles only the H3 wrapper and finite-drop
endpoint into a fresh isolated directory. Each has a 90-second limit.
The existing cache is not overwritten. Printed axiom sets must match the
accepted lists exactly: 601, 607 and 604; no `sorry` is accepted.

This is fresh endpoint compilation against accepted dependency objects,
not a cold rebuild of all native certificates. Cloud validation results
are retained separately after completion. Paper v10 and public release
remain separate work; this assembly does not publish or tag anything.

The first bounded attempt at `fb8838172e0` passed the dependency hash checks,
then failed before theorem checking because Lean resolved the partial fresh
`Proofs` package root without falling through to the original cache.
`failed-attempt1` preserves its raw job and compile logs. The retry links
the 891 verified dependency objects into the fresh package root, then writes
the two new endpoint objects there. Resource limits and theorem sources
are unchanged.
