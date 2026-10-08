# Consume the U1/R15 pilot in the full H3 census

Status: **source-only, uncompiled, unqueued**.

The U1/R15 native rejection and its original no-joint consumer are independently
verified in `../h3_cloud_u1r15_20261008/split-evidence/`. `Full260.lean`
connects that exact certificate to the representative in the final full census,
erases `(1,15)`, and proposes the resulting 260-pair witness and conditional
exclusion theorems. The other 260 rejections remain explicit hypotheses.

The first three reports check membership, count, and input identity using
standard axioms only (or none). The last three are expected to retain the
one existing native rejection axiom, in addition to standard axioms. No new
native search is performed. No full H3 or deficient-branch exclusion follows.

Compilation must await the cloud-verified `Full261` and `CapacityReduction`
objects from the still-running census. Reuse those objects and the already
verified native certificate; do not repeat the 97-minute rejection search.
The build must preserve source/object/log hashes and all six exact axiom
reports before this reduction is called verified. The source remains outside
the library's default build glob.
