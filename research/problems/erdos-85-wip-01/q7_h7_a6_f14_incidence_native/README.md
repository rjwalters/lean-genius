# Reviewed native necessary S-P incidence API

Review 2717 accepts this native implementation of the necessary family and incidence criteria reviewed in 2712 and 2713. Each pair vertex selects a singleton-neighbor family; exact singleton capacities and pairwise common-neighbor bounds are necessary for any completion. Pair-pair edges remain omitted.

The API validates the saved a6 host graph type and emits replayable negative choice trees or empty-family witnesses. UNKNOWN and INVALID are not exclusions. The Python adapter verifies source/binary hashes and limits research calls to 10,000 choice nodes.

Independent review checked all 151 source-joined fixtures (91 empty families and 60 negative trees), all branches, malformed/deadline/node-boundary controls, and a synthetic positive choice-engine fixture. The synthetic fixture is not an H7 graph. Hash-bound ASan/UBSan checks passed. This is API qualification only; application to the 445,699-case F14 complement and whole-root composition require separate review.

Author and reviewer files are verbatim under their frozen manifests. BANK_PINS.json binds every payload other than itself. Scope: paper plus computation, no Lean, no global claim.
