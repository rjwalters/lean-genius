# H7 hsb LRAT adapter

Status: **cloud build PASS; four exports independently audited**.

`Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalHsbLrat` connects successful
Lean `LRAT.check` results to the existing H7 leaf/cover evidence interface.
It uses `cnf_unsat_of_extension_lrat` from `Erdos85CubeTreeComposition`, which
already combines the standard checker's soundness with removal of extension
variable tautologies. The exact generated strengthened cube appears in both
checker formulas; the appended leaf units and cover clauses match HsbLeaves.

The four exports prove leaf soundness, cover soundness, assembly of evidence
for the generated leaf inventory, and semantic exclusion using an arbitrary
checked leaf list. The latter remains sound because its checked cover supplies
exhaustiveness. Expected axiom reports contain only standard axioms.

Raw proof data controls the padding bound; the prepared proof must pass the
Lean checker on the padded exact formula. No parser or renumbering correctness
claim is needed for that implication. External `cake_lpr` success alone does
not instantiate these propositions. Concrete arrays and positive Lean checker
theorems still have to be supplied for every required certificate.

The source was prepared in the H3 worktree as an isolated addition for the H7
branch. Existing H7 files and running cloud refs were not changed.

The isolated H7 adapter branch compiled at `ef132f31619` in job
`20261008T052852-erdos85__h7-lrat-adapter-20261008-224002`, exit 0 at
05:32:26 UTC. The target took 4.1 seconds; the 8,802-job dependency build
also passed. `audit.json` records all four standard-only axiom reports,
matching source hashes, independently fetched object hash, and raw log hash.
The full log is retained as `proof-pass.log`. The original H7 worktree and
cache were untouched; the new cache was copied with XFS copy-on-write.

The paper's intended H7 endpoint remains externally CakeML-verified,
check-then-discard evidence tied to Lean formulas by emitter identity, as
clarified by Claude in room message 52703. This adapter is optional
strengthening for selected certificates, not a new requirement to replay
all 377,776 leaves inside Lean. A separate bounded cover pilot measures one
such optional use.
