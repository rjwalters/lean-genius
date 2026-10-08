# H7 hsb LRAT adapter

Status: **source prepared; requires the H7 branch and a cloud build**.

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
