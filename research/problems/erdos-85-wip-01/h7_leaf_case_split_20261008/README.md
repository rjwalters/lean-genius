# Positive-unit leaf and negative-cover interface

Status: **first cloud build failed on simplification; fixed source awaiting recheck**.

`Proofs.Erdos85CnfPositiveCaseSplit` defines a positive-unit CNF for each
list of variables and the negative blocking clause for each list. It proposes
a generic Boolean partition theorem and a conditional UNSAT theorem from
all case certificates plus a cover certificate, without a separate `hsplit`
hypothesis. Repeated variables, duplicate cases, and empty lists are allowed.

For H7, each list is the edge-variable list of one generator leaf. The
negative cover matches the shape of `SevenHighT0Hsb.coverClauses`, while
each case asserts the leaf edges by unit clauses. This module does not yet
supply the exact H7 representation equality, any UNSAT certificate, or any
semantic graph exclusion. The cover and every listed leaf must still be
proved UNSAT after appending the same base formula (cube plus sound hsb).

The module imports only `Std.Sat.CNF.Basic`; it can be cloud-checked on the
free H3 pilot worktree without touching Claude's live H7 worktree or the
running H3 deficient pilot/census. No finite rejection search is performed.

Claude independently added the more general signed-literal theorem
`cnf_unsat_of_blocking_clauses` in `...CanonicalHsbLeaves` at `e812684bde7`.
That is the H7 integration path. This positive-only module is a standalone
cross-check and requires no changes to Claude's proof files. The first build
failed because composition expressions were not unfolded by the core simp
set; `Function.comp_def` is now supplied explicitly. The failed build and
its follower output are retained in `first-build.json` / `first-build.log`.
