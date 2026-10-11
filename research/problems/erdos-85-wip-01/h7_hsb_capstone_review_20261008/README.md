# Independent H7 leaf and capstone audit

Status: **PASS for the conditional proof chain; structural certificates remain open**.

Both cloud builds at `512a3f4a683` exited 0. The executed source bytes for
HsbLeaves, HsbCapstone, and HsbStratumCapstone match independently fetched
cloud source hashes and the subsequent H7 branch revision. Their cloud
object hashes and complete raw build logs are retained in `audit.json`.
All eight printed exports were checked. The stratum wrappers have exactly
the same 94 axioms as the previously independently audited MixedCapstone:
the standard three plus 91 existing native-decision axioms. Hsb introduces
no additional axiom. No `sorryAx` occurs in the reviewed exports.

The signed blocking-clause theorem handles arbitrary lists of clauses,
including empty or duplicate clauses. Every leaf and the checked cover
append to the same strengthened cube. The cover supplies exhaustiveness;
the proof does not assume an unchecked partition. The capstone still
quantifies over all 28 structural cubes.

The all-cube identity receipt has 28 distinct roots, matching Lean/Python
hsb and cover hashes, matching masks, and every emitted witness checked.
Its totals are 2,066,981 hsb clauses and 377,776 leaves. The cloud job exit
was independently read as 0. This review checks that receipt's consistency;
it does not rerun the finite generator locally.

The remaining certificate campaign and certificate/byte-identity bridge
into `SevenHighT0CanonicalHsbEvidence` are not discharged by these builds.
The resulting H7 exclusion remains conditional.
