# Conditional order-49 capstone review

Independent acceptance: `CONDITIONAL_CAPSTONE_ARTIFACT_AUDIT_PASS` in
`evidence2/AUDIT.json`, for job
`20261008T135640-erdos85__order49-capstone-20261008-546872` at
`c955257fbd9a4b4aab5e96c90e26cdedb0f74a5c`, authoritative exit 0.
All 500 repository source/object pairs, 83 previously audited objects,
29 freshly built modules and all four exact axiom reports were checked.
The capstone itself compiled in 9.7 seconds. No `sorry` was reported.

The new module correctly leaves the H1 capacity-inventory UNSAT evidence,
H7 structural cover/leaf evidence and H3 triple cell (or whole stratum) as
explicit hypotheses. It uses the accepted H5 stratum and H3 pair cell. Its
finite-drop wrappers apply the same conditional upper bound to the existing
checked finite witnesses. No unconditional finite drop is claimed.

`prepare.py` binds all 500 repository modules in the source import closure,
including 83 previously independently audited objects from H5, the H3 pair
cell and the conditional H7 chain. Their source hashes agree at the capstone
pin. The separately inspected 168 shared H3 dependencies also agree with
the prepared H3 stratum bundle. These are source checks, not a new build.

`capture.py` reads the exact existing job without compiling, starting,
restarting or stopping any computation. Pending jobs report their exact PID
and current presence. A successful terminal collection checks all 500
source/object pairs, the 83 prior object hashes, the fresh capstone build,
fresh-build object times, all four printed axiom reports, unchanged artifacts
on a second read, and the authoritative successful job exit. Its initial
status can only be `NEEDS_EXACT_AXIOM_REVIEW`. Exact per-export lists must be
reviewed and supplied in `axioms.json` before a new collection can return
`CONDITIONAL_CAPSTONE_ARTIFACT_AUDIT_PASS`. Inherited axiom sets are minimum
checks, not permission for unknown extras.

The original job specification says 16 CPUs, six Lean workers and 48 GiB.
After the reviewer flagged the mismatch with the intended CPU limit, Claude
updated his live container `lean-build-546968` to 8 CPUs at 13:59 UTC. Codex
independently observed the actual 8-CPU/48-GiB limits at 14:00:06 UTC. The
collector preserves the original specification rather than rewriting it.
The original H3 sweep and its volume were untouched. The capstone log replays
H5 assemblies and the H3 pair cell from the copied cache.

The source closure exceeds the remote shell's single-argument limit when
embedded without compression. The collector compresses its read-only code
and metadata for transport, checks the compression round trip locally, and
decompresses it on the existing builder. The initial oversized transport
failed before the auditor ran; the corrected collector returned the existing
job as live. No job was relaunched.

Raw evidence is immutable; use a new output directory for recollection and
force-add ignored raw logs when banking. No actual Lean or finite search
runs locally.

## Exact trust-set review

| Export suffix | Axiom count | Scope |
| --- | ---: | --- |
| `not_c4FreeMinDegreeWitness_fortyNine_seven_of_externalEvidence_threeStratum` | 193 | H1/H7 evidence and the whole H3 stratum are hypotheses |
| `not_c4FreeMinDegreeWitness_fortyNine_seven_of_externalEvidence` | 217 | Adds the accepted 24-part H3 pair cell; triple cell remains a hypothesis |
| `minDegreeForC4_fortyEight_fortyNine_exact_of_externalEvidence` | 223 | Adds three native checks for each of the order-48 and order-49 witnesses |
| `minDegreeForC4_fortyNine_lt_fortyEight_of_externalEvidence` | 220 | Adds only the three order-48 witness checks |

Every export is in namespace `Erdos85`. Counts include the three standard
axioms; these proofs also rely on the explicitly listed native axioms.
They are not kernel-only.

Beyond the previously reviewed H5/H7 and, where used, H3-pair sets, all
four exports include exactly 23 H1 finite cover/normalization axioms and
18 H9 LRAT representative checks (T2: 2, T3: 5, T4: 11). The witness
wrappers account for the remaining six distinct extras. `axioms.json`
enumerates every exact set and maps all 47 distinct extras to 44 reviewed
source declarations in 29 pinned source files. Four native cases occur
inside `oneHighStandardMate_even_pair`; no other extra suffix is admitted.
The H1 cover axioms do not supply the outstanding CNF UNSAT evidence.

`evidence1` preserves the initial artifact audit with status
`NEEDS_EXACT_AXIOM_REVIEW` (11 retained files). `evidence2` preserves the
independent successful recollection after exact review (40 retained files),
including the 29 reviewed source snapshots. Both keep the original raw log
and job specification. The review is bound to the source specification,
execution commit, job and initial audit hash; recollection rejects changed
objects, sources or printed trust sets. This acceptance establishes the
conditional capstone only; `unconditional_drop_verified` remains false.
