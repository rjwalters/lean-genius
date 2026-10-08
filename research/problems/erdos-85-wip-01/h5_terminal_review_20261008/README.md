# H5 terminal acceptance preparation

Status: collector prepared and metadata tests pass. The exact H5 build job
`20261008T112746-erdos85__h5-formal-20261008-455708` was independently confirmed
live while preparing this package. No part or whole-stratum acceptance is
recorded here yet.

Execution pin: `99bc3e3413008ca13d5efb29bee5e855af961976`.
The source inventory was previously checked in `../h5_stratum_review_20261008`:
40 native part modules, three representative assemblies and one stratum
assembly. This collector reads the existing builder; it does not run Lean,
start or cancel a job, advance the H5 branch, or edit the peer's files.

## Terminal checks

`capture.py` invokes `audit_cloud.py` with the pinned inventory and the prior
independent Engine/Bridge/Fast audits. A live job returns its exact PID and
current presence without writing acceptance evidence. A terminal job must
have a successful authoritative exit, the correct execution commit and job
specification, completion banners and no compiler error or sorry warning.

Every one of the 44 source modules must match both its reviewed hash and the
execution commit. Every module needs a fresh build record and a nonempty
object created inside that job's interval. Object hashes are read twice to
reject changes during collection. The four previously audited dependencies
must retain their source and object hashes. Source snapshots, object
metadata, raw job log/specification/exit, collector source and input audit
records are retained locally; binary objects remain on the builder.

`validate_axioms.py` binds each printed theorem to its actual source module.
Each representative must have exactly the three standard logical axioms and
its own 16, 16 or 8 search-part axioms. Each graph-side cell must include the
corresponding search axioms; the final stratum must include all 40. Missing,
duplicate, wrong-cell and sorry axioms fail acceptance.

## Separate graph-cover review

The existing graph cover contains native proofs beyond the new 40-part
search. `graph-axioms.json` pins the three graph-cover sources and points to
seven enclosing theorem names containing eight tactic sites. These are
source-review pointers, not an allowed prefix list: case splits may emit
more than one generated native axiom per source site.

The sites prove finite representative-mask fiber counts, representative
array lengths of 49, and the local triple-support count used
by the two-triple representative. The generic graph-cover theorem refers
to all three cover branches, so one must not assume that a cell export's
additional axiom set contains only that cell's fiber computations.

The exact extra axiom names must be reviewed from the final printed reports
and linked to these proofs and any transitive dependency. Until that review
is recorded as `EXACT_GRAPH_AXIOMS_REVIEWED`, the strongest possible result
is `NEEDS_GRAPH_AXIOM_REVIEW`, even if all build and object checks pass.
An unreviewed extra can never pass through a wildcard or namespace allowance.
A later review must list exact extras separately for each of the four
exports, then rerun collection into a new evidence directory. Retain the
initial collection unchanged.

## Run

```sh
python3 -B capture.py
python3 -B capture.py --output terminal-evidence2
```

The default output is `terminal-evidence1`; differing existing evidence is
never overwritten. After a terminal capture, explicitly force-add ignored
raw `*.log` files when banking the evidence. `REJECTED` and
`NEEDS_GRAPH_AXIOM_REVIEW` grant no whole-stratum credit.

Validation performed: 23 metadata-only tests. Twelve cover exact axiom sets,
missing or duplicate reports, incorrect cells, unreviewed graph axioms and
`sorryAx`; eleven cover terminal acceptance, missing/stale/future/changed
objects, source drift, missing fresh build records, failed jobs, wrong
execution pins, and live/graph-review pending states. Synthetic tests grant
no mathematical credit and run no finite search.
