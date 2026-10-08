# Strong full-case census: 276 to 261

Status: **bounded cloud continuation running, not a final Lean proof receipt**.

The first job reached its four-hour limit and exited 124 at 06:07:02 UTC,
with 309 of 342 modules passing through `Zero32Shard7`. Its container and
compiler processes were confirmed absent before terminal capture. The new
job `20261008T060931-erdos85__h3-census-20261008-248468`, at commit
`6b91e1d41371835eb90e2aa647786be506a86766`, has a one-hour cap and 32-GiB
memory limit. It validated the complete prerequisite, all 309 passing
modules, and 453 library/toolchain source paths, then preserved and
revalidated the old output snapshot. Observed new PASS results include
`Zero32Shard8` and `Zero32Shard9`. `continuation-evidence/` retains the old
terminal log and receipt, host capture, observed continuation receipt,
and launch record. The final audit remains pending.

`Full261.lean` connects the strong actual-graph witness in `Full276.lean`
to `FullCapacityPruning.remainingPairs`, the retained 261-pair census.
The terminal and capacity membership lemmas use `hj.forget`, while the
conclusion retains the original `ThreeHighDistinctJointWitness` at exactly
the same representative pair and cross. The second theorem still requires
native-search rejection for every remaining pair. No rejection is supplied
here; this package does not close the full branch or the H3 stratum.

The source-only plan contains 107 prerequisite modules from the full branch
of `../h3_strong_census_20261008`, followed by 342 additional modules:
339 retained certificate modules, the terminal and capacity reductions,
and the new `Full261` module. The 339 certificate modules comprise 214
fixed-pair rejection modules, 44 fixed-pair coverage modules, 41 U32/R14
coverage modules, and 40 subset-capacity modules. There are 15 data-only
modules; the other modules request 1,077 axiom reports in total. Namespace-local
names in some retained `#print` commands are matched against fully qualified
Lean output, in order. The two new exports are:

- `FullUStrongFinalCensus.actual_distinct_witness`
- `FullUStrongFinalCensus.excluded_of_rejections`

Host checks completed: Python parsing, complete acyclic source/import
inventory, explicit axiom-report inventory, and refusal to compile outside
Docker. No Lean build has completed for this package. Cloud job
`20261008T014827-erdos85__h3-census-20261008-82783` started at 02:06:42 UTC
after the full and deficient census passed. It uses the same dedicated worktree
at 32 GiB / four Lake threads
with a four-hour limit; individual module checks use one Lean thread.
`launch.json` records the submission and actual execution commit. Its prerequisite full census is now
verified in `../h3_strong_census_20261008/evidence-full/`. The pilot is unchanged.

After the full census prerequisite has a PASS receipt, run from `proofs/`
inside the repository Docker environment:

```sh
lake env python3 ../research/problems/erdos-85-wip-01/h3_strong_final_census_20261008/check.py \
  --base-build /workspace/research/problems/erdos-85-wip-01/h3_strong_census_20261008/_build/cloud-dedicated-first/full \
  --output /workspace/research/problems/erdos-85-wip-01/h3_strong_final_census_20261008/_build/cloud-first
```

The checker validates every prerequisite source, object, compiler log, axiom
export, and receipt entry before reuse. It then builds missing library
dependencies and compiles the 342 modules in dependency order, with one Lean
thread per compiler process. Output must be a new directory. Every module
retains its source copy, object, complete log, and JSON record. `RUN.json`
records progress and the terminal result; there is no automatic retry or
resume. A `PASS` for this package will still leave the finite rejection
hypotheses open.

Use `python3 check.py --plan` for a read-only inventory without Lean.

`audit.py` independently checks a completed build's retained evidence without
running Lean or changing build files. It requires the original source copies,
objects, logs, individual receipts, and `RUN.json` for both builds. It checks
the complete source inventory, dependency commands and hashes, compiler
commands, object hashes, and axiom reports parsed directly from compiler logs.
It rejects incomplete receipts, changed artifacts, and nonstandard axioms.
The final build must also record the exact prerequisite receipt hash.

Run on the cloud host with this script available (the running build branch
does not need to be advanced):

```sh
python3 audit.py --repository /opt/e85/wt/erdos85__h3-census-20261008 \
  --base-build /opt/e85/wt/erdos85__h3-census-20261008/research/problems/erdos-85-wip-01/h3_strong_census_20261008/_build/cloud-dedicated-first/full \
  --output /opt/e85/wt/erdos85__h3-census-20261008/research/problems/erdos-85-wip-01/h3_strong_final_census_20261008/_build/cloud-first
```

The recorded container repository defaults to `/workspace`; override
`--recorded-repository` only for a build that used a different mount path.
Validation of the audit: a valid synthetic receipt was accepted and seven
variants were rejected (running status, missing module, changed source,
changed object, changed log, mismatched individual receipt, and nonstandard
axioms). The audit also passed against the real full-census prerequisite:
107 modules and 228 axiom reports, receipt SHA-256
`9924e45dfa932bae6af3607eb7de97e4b77d590366bf8d4bb9eaaf8de480236f`.
The final 342-module audit remains pending completion of its cloud build.

## Continuation after a terminal timeout or failure

`resume.py` preserves verified prefix work if the original bounded job stops
before completion. Its first use is recorded above. It never stops or submits
a cloud job itself.

First, on the cloud host, its `--capture-terminal JOB` mode requires the
authoritative job exit file to contain a nonzero exit and the old process ID
to be absent. It parses the actual command in the job log and binds the
requested output directory to that command, execution commit, log hash,
exit hash, and current receipt hash. The terminal record must be a new file.
Missing exit evidence or an observation timeout cannot authorize a continuation.
The host also compares the transitive library and Lean/Lake configuration
against the original execution commit, then records every source hash
(including absence of alternative configuration files). The container checks
that exact inventory without invoking Git: inspection of the running census
container confirmed that its worktree's external Git directory is not mounted.

Only after capture, an explicitly submitted continuation may run the helper
inside cloud Docker, from `proofs/`, with `--terminal-record`, `--base-build`,
`--output` (the original container path), and `--snapshot` (a new separate
directory). The dedicated census ref must remain unchanged while a job is
live. No continuation is submitted by this preparation artifact.

Before changing output, the helper checks the full prerequisite census and
every passing module in the exact dependency prefix. It checks original and
copied sources, object/log hashes, commands, individual receipts, requested
axiom reports, and standard-only axiom sets. It also refuses changes to the
transitive library sources or Lean/Lake settings, including `lakefile.toml`.
The entire old output is copied to the fresh snapshot and revalidated before
the active receipt changes. A last failed module is retained in the snapshot
and recompiled; it is never reused as a success. Remaining modules compile
at the same original paths with one Lean thread, and a complete audit follows.

`python3 test_resume.py` runs 17 small metadata-only regression tests. These
accept a valid prefix and copied snapshot and reject changed sources, objects,
logs, receipts, dependency evidence, report inventories, report names, axiom
sets, result order, and nonzero successful exits. They also check refusal of
live or successful jobs, missing terminal records, wrong output paths, and
changed transitive library or Lake settings. The container-side checks also
pass with Git deliberately unavailable and reject a missing captured inventory
or newly introduced Lake configuration. They invoke neither Lean nor
finite search. A read-only check against the original execution commit
`3e67a0afc3b9b99a478f5c37cc7c2ac29a8bcfb7` found all 453 transitive library
and toolchain input paths unchanged at preparation time.
