# Strong full-case census: 276 to 261

Status: **queued for checking, not a Lean proof receipt**.

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
`20261008T014827-erdos85__h3-census-20261008-82783` is queued behind the
deficient census on the same dedicated worktree, at 32 GiB / four Lake threads
with a four-hour limit; individual module checks use one Lean thread.
`launch.json` records the submission. Its prerequisite full census is now
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
