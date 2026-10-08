# Concrete strong H3 census connections — awaiting verification

The four new exports in `Full276.lean` and `Deficient1554.lean` have not yet
compiled. They are prepared source, not verified proof evidence.

`Full276.lean` connects an actual full-branch graph to the existing 276-pair
block-pruned set, retaining `ThreeHighDistinctJointWitness`. It uses the complete
55-entry coverage assembly, the newly verified concrete strong block transport,
and the existing triangle/far-color pruning. Its exclusion theorem explicitly
requires all 276 native pair searches to return false.

`Deficient1554.lean` connects an actual deficient-branch graph to the existing
1,554-pair set using the complete 370-entry coverage assembly and existing
structural pruning. Its exclusion theorem also retains all finite rejections
as hypotheses.

Neither file proves any finite rejection. The later full-branch terminal and
capacity reductions to 261 pairs remain to be connected separately; this
package does not replace that intended final census. The H3 pair-profile branch
and the full paper conclusion remain open.

The cloud job `20261008T005410-erdos85__h3-triple-formal-20261007-50086`
was cancelled before compilation: the census is independent of the pilot
and a local Docker slot became free. `launch.json` retains the initial queue
and cancellation record. `local-launch.json` records the replacement run in
container `lean-build-22830`, at 8 GiB / one worker / one Lean thread, with a
60-minute limit and unchanged sources. Neither launch is a proof receipt.

## Checker

The read-only plan validates all 100 full and 200 deficient shard names against
the respective assembly imports, then checks the dependency order of 107 full
and 203 deficient modules:

```sh
python3 research/problems/erdos-85-wip-01/h3_strong_census_20261008/check.py --plan
```

The checker copies retained sources byte-for-byte, builds their library
dependencies, compiles independent shards with a configurable worker count (one Lean thread
each; the current local run uses one worker), and compiles the assemblies and new wrappers sequentially. Full and
deficient outputs are isolated because both packages use `Assembly` and
`Pruning` as module names. It retains per-module source/log/olean hashes and
requires the exact declared axiom-export list with only standard axioms.
After a failed shard, queued shards are skipped and the branch is not certified.

Compilation must run inside the repository Docker environment, from `proofs/`
under `lake env`. The checker refuses to compile on the host Mac. For the cloud:

```sh
e85-remote run erdos85/h3-triple-formal-20261007 --full --mem 48 --threads 2 --timeout 2h --no-follow -- 'lake env python3 ../research/problems/erdos-85-wip-01/h3_strong_census_20261008/check.py --branch both --workers 2 --output /workspace/research/problems/erdos-85-wip-01/h3_strong_census_20261008/_build/cloud-first'
```

The cloud command is a reproduction option, not the active run. Use a new
output directory. The same-branch worktree lock queues behind other jobs; do not launch an additional branch to bypass that
lock and exceed the agreed allocation. Submission is not proof of a successful
build. Check the actual job outcome and retain its completed evidence before
counting any new export as verified. The branch ref is resolved after the job
acquires the worktree lock; the job log records the actual source commit.
